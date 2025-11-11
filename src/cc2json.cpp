#include <boost/filesystem.hpp>
#include <boost/flyweight.hpp>
#include <iostream>
#include <fstream>
#include <string>
#include <unordered_set>
#include <vector>
#include <sys/resource.h>

#include "FactGenerator/include/ContextSensitivity.hpp"
#include "FactGenerator/src/ContextSensitivity.cpp"
#include "FactGenerator/include/FactGenerator.hpp"
#include "FactGenerator/src/FactGenerator.cpp"
#include "FactGenerator/include/FactWriter.hpp"
#include "FactGenerator/src/FactWriter.cpp"
#include "FactGenerator/src/Globals.cpp"
#include "FactGenerator/src/Signatures.cpp"
#include "FactGenerator/src/PredicateGroups.cpp"
#include "FactGenerator/src/InstructionVisitor.cpp"
#include "FactGenerator/include/RefmodeEngine.hpp"
#include "FactGenerator/src/RefmodeEngine.cpp"
#include "FactGenerator/src/Constants.cpp"
#include "FactGenerator/src/Variables.cpp"
#include "FactGenerator/src/Assembly.cpp"
#include "FactGenerator/src/Functions.cpp"
#include "FactGenerator/src/LlvmEnums.cpp"
#include "FactGenerator/src/TypeVisitor.cpp"
#include "FactGenerator/include/TypeAccumulator.hpp"

// start modified copy of FactGenerator/src/Types.cpp
using cclyzer::FactGenerator;
namespace pred = cclyzer::predicates;

void FactGenerator::writeTypes(const llvm::DataLayout& layout) {
  using llvm_utils::TypeAccumulator;

  // Add basic primitive types
  writeFact(pred::primitive_type::id, "void");
  writeFact(pred::primitive_type::id, "label");
  writeFact(pred::primitive_type::id, "metadata");
  writeFact(pred::primitive_type::id, "x86mmx");

  // Find types contained in the types encountered so far, but not
  // referenced directly

  TypeAccumulator type_accum;
  for (const auto* type : types) {
    type_accum.visitType(type);
  }

  // Create type visitor
  TypeVisitor tv(*this, layout);

  // Record each type encountered
  for (const auto* ty : type_accum) {
    tv.visitType(ty);
  }
}

// end
// start modified copy of RefmodeEngineImpl.cpp
//#include "FactGenerator/src/RefmodeEngineImpl.hpp"

#include <llvm/IR/Metadata.h>
#include <llvm/Support/raw_ostream.h>

#include <boost/algorithm/string.hpp>
#include <boost/flyweight.hpp>
#include <map>

using cclyzer::refmode_t;
using cclyzer::RefmodeEngine;
using std::string;

using boost::algorithm::trim;

// Refmode for LLVM Values

auto RefmodeEngine::Impl::refmodeOf(const llvm::Value *Val) -> refmode_t {
  string rv;
  llvm::raw_string_ostream rso(rv);

  if (Val->hasName()) {
    rso << (llvm::isa<llvm::GlobalValue>(Val) ? '@' : '%') << Val->getName();
    goto print;
  }

  if (llvm::isa<llvm::Constant>(Val)) {
    Val->printAsOperand(rso, /* PrintType */ false);
    goto print;
  }

  if (Val->getType()->isVoidTy()) {
    Val->printAsOperand(rso, /* PrintType */ false);
    goto print;
  }

  if (Val->getType()->isMetadataTy()) {
    const auto *mv = llvm::cast<llvm::MetadataAsValue>(Val);
    const llvm::Metadata *meta = mv->getMetadata();

    appendMetadataId(rso, *meta);
    goto print;
  }

  // Handle unnamed variables
  for (auto it = ctx->rbegin(); it != ctx->rend(); ++it) {
    ContextManager::context &ctxt = *it;

    if (ctxt.isFunction) {
      if (ctxt.numbering.empty()) {
        computeNumbering(
            llvm::cast<llvm::Function>(ctxt.anchor), ctxt.numbering);
      }

      rso << '%' << ctxt.numbering[Val];
      goto print;
    }
  }

  // Expensive
  Val->printAsOperand(rso, false, &ctx->module());

print:
  // Trim external whitespace
  string ref = rso.str();
  trim(ref);

  return ref;
}

void RefmodeEngine::Impl::appendMetadataId(
    llvm::raw_string_ostream &rso, const llvm::Metadata &meta) {
  if (llvm::isa<llvm::MDNode>(meta)) {
    meta.printAsOperand(rso, *slotTracker);
  } else if (llvm::isa<llvm::MDString>(meta)) {
    meta.printAsOperand(rso, *slotTracker);
  } else {
    const auto &v = llvm::cast<llvm::ValueAsMetadata>(meta);
    const llvm::Value *inner_value = v.getValue();
    const llvm::Type *type = v.getType();

    if (llvm::isa<llvm::ConstantAsMetadata>(meta)) {
      meta.printAsOperand(rso, *slotTracker);
    } else {
      // For unknown reasons the printAsOperand() method is
      // super expensive for this particular metadata type,
      // at least for LLVM version 3.7.{0,1}. So instead, we
      // manually construct the refmodes ourselves.

      rso << refmode<llvm::Type>(*type) << " " << refmodeOf(inner_value);
    }
  }
}

void RefmodeEngine::Impl::computeNumbering(
    const llvm::Function *func,
    std::map<const llvm::Value *, unsigned> &numbering) {
  unsigned counter = 0;

  // Arguments get the first numbers.
  for (const auto &arg : func->args()) {
    if (!arg.hasName()) {
      numbering[&arg] = counter++;
    }
  }

  // Walk the basic blocks in order.
  for (const auto &bb : *func) {
    if (!bb.hasName()) {
      numbering[&bb] = counter++;
    }

    // Walk the instructions in order.
    for (const auto &instr : bb) {
      // void instructions don't get numbers.
      if (!instr.hasName() && !instr.getType()->isVoidTy()) {
        numbering[&instr] = counter++;
      }
    }
  }

  assert(!numbering.empty() && "asked for numbering but numbering was no-op");
}
// end modified copy of RefmodeEngineImpl.cpp

#include "PAInterface.h"
#include "PAInterface.cpp"
#include "PointerAnalysis.h"
#include "PointerAnalysis.cpp"
#include "Wrapper.hpp"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/SourceMgr.h"

namespace fs = boost::filesystem;

static llvm::cl::OptionCategory CJCat("cc2json options");
static llvm::cl::opt<std::string>
    InputFilename(
        llvm::cl::Positional, llvm::cl::desc("<input file>"), llvm::cl::Required,
        llvm::cl::cat(CJCat));

static llvm::cl::opt<std::string>
    JsonOutFilename(
        "json-out",
        llvm::cl::desc("Output file for JSON results"),
        llvm::cl::value_desc("filename"),
        llvm::cl::cat(CJCat));

auto factgen_module(
    llvm::Module &module,
    const fs::path &output_dir,
    const std::optional<boost::filesystem::path> &signatures,
    ContextSensitivity sensitivity,
    Entrypoints entrypoints)
    -> std::tuple<
        fs::path,
        std::map<boost::flyweight<std::string>, const llvm::Value *>> {
  using cclyzer::FactGenerator;
  using cclyzer::FactWriter;
  using cclyzer::predicates::predicates_reg;

  std::cerr << "Writing facts to: " << output_dir << "...\n";

  // initialize factgen and output writer
  FactWriter writer(predicates_reg, output_dir, "\t");
  FactGenerator &gen = FactGenerator::getInstance(writer);
  const std::string &real_path = module.getSourceFileName();

  // do the fact generation
  auto res_maps = gen.processModule(module, real_path, signatures, sensitivity, entrypoints);

  const llvm::DataLayout &layout = module.getDataLayout();
  gen.writeTypes(layout);

  return std::make_tuple(output_dir, std::move(res_maps));
}

static auto da_str(Analysis which) -> std::string {
  switch (which) {
    case Analysis::DEBUG:
      return ("debug");
    case Analysis::SUBSET:
      return ("subset");
    case Analysis::UNIFICATION:
      return ("unification");
  }
  assert(false && "unreachable");
}

// Helper function to convert llvm::Value* to string, printing only function names for functions
std::string llvm_value_to_string(const llvm::Value* val, bool show_func_sig = false) {
    if (!val) {
        return "nullptr";
    }

    // Check if this is a function
    if (const auto* func = llvm::dyn_cast<llvm::Function>(val)) {
        if (!show_func_sig) { return std::string(func->getName()); }

        std::string str;
        llvm::raw_string_ostream os(str);
        os << *(func->getReturnType()) << " @" << func->getName() << "(";
        bool first = true;
        for (const auto& arg : func->args()) {
            if (!first) os << ", ";
            os << *(arg.getType());
            first = false;
        }
        os << ")";
        return os.str();
    }

    // For non-functions, use the regular printing
    std::string str;
    llvm::raw_string_ostream os(str);
    val->print(os);
    return os.str();
}

// Helper function to escape JSON strings
static std::string json_escape(const std::string& s) {
    std::string result;
    result.reserve(s.length());
    for (char c : s) {
        switch (c) {
            case '"':  result += "\\\""; break;
            case '\\': result += "\\\\"; break;
            case '\b': result += "\\b"; break;
            case '\f': result += "\\f"; break;
            case '\n': result += "\\n"; break;
            case '\r': result += "\\r"; break;
            case '\t': result += "\\t"; break;
            default:
                if ('\x00' <= c && c <= '\x1f') {
                    char buf[7];
                    snprintf(buf, sizeof(buf), "\\u%04x", static_cast<unsigned char>(c));
                    result += buf;
                } else {
                    result += c;
                }
        }
    }
    return result;
}

struct UniqueFilenameMapper {
    // Maps from short filename to the (directory, filename) pair that claimed it
    std::map<std::string, std::pair<std::string, std::string>> shortToFull;

    // Maps from (directory, filename) to its assigned short filename
    std::map<std::pair<std::string, std::string>, std::string> fullToShort;

    std::string getShortFilename(const std::string& directory, const std::string& filename) {
        auto key = std::make_pair(directory, filename);

        // Check if we've already assigned a short name for this pair
        auto it = fullToShort.find(key);
        if (it != fullToShort.end()) {
            return it->second;
        }

        // Try the original filename first
        std::string candidate = filename;
        int suffix = 1;

        while (true) {
            auto sit = shortToFull.find(candidate);
            if (sit == shortToFull.end()) {
                // This short name is available
                shortToFull[candidate] = key;
                fullToShort[key] = candidate;
                return candidate;
            }

            // Check if the existing mapping is for the same (directory, filename)
            if (sit->second == key) {
                return candidate;
            }

            // Generate next candidate with suffix
            candidate = filename + "!" + std::to_string(suffix);
            suffix++;
        }
    }
};

std::string llvm_call_site_to_string(const llvm::Value* val, UniqueFilenameMapper &ufm) {
    if (!val) {
        return "nullptr";
    }
    if (const llvm::Instruction *I = dyn_cast<llvm::Instruction>(val)) {
        if (const llvm::DebugLoc Loc = I->getDebugLoc()) {
            unsigned Line = Loc.getLine();
            unsigned Column = Loc.getCol();
            llvm::DILocalScope *Scope = Loc.get()->getScope();
            //llvm::StringRef Filename = Loc.getFilename();

            std::string uf = ufm.getShortFilename(Scope->getDirectory().str(),
                                                  Scope->getFilename().str());

            std::string str;
            llvm::raw_string_ostream os(str);
            os << "{ " << "\"line\": " << Line
                       << ", \"col\": " << Column
                       << ", \"p\": \"" << I->getFunction()->getName() << "\""
                       << ", \"uf\": \"" << json_escape(uf) << "\" }";
            return os.str();
        }
    }
    return std::string("\"") + llvm_value_to_string(val) + std::string("\"");
}

// Process a string to strip "*global_alloc@" prefix and filter entries starting with "."
static std::optional<std::string> process_global_name(const std::string& name) {
    std::string processed = name;

    // Strip "*global_alloc@" prefix if present
    const std::string prefix = "*global_alloc@";
    if (processed.substr(0, prefix.length()) == prefix) {
        processed = processed.substr(prefix.length());
    }

    // Filter out entries starting with "."
    if (!processed.empty() && processed[0] == '.') {
        return std::nullopt;
    }

    return processed;
}

// Check if an alias entry is trivial (X,X) or (X[0], X)
static bool is_trivial_alias(const std::string& alloc1, const std::string& alloc2) {
    if (alloc1 == alloc2) {
        return true;
    }

    // Check if alloc1 is alloc2[0] or alloc2 is alloc1[0]
    if (alloc1.length() > 3 && alloc1.substr(alloc1.length() - 3) == "[0]") {
        std::string base1 = alloc1.substr(0, alloc1.length() - 3);
        if (base1 == alloc2) {
            return true;
        }
    }

    if (alloc2.length() > 3 && alloc2.substr(alloc2.length() - 3) == "[0]") {
        std::string base2 = alloc2.substr(0, alloc2.length() - 3);
        if (base2 == alloc1) {
            return true;
        }
    }

    return false;
}


int main(int argc, char *argv[]) {
    const llvm::cl::OptionCategory*  relevant_cats[] = { &CJCat, &cclyzer::cccat };
    llvm::cl::HideUnrelatedOptions(relevant_cats);
    llvm::cl::ParseCommandLineOptions(argc, argv, "cclyzer++ standalone analysis\n");

    // Set file descriptor limit to 1024 to ensure Souffle can open enough files
    struct rlimit rl;
    rl.rlim_cur = 1024;
    rl.rlim_max = 1024;
    if (setrlimit(RLIMIT_NOFILE, &rl) != 0) {
        std::cerr << "Warning: Failed to increase file descriptor limit\n";
    }

    // 1. Load LLVM module
    llvm::LLVMContext context;
    llvm::SMDiagnostic err;
    std::unique_ptr<llvm::Module> module = llvm::parseIRFile(InputFilename, err, context);

    if (!module) {
        err.print(argv[0], llvm::errs());
        return 1;
    }

    // 2. Run fact generation and pointer analysis
    const fs::path output_dir = fs::path(cclyzer::datalog_debug_dir_option);
    if (!fs::exists(output_dir)) {
        fs::create_directories(output_dir);
    }

    std::optional<fs::path> signatures_path;
    if (cclyzer::signatures != "") {
        signatures_path = std::optional<fs::path>(fs::path(cclyzer::signatures));
    } else {
        signatures_path = std::optional<fs::path>();
    }

    auto [dir, llvm_val_map] =
        factgen_module(*module, output_dir, signatures_path,
            cclyzer::context_sensitivity, cclyzer::entrypoints);
    const auto pa = cclyzer::get_interface(cclyzer::datalog_analysis);
    PAFlags flags = PAFlags::NONE;
    if (cclyzer::datalog_debug_option) {
        flags = flags | PAFlags::WRITE_ALL;
    }

    pa->runPointerAnalysis(dir, flags);
    if (cclyzer::datalog_check_assertions_option) {
        pa->checkAssertions(cclyzer::datalog_analysis == Analysis::DEBUG);
    }

    std::map<int, boost::flyweight<std::string>> context_to_string;
    const auto context_to_string_vec =
        pa->relationToVector<int, boost::flyweight<std::string>>(
            "context_to_string", llvm_val_map);
    for (const auto &[fst, snd] : context_to_string_vec) {
        context_to_string.emplace(fst, snd);
    }

    std::multimap<const llvm::Value *, std::tuple<int, int, const llvm::Value *>>
        call_graph;
    const auto callgraph_vec =
        pa->relationToVector<int, const llvm::Value *, int, const llvm::Value *>(
            cclyzer::reachable_callgraph_edge(cclyzer::datalog_analysis), llvm_val_map);
    for (const auto &[callee_ctx, callee, caller_ctx, caller] : callgraph_vec) {
        std::tuple<int, int, const llvm::Value *> entry(
            caller_ctx, callee_ctx, callee);
        call_graph.emplace(caller, entry);
    }

    std::set<const llvm::Value *> null_ptr_set;
    auto var_points_to_rel = pa->relationToVector<
        int,
        boost::flyweight<std::string>,
        int,
        const llvm::Value *>(cclyzer::var_points_to(cclyzer::datalog_analysis), llvm_val_map);
    for (const auto &[_alloc_ctx, alias_set_identifier, _pointer_ctx, value] :
        var_points_to_rel) {
        if (alias_set_identifier == "*null*") {
        null_ptr_set.emplace(value);
        }
    }

    cclyzer::PointerAnalysisAAResult result(
        std::move(context_to_string),
        std::move(var_points_to_rel),
        pa->relationToVector<
            int,
            boost::flyweight<std::string>,
            boost::flyweight<std::string>>(
            cclyzer::alloc_may_alias(cclyzer::datalog_analysis), llvm_val_map),
        pa->relationToVector<
            int,
            boost::flyweight<std::string>,
            boost::flyweight<std::string>>(
            cclyzer::alloc_must_alias(cclyzer::datalog_analysis), llvm_val_map),
        pa->relationToVector<
            int,
            boost::flyweight<std::string>,
            boost::flyweight<std::string>>(
            cclyzer::alloc_subregion(cclyzer::datalog_analysis), llvm_val_map),
        pa->relationToVector<
            int,
            boost::flyweight<std::string>,
            boost::flyweight<std::string>>(
            cclyzer::alloc_contains(cclyzer::datalog_analysis), llvm_val_map),
        pa->relationToVector<
            int,
            boost::flyweight<std::string>,
            int,
            boost::flyweight<std::string>>(
            cclyzer::ptr_points_to(cclyzer::datalog_analysis), llvm_val_map),
        pa->relationToVector<
            int,
            boost::flyweight<std::string>,
            int,
            const llvm::Value *>(
            cclyzer::operand_points_to(cclyzer::datalog_analysis), llvm_val_map),
        pa->relationToVector<const llvm::Value *, boost::flyweight<std::string>>(
            "global_allocation_by_variable", llvm_val_map),
        pa->relationToVector<int, boost::flyweight<std::string>, int>(
            cclyzer::allocation_size(cclyzer::datalog_analysis), llvm_val_map),
        pa->relationToVector<
            int,
            const llvm::Value *,
            int,
            boost::flyweight<std::string>>(
            cclyzer::allocation_by_instr(cclyzer::datalog_analysis), llvm_val_map),
        std::move(null_ptr_set),
        std::move(call_graph));

    if (!cclyzer::datalog_debug_option) {
        boost::filesystem::remove_all(dir);
    }

    // 3a. Print relation contents
    std::cout << "\n--- Relation: context_to_string ---\n";
    for (const auto& entry : result.getContextToString()) {
        std::cout << "  " << entry.first << ", " << entry.second << "\n";
    }

    std::cout << "\n--- Relation: variable_points_to ---\n";
    for (const auto& entry : result.getVariablePointsTo()) {
        std::cout << "  " << std::get<0>(entry) << ", "
                  << std::get<1>(entry) << ", "
                  << std::get<2>(entry) << ", "
                  << llvm_value_to_string(std::get<3>(entry)) << "\n";
    }

    std::cout << "\n--- Relation: pointer_points_to ---\n";
    for (const auto& entry : result.getPointerPointsTo()) {
        std::cout << "  " << std::get<0>(entry) << ", "
                  << std::get<1>(entry) << ", "
                  << std::get<2>(entry) << ", "
                  << std::get<3>(entry) << "\n";
    }

    std::cout << "\n--- Relation: alloc_may_alias ---\n";
    size_t may_alias_elided = 0;
    for (const auto& entry : result.getAllocMayAlias()) {
        std::string alloc1 = std::get<1>(entry).get();
        std::string alloc2 = std::get<2>(entry).get();
        if (!is_trivial_alias(alloc1, alloc2)) {
            std::cout << "  " << std::get<0>(entry) << ", "
                      << std::get<1>(entry) << ", "
                      << std::get<2>(entry) << "\n";
        } else {
            may_alias_elided++;
        }
    }
    std::cout << "  (" << may_alias_elided << " trivial entries elided)\n";

    std::cout << "\n--- Relation: alloc_must_alias ---\n";
    size_t must_alias_elided = 0;
    for (const auto& entry : result.getAllocMustAlias()) {
        std::string alloc1 = std::get<1>(entry).get();
        std::string alloc2 = std::get<2>(entry).get();
        if (!is_trivial_alias(alloc1, alloc2)) {
            std::cout << "  " << std::get<0>(entry) << ", "
                      << std::get<1>(entry) << ", "
                      << std::get<2>(entry) << "\n";
        } else {
            must_alias_elided++;
        }
    }
    std::cout << "  (" << must_alias_elided << " trivial entries elided)\n";

    std::cout << "\n--- Relation: alloc_subregion ---\n";
    for (const auto& entry : result.getAllocSubregion()) {
        std::cout << "  " << std::get<0>(entry) << ", "
                  << std::get<1>(entry) << ", "
                  << std::get<2>(entry) << "\n";
    }

    std::cout << "\n--- Relation: alloc_contains ---\n";
    for (const auto& entry : result.getAllocContains()) {
        std::cout << "  " << std::get<0>(entry) << ", "
                  << std::get<1>(entry) << ", "
                  << std::get<2>(entry) << "\n";
    }

    std::cout << "\n--- Relation: operand_points_to ---\n";
    for (const auto& entry : result.getOperandPointsTo()) {
        std::cout << "  " << std::get<0>(entry) << ", "
                  << std::get<1>(entry) << ", "
                  << std::get<2>(entry) << ", "
                  << llvm_value_to_string(std::get<3>(entry)) << "\n";
    }

    std::cout << "\n--- Relation: global_allocations ---\n";
    for (const auto& entry : result.getGlobalAllocations()) {
        std::cout << "  " << llvm_value_to_string(std::get<0>(entry)) << ", "
                  << std::get<1>(entry) << "\n";
    }

    std::cout << "\n--- Relation: allocation_sizes ---\n";
    for (const auto& entry : result.getAllocationSizes()) {
        std::cout << "  " << std::get<0>(entry) << ", "
                  << std::get<1>(entry) << ", "
                  << std::get<2>(entry) << "\n";
    }

    std::cout << "\n--- Relation: allocation_sites ---\n";
    for (const auto& entry : result.getAllocationSites()) {
        std::cout << "  " << std::get<0>(entry) << ", "
                  << llvm_value_to_string(std::get<1>(entry)) << ", "
                  << std::get<2>(entry) << ", "
                  << std::get<3>(entry) << "\n";
    }

    std::cout << "\n--- Relation: null_ptr_set ---\n";
    for (const auto& entry : result.getNullPtrSet()) {
        std::cout << "  " << llvm_value_to_string(entry) << "\n";
    }

    std::cout << "\n--- Relation: callgraph ---\n";
    for (const auto& entry : result.getCallGraph()) {
        std::cout << "  Key: " << llvm_value_to_string(entry.first) << "\n";
        std::cout << ", Value: ("
                  << std::get<0>(entry.second) << ", "
                  << std::get<1>(entry.second) << ", "
                  << llvm_value_to_string(std::get<2>(entry.second)) << ")\n";
        std::cout << "\n";
    }

    // Print escape analysis relations
    std::cout << "\n--- Relation: mutated_or_escaped_global ---\n";
    auto mutated_or_escaped_rel = pa->relationToVector<boost::flyweight<std::string>>(
        "mutated_or_escaped_global", llvm_val_map);
    for (const auto& alloc_tuple : mutated_or_escaped_rel) {
        std::cout << "  " << std::get<0>(alloc_tuple) << "\n";
    }

    std::cout << "\n--- Relation: escaping_function_arg ---\n";
    auto escaping_arg_rel = pa->relationToVector<const llvm::Value *, int, int>(
        "escaping_function_arg", llvm_val_map);
    for (const auto& [func, index, reason] : escaping_arg_rel) {
        std::cout << "  Arg Index: " << index << ", Reason: " << reason << ", Function: " << llvm_value_to_string(func) << "\n";
    }

    std::cout << "\n--- Relation: func_without_defn ---\n";
    auto func_without_defn_rel = pa->relationToVector<const llvm::Value *>(
        "func_without_defn", llvm_val_map);
    for (const auto& func_tuple : func_without_defn_rel) {
        std::cout << "  " << llvm_value_to_string(std::get<0>(func_tuple)) << "\n";
    }

    // Read global_initializer_references relation
    auto global_init_refs_rel = pa->relationToVector<
        boost::flyweight<std::string>,
        boost::flyweight<std::string>>(
        "global_initializer_references", llvm_val_map);

    UniqueFilenameMapper ufm;

    // Print connected components relations
    std::string cc_prefix = da_str(cclyzer::datalog_analysis) + "_connected_components";

    std::cout << "\n--- Relation: " << cc_prefix << ".calls_target ---\n";
    auto calls_target_rel = pa->relationToVector<
        boost::flyweight<std::string>,
        boost::flyweight<std::string>>(
        cc_prefix + ".calls_target", llvm_val_map);
    for (const auto& [call_site, callee] : calls_target_rel) {

        std::cout << "  " << call_site;
        const llvm::Value* call_site_val = llvm_val_map.at(boost::flyweight<std::string>(call_site));
        if (call_site_val) {
            std::cout << "  " << llvm_call_site_to_string(call_site_val, ufm);
        }

        std::cout << " -> " << callee << "\n";
    }

    std::cout << "\n--- Relation: " << cc_prefix << ".component_representative ---\n";
    auto component_repr_rel = pa->relationToVector<
        boost::flyweight<std::string>,
        boost::flyweight<std::string>>(
        cc_prefix + ".component_representative", llvm_val_map);
    for (const auto& [node, repr] : component_repr_rel) {
        std::cout << "  " << node << " => " << repr << "\n";
    }

    std::cout << "\n--- Relation: " << cc_prefix << ".component_size ---\n";
    auto component_size_rel = pa->relationToVector<
        boost::flyweight<std::string>,
        int>(
        cc_prefix + ".component_size", llvm_val_map);
    for (const auto& [repr, size] : component_size_rel) {
        std::cout << "  Component " << repr << ": " << size << " nodes\n";
    }

    std::cout << "\n--- Relation: " << cc_prefix << ".component_call_site_count ---\n";
    auto component_call_site_count_rel = pa->relationToVector<
        boost::flyweight<std::string>,
        int>(
        cc_prefix + ".component_call_site_count", llvm_val_map);
    for (const auto& [repr, count] : component_call_site_count_rel) {
        std::cout << "  Component " << repr << ": " << count << " call sites\n";
    }

    std::cout << "\n--- Relation: " << cc_prefix << ".component_callee_count ---\n";
    auto component_callee_count_rel = pa->relationToVector<
        boost::flyweight<std::string>,
        int>(
        cc_prefix + ".component_callee_count", llvm_val_map);
    for (const auto& [repr, count] : component_callee_count_rel) {
        std::cout << "  Component " << repr << ": " << count << " callees\n";
    }

    std::cout << "\n--- Relation: " << cc_prefix << ".component_has_unknown_target ---\n";
    auto component_has_unknown_rel = pa->relationToVector<
        boost::flyweight<std::string>>(
        cc_prefix + ".component_has_unknown_target", llvm_val_map);
    for (const auto& repr_tuple : component_has_unknown_rel) {
        std::cout << "  Component " << std::get<0>(repr_tuple) << " has UNKNOWN targets\n";
    }

    std::cout << "\n--- Relation: " << cc_prefix << ".call_site_fully_resolved ---\n";
    auto call_site_fully_resolved_rel = pa->relationToVector<
        boost::flyweight<std::string>>(
        cc_prefix + ".call_site_fully_resolved", llvm_val_map);
    for (const auto& site_tuple : call_site_fully_resolved_rel) {
        std::cout << "  " << std::get<0>(site_tuple) << " (fully resolved)\n";
    }

    std::cout << "\n--- Relation: " << cc_prefix << ".call_site_partially_unknown ---\n";
    auto call_site_partially_unknown_rel = pa->relationToVector<
        boost::flyweight<std::string>>(
        cc_prefix + ".call_site_partially_unknown", llvm_val_map);
    for (const auto& site_tuple : call_site_partially_unknown_rel) {
        std::cout << "  " << std::get<0>(site_tuple) << " (partially unknown)\n";
    }

    std::cout << "\n--- Relation: " << cc_prefix << ".call_site_fully_unknown ---\n";
    auto call_site_fully_unknown_rel = pa->relationToVector<
        boost::flyweight<std::string>>(
        cc_prefix + ".call_site_fully_unknown", llvm_val_map);
    for (const auto& site_tuple : call_site_fully_unknown_rel) {
        std::cout << "  " << std::get<0>(site_tuple) << " (fully unknown)\n";
    }

    // Print mutable global tissue relations
    std::string tissue_prefix = da_str(cclyzer::datalog_analysis) + "_mutable_global_tissue";

    std::cout << "\n--- Relation: " << tissue_prefix << ".directly_accesses_mutable_global ---\n";
    auto directly_accesses_rel = pa->relationToVector<const llvm::Value *>(
        tissue_prefix + ".directly_accesses_mutable_global", llvm_val_map);
    for (const auto& func_tuple : directly_accesses_rel) {
        std::cout << "  " << llvm_value_to_string(std::get<0>(func_tuple)) << "\n";
    }

    std::cout << "\n--- Relation: " << tissue_prefix << ".mutable_global_tissue ---\n";
    auto tissue_rel = pa->relationToVector<const llvm::Value *>(
        tissue_prefix + ".mutable_global_tissue", llvm_val_map);
    for (const auto& func_tuple : tissue_rel) {
        std::cout << "  " << llvm_value_to_string(std::get<0>(func_tuple)) << "\n";
    }


    // 3. Print relation sizes
    std::cout << "Relation sizes:\n";
    std::cout << "  context_to_string: " << result.getContextToString().size() << "\n";
    std::cout << "  variable_points_to: " << result.getVariablePointsTo().size() << "\n";
    std::cout << "  pointer_points_to: " << result.getPointerPointsTo().size() << "\n";
    std::cout << "  alloc_may_alias: " << result.getAllocMayAlias().size() << "\n";
    std::cout << "  alloc_must_alias: " << result.getAllocMustAlias().size() << "\n";
    std::cout << "  alloc_subregion: " << result.getAllocSubregion().size() << "\n";
    std::cout << "  alloc_contains: " << result.getAllocContains().size() << "\n";
    std::cout << "  operand_points_to: " << result.getOperandPointsTo().size() << "\n";
    std::cout << "  global_allocations: " << result.getGlobalAllocations().size() << "\n";
    std::cout << "  allocation_sizes: " << result.getAllocationSizes().size() << "\n";
    std::cout << "  allocation_sites: " << result.getAllocationSites().size() << "\n";
    std::cout << "  null_ptr_set: " << result.getNullPtrSet().size() << "\n";
    std::cout << "  callgraph: " << result.getCallGraph().size() << "\n";
    std::cout << "  mutated_or_escaped_global: " << mutated_or_escaped_rel.size() << "\n";
    std::cout << "  escaping_function_arg: " << escaping_arg_rel.size() << "\n";
    std::cout << "  func_without_defn: " << func_without_defn_rel.size() << "\n";
    std::cout << "  " << cc_prefix << ".calls_target: " << calls_target_rel.size() << "\n";
    std::cout << "  " << cc_prefix << ".component_representative: " << component_repr_rel.size() << "\n";
    std::cout << "  " << cc_prefix << ".component_size: " << component_size_rel.size() << "\n";
    std::cout << "  " << cc_prefix << ".component_call_site_count: " << component_call_site_count_rel.size() << "\n";
    std::cout << "  " << cc_prefix << ".component_callee_count: " << component_callee_count_rel.size() << "\n";
    std::cout << "  " << cc_prefix << ".component_has_unknown_target: " << component_has_unknown_rel.size() << "\n";
    std::cout << "  " << cc_prefix << ".call_site_fully_resolved: " << call_site_fully_resolved_rel.size() << "\n";
    std::cout << "  " << cc_prefix << ".call_site_partially_unknown: " << call_site_partially_unknown_rel.size() << "\n";
    std::cout << "  " << cc_prefix << ".call_site_fully_unknown: " << call_site_fully_unknown_rel.size() << "\n";
    std::cout << "  " << tissue_prefix << ".directly_accesses_mutable_global: " << directly_accesses_rel.size() << "\n";
    std::cout << "  " << tissue_prefix << ".mutable_global_tissue: " << tissue_rel.size() << "\n";

    // Write JSON output if requested
    if (!JsonOutFilename.empty()) {
        std::ofstream json_file(JsonOutFilename);
        if (!json_file) {
            std::cerr << "Error: Failed to open JSON output file: " << JsonOutFilename << "\n";
            return 1;
        }

        json_file << "{\n";
        json_file << "  \"mutated_or_escaped_global\": [\n";

        bool first = true;
        for (const auto& alloc_tuple : mutated_or_escaped_rel) {
            std::string name = std::get<0>(alloc_tuple).get();
            auto processed_opt = process_global_name(name);

            if (processed_opt.has_value()) {
                if (!first) {
                    json_file << ",\n";
                }
                json_file << "    \"" << json_escape(processed_opt.value()) << "\"";
                first = false;
            }
        }

        json_file << "\n  ],\n";

        // Add connected components
        json_file << "  \"call_graph_components\": [\n";

        // Build a map from representative to component data
        // Tuple: (call_sites, call_targets, all_mutable)
        // all_mutable is true when component has no unknown or external targets
        std::map<std::string, std::tuple<std::set<std::string>, std::set<std::string>, bool>> components;

        // Build map of node -> representative
        std::map<std::string, std::string> node_to_repr;
        for (const auto& [node, repr] : component_repr_rel) {
            node_to_repr[node.get()] = repr.get();
        }

        // Build sets of all call sites and all call targets from calls_target relation
        std::set<std::string> all_call_sites;
        std::set<std::string> all_call_targets;

        for (const auto& [call_site, callee] : calls_target_rel) {
            std::string site_str = call_site.get();
            std::string callee_str = callee.get();

            all_call_sites.insert(site_str);
            if (callee_str != "UNKNOWN") {
                all_call_targets.insert(callee_str);
            }
        }

        // Get all nodes in each component
        auto call_graph_component_rel = pa->relationToVector<
            boost::flyweight<std::string>,
            boost::flyweight<std::string>>(
            cc_prefix + ".call_graph_component", llvm_val_map);

        // Collect call sites and callees for each component
        for (const auto& [node, _] : call_graph_component_rel) {
            std::string node_str = node.get();

            // Skip UNKNOWN nodes
            if (node_str == "UNKNOWN") {
                continue;
            }

            // Find representative for this node
            auto repr_it = node_to_repr.find(node_str);
            if (repr_it == node_to_repr.end()) {
                continue;
            }
            std::string repr = repr_it->second;

            // Initialize component entry if not exists
            // Default all_mutable = true (will be set to false if unknown/external found)
            if (components.find(repr) == components.end()) {
                components[repr] = std::make_tuple(
                    std::set<std::string>(),
                    std::set<std::string>(),
                    true); // default: all_mutable = true
            }

            // Categorize node as call site or call target based on calls_target relation
            if (all_call_sites.find(node_str) != all_call_sites.end()) {
                std::get<0>(components[repr]).insert(node_str); // call_sites
            }
            if (all_call_targets.find(node_str) != all_call_targets.end()) {
                std::get<1>(components[repr]).insert(node_str); // call_targets
            }
        }

        // Check for components with UNKNOWN targets
        // Mark them as not all_mutable (all_mutable = false)
        for (const auto& repr_tuple : component_has_unknown_rel) {
            std::string repr = std::get<0>(repr_tuple).get();
            if (components.find(repr) == components.end()) {
                components[repr] = std::make_tuple(
                    std::set<std::string>(),
                    std::set<std::string>(),
                    false); // not all_mutable because has unknown
            } else {
                std::get<2>(components[repr]) = false; // not all_mutable
            }
        }

        // Build set of functions without definitions (external functions)
        // Use the relationToVector that returns strings directly
        auto func_without_defn_str_rel = pa->relationToVector<boost::flyweight<std::string>>(
            "func_without_defn", llvm_val_map);
        std::set<std::string> external_funcs;
        for (const auto& func_tuple : func_without_defn_str_rel) {
            external_funcs.insert(std::get<0>(func_tuple).get());
        }

        // Build set of escaped function allocations
        std::set<std::string> escaped_funcs;
        for (const auto& alloc_tuple : mutated_or_escaped_rel) {
            std::string name = std::get<0>(alloc_tuple).get();
            // Strip "*global_alloc@" prefix if present
            const std::string prefix = "*global_alloc@";
            if (name.substr(0, prefix.length()) == prefix) {
                name = name.substr(prefix.length());
            }
            escaped_funcs.insert(name);
        }

        // Check for components with external or escaped functions
        // For components not yet in the map, they start with all_mutable = true
        // For components already marked (from unknown targets), we may need to additionally set all_mutable = false
        for (auto& [repr, data] : components) {
            const auto& call_targets = std::get<1>(data);

            // Check if component has external or escaped functions
            bool has_external_or_escaped = false;
            for (const auto& target : call_targets) {
                // Check if function is external (no definition)
                if (external_funcs.find(target) != external_funcs.end()) {
                    has_external_or_escaped = true;
                    break;
                }
                // Check if function is escaped
                // The target is in format "<file>:function" and escaped_funcs has "function"
                // so we need to extract just the function name
                std::string func_name = target;
                size_t colon_pos = func_name.rfind(':');
                if (colon_pos != std::string::npos) {
                    func_name = func_name.substr(colon_pos + 1);
                }
                // Escaped functions can be considered to have unknown call sites.
                if (escaped_funcs.find(func_name) != escaped_funcs.end()) {
                    has_external_or_escaped = true;
                    break;
                }
            }

            // Update all_mutable: it's only true if no unknown AND no external/escaped
            if (has_external_or_escaped) {
                std::get<2>(data) = false; // not all_mutable
            }
            // If not marked by unknown targets and no external/escaped, it remains true (default initialized to false, we'll fix below)
        }

        // Write components to JSON
        first = true;
        for (const auto& [repr, data] : components) {
            const auto& [call_sites, call_targets, all_mutable] = data;

            if (!first) {
                json_file << ",\n";
            }
            first = false;

            json_file << "    {\n";

            // Write call_sites
            json_file << "      \"call_sites\": [\n";
            bool first_site = true;
            for (const auto& site : call_sites) {
                if (!first_site) {
                    json_file << ",\n";
                }
                const llvm::Value* call_site_val = llvm_val_map.at(boost::flyweight<std::string>(site));
                if (call_site_val) {
                  json_file << "        " << llvm_call_site_to_string(call_site_val, ufm);
                } else {
                  json_file << "        \"" << json_escape(site) << "\"";
                }
                first_site = false;
            }
            json_file << "\n      ],\n";

            // Write call_targets
            json_file << "      \"call_targets\": [\n";
            bool first_target = true;
            for (const auto& target : call_targets) {
                if (!first_target) {
                    json_file << ",\n";
                }
                json_file << "        \"" << json_escape(target) << "\"";
                first_target = false;
            }
            json_file << "\n      ],\n";

            // Write all_mutable (true if no unknown and no external targets)
            json_file << "      \"all_mutable\": " << (all_mutable ? "true" : "false") << "\n";
            json_file << "    }";
        }

        json_file << "\n  ],\n";

        // Add unique filename mapping
        json_file << "  \"unique_filenames\": {\n";
        bool first_ufm = true;
        for (const auto& [shortName, fullPath] : ufm.shortToFull) {
            if (!first_ufm) {
                json_file << ",\n";
            }
            first_ufm = false;

            json_file << "  \"" << json_escape(shortName) << "\": {"
                << "\"directory\": \"" << json_escape(fullPath.first) << "\", "
                << "\"filename\": \"" << json_escape(fullPath.second) << "\"}";
        }
        json_file << "\n  },\n";


        // Add mutable global tissue
        json_file << "  \"mutable_global_tissue\": {\n";

        // Write directly_accesses_mutable_global
        json_file << "    \"directly_accesses\": [\n";
        first = true;
        for (const auto& func_tuple : directly_accesses_rel) {
            if (!first) {
                json_file << ",\n";
            }
            json_file << "      \"" << json_escape(llvm_value_to_string(std::get<0>(func_tuple))) << "\"";
            first = false;
        }
        json_file << "\n    ],\n";

        // Write mutable_global_tissue
        json_file << "    \"tissue\": [\n";
        first = true;
        for (const auto& func_tuple : tissue_rel) {
            if (!first) {
                json_file << ",\n";
            }
            json_file << "      \"" << json_escape(llvm_value_to_string(std::get<0>(func_tuple))) << "\"";
            first = false;
        }
        json_file << "\n    ]\n";
        json_file << "  },\n\n";

        // Write global_initializer_references
        json_file << "  \"global_initializer_references\": {\n";
        std::map<std::string, std::vector<std::string>> init_refs_map;
        for (const auto& [global_var, ref_name] : global_init_refs_rel) {
            std::string var_str = global_var.get();
            std::string name_str = ref_name.get();

            // Extract global variable name: from "<file>:@name" extract "name"
            auto at_pos = var_str.rfind(":@");
            if (at_pos != std::string::npos) {
                std::string var_name = var_str.substr(at_pos + 2); // skip ":@"

                // Strip leading "@" from referenced name for consistency
                std::string ref_name = name_str;
                if (!ref_name.empty() && ref_name[0] == '@') {
                    ref_name = ref_name.substr(1);
                }

                init_refs_map[var_name].push_back(ref_name);
            }
        }

        first = true;
        for (const auto& [var, refs] : init_refs_map) {
            // Filter out string constants (names starting with ".")
            std::vector<std::string> filtered_refs;
            for (const auto& ref : refs) {
                if (!ref.empty() && ref[0] != '.') {
                    filtered_refs.push_back(ref);
                }
            }

            // Skip entries with no non-string references
            if (filtered_refs.empty()) {
                continue;
            }

            if (!first) {
                json_file << ",\n";
            }
            json_file << "    \"" << json_escape(var) << "\": [\n";
            bool first_ref = true;
            for (const auto& ref : filtered_refs) {
                if (!first_ref) {
                    json_file << ",\n";
                }
                json_file << "      \"" << json_escape(ref) << "\"";
                first_ref = false;
            }
            json_file << "\n    ]";
            first = false;
        }
        json_file << "\n  }\n";

        json_file << "}\n";
        json_file.close();

        std::cout << "\nJSON output written to: " << JsonOutFilename << "\n";
    }

    return 0;
}
