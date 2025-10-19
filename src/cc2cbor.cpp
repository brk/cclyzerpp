#include <boost/filesystem.hpp>
#include <boost/flyweight.hpp>
#include <iostream>
#include <string>
#include <unordered_set>
#include <vector>

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

static llvm::cl::opt<std::string>
    InputFilename(
        llvm::cl::Positional, llvm::cl::desc("<input file>"), llvm::cl::Required);

auto factgen_module(
    llvm::Module &module,
    const fs::path &output_dir,
    const std::optional<boost::filesystem::path> &signatures,
    ContextSensitivity sensitivity)
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
  auto res_maps = gen.processModule(module, real_path, signatures, sensitivity);

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

// Helper function to convert llvm::Value* to string
std::string llvm_value_to_string(const llvm::Value* val) {
    std::string str;
    llvm::raw_string_ostream os(str);
    if (val) {
        val->print(os);
    } else {
        os << "nullptr";
    }
    return os.str();
}

int main(int argc, char *argv[]) {
    llvm::cl::ParseCommandLineOptions(argc, argv, "cclyzer++ standalone analysis\n");

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
        factgen_module(*module, output_dir, signatures_path, cclyzer::context_sensitivity);
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
            cclyzer::callgraph_edge(cclyzer::datalog_analysis), llvm_val_map);
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
    for (const auto& entry : result.getAllocMayAlias()) {
        std::cout << "  " << std::get<0>(entry) << ", "
                  << std::get<1>(entry) << ", "
                  << std::get<2>(entry) << "\n";
    }

    std::cout << "\n--- Relation: alloc_must_alias ---\n";
    for (const auto& entry : result.getAllocMustAlias()) {
        std::cout << "  " << std::get<0>(entry) << ", "
                  << std::get<1>(entry) << ", "
                  << std::get<2>(entry) << "\n";
    }

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
        std::cout << "  Key: " << llvm_value_to_string(entry.first) << ", Value: ("
                  << std::get<0>(entry.second) << ", "
                  << std::get<1>(entry.second) << ", "
                  << llvm_value_to_string(std::get<2>(entry.second)) << ")\n";
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

    return 0;
}
