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

