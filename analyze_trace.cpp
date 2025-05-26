/*
   WinAFL-PT Crash Analyzer & Trace Slicer
   ------------------------------------------------

   Created by Gyumin Baek <guminb@ajou.ac.kr> (2025)

   Copyright 2025 Gyumin Baek. All Rights Reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

 */


#include <fstream>
#include <vector>
#include <string>
#include <regex>
#include <iostream>
#include <set>
#include <sstream>  

struct instruction_frame {
    std::string symbol;
    std::string asm_line;
};

struct root_cause_info {
    std::string filePath;
    std::string mode;
    std::vector<instruction_frame> frames;
};


bool compare_root_cause_info(const root_cause_info& a, const root_cause_info& b)
{
    if (a.mode != b.mode) return false;
    if (a.frames.size() != b.frames.size()) return false;
    for (size_t i = 0; i < a.frames.size(); i++) {
        if (a.frames[i].symbol != b.frames[i].symbol ||
            a.frames[i].asm_line != b.frames[i].asm_line)
            return false;
    }
    return true;
}

bool parse_root_cause_file(const char *filePath, root_cause_info &info)
{
    std::ifstream in(filePath);
    if (!in) {
        std::cerr << "Failed to open file: " << filePath << "\n";
        return false;
    }
    info.filePath = filePath;
    info.mode = "";
    info.frames.clear();

    std::string line;
    bool modeFound = false;
    bool inFrameBlock = false;
    while (std::getline(in, line)) {

        if (!modeFound && line.find("Mode") != std::string::npos) {
            size_t colonPos = line.find(':');
            if (colonPos != std::string::npos) {
                info.mode = line.substr(colonPos + 1);

                info.mode.erase(0, info.mode.find_first_not_of(" \t"));
                info.mode.erase(info.mode.find_last_not_of(" \t\r\n") + 1);
            }
            modeFound = true;
            continue;
        }

        if (!inFrameBlock) {
            if (line.find("--- Slice Result") != std::string::npos ||
                line.find("--- Call Context") != std::string::npos) {
                inFrameBlock = true;
                continue;
            }
        }
        else {

            if (line.find("===") != std::string::npos)
                break;
            if (line.empty())
                continue;

            std::string symbol = line;
            std::string asm_line;
            if (!std::getline(in, asm_line))
                break;
            if (asm_line.find("===") != std::string::npos)
                break;

            symbol.erase(symbol.find_last_not_of(" \t\r\n") + 1);
            asm_line.erase(asm_line.find_last_not_of(" \t\r\n") + 1);
            instruction_frame frame { symbol, asm_line };
            info.frames.push_back(frame);
        }
    }
    in.close();
    return true;
}


extern "C" int deduplicate_root_cause_seeds(const char **sliceFiles, int sliceCount, int *uniqueIndices)
{
    std::vector<root_cause_info> seeds;
    for (int i = 0; i < sliceCount; i++) {
        root_cause_info info;
        if (parse_root_cause_file(sliceFiles[i], info)) {
            seeds.push_back(info);
        }
    }
    int n = static_cast<int>(seeds.size());
    std::vector<bool> uniqueFlags(n, true);
    for (int i = 0; i < n; i++) {
        if (!uniqueFlags[i])
            continue;
        for (int j = i + 1; j < n; j++) {
            if (uniqueFlags[j] && compare_root_cause_info(seeds[i], seeds[j])) {
                uniqueFlags[j] = false;
            }
        }
    }
    int uniqueCount = 0;
    for (int i = 0; i < n; i++) {
        if (uniqueFlags[i]) {
            uniqueIndices[uniqueCount++] = i;
        }
    }
    return uniqueCount;
}


extern "C" void analyze_trace_file(const char* trace_path, const char* coverage_module, const char* output_filepath, bool is64bit) {

    std::string module_name = coverage_module;
    if (size_t pos = module_name.find('.'); pos != std::string::npos) {
        module_name.resize(pos);
    }
    
    std::ifstream f(trace_path);
    if(!f) {
        std::cerr<<"Failed to open "<<trace_path<<"\n";
        return;
    }

    std::ofstream out(output_filepath);
    if (!out) {
        std::cerr << "Failed to open " << output_filepath << "\n";
        return;
    }


    std::vector<std::pair<std::string, std::string>> blocks;
    std::string line;
    bool started = false;
    while (std::getline(f, line)) {
        if (!started && line.find("Execution Trace Log:") != std::string::npos) {
            started = true;
            continue;
        }
        if (!started || line == "-------------------------------------------" || line.empty())
            continue;
        std::string sym = line;
        if (!std::getline(f, line))
            break;
        std::string asm_line = line;
        blocks.emplace_back(sym, asm_line);
    }
    f.close();

    if (blocks.empty()) {
        std::cout << "No blocks found in trace file.\n";
        return;
    }

    const auto& last_block = blocks.back();

    bool in_target = (last_block.first.find(module_name) != std::string::npos);

    out << "===========================================\n";
    out << "Trace Slice Analysis Report\n";
    out << "===========================================\n";
    out << "Input Trace    : " << trace_path << "\n";
    out << "Coverage Module: " << module_name << "\n";
    out << "Mode           : " << (in_target ? "BACKWARD SLICE" : "CALL CONTEXT") << "\n\n";

    static const std::string regs[] = {
        // GP registers (64/32/16/8)
        "rax", "eax", "ax", "al", "rbx", "ebx", "bx", "bl",
        "rcx", "ecx", "cx", "cl", "rdx", "edx", "dx", "dl",
        "rsi", "esi", "si", "sil", "rdi", "edi", "di", "dil",
        "rbp", "ebp", "bp", "bpl", "rsp", "esp", "sp", "spl",
        "r8", "r8d", "r8w", "r8b", "r9", "r9d", "r9w", "r9b",
        "r10", "r10d", "r10w", "r10b", "r11", "r11d", "r11w", "r11b",
        "r12", "r12d", "r12w", "r12b", "r13", "r13d", "r13w", "r13b",
        "r14", "r14d", "r14w", "r14b", "r15", "r15d", "r15w", "r15b",
        // SSE registers
        "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7",
        "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15"
    };

    std::string pattern = "\\b(";
    for (size_t i = 0; i < sizeof(regs) / sizeof(regs[0]); i++) {
        if (i) pattern += "|";
        pattern += regs[i];
    }
    pattern += ")\\b";
    std::regex reg_rx(pattern, std::regex::icase);
    std::regex call_rx(R"(\bcall\b)", std::regex::icase);

    if(!in_target) {
        int idx = (int)blocks.size()-2;
        if(blocks[idx].first.find(module_name)!=std::string::npos && std::regex_search(blocks[idx].second, call_rx)) {
            out << "--- Call Context (last 5 instructions) ---\n";
            int start = std::max(0, idx-5);
            for(int i=start; i<=idx+1 && i<(int)blocks.size(); i++) {
                out<<blocks[i].first<<"\n"<<blocks[i].second<<"\n\n";
            }
        }
        else{
            out << "*** No coverage module call found ***\n";
        }
        out << "===========================================\n";
        return;

    }
    else {
        std::set<std::string> regs_used;
        std::smatch m;
        std::string tmp = last_block.second;

        while (std::regex_search(tmp, m, reg_rx)) {
            regs_used.insert(m.str());
            tmp = m.suffix().str();
        }


        out << "--- Slice Registers ---\n";
        for(auto&r:regs_used){
            out<<" "<<r;
        }
        out<<"\n";
        
        std::vector<std::pair<std::string,std::string>> slice;
        slice.push_back(last_block);
        for(int i = (int)blocks.size()-2; i >= 0 && !regs_used.empty(); i--) {
            std::set<std::string> found;
            tmp = blocks[i].second;
            while(std::regex_search(tmp,m,reg_rx)) {
                found.insert(m.str()); 
                tmp = m.suffix().str();
            }

            bool overlap = false;
            for(auto&r:found) {
                if(regs_used.count(r)){ 
                    overlap = true; 
                    break; 
                }
            }
            
            if(!overlap) {
                continue;
            }

            slice.push_back(blocks[i]);
            std::istringstream iss(blocks[i].second);
            std::string addr, hexbytes, first, second, opcode, operands;
            iss >> addr >> hexbytes >> first;
            
            static const std::set<std::string> prefixes = {"rep","repe","repz","repne","lock"};
            if (prefixes.count(first)) {
                iss >> second;
                opcode = first + " " + second;
            } else {
                opcode = first;
            }
            
            std::getline(iss, operands);
            if (!operands.empty() && operands[0]==' '){
                operands.erase(0,1);
            }

            std::vector<std::string> opnds;
            std::istringstream op_stream(operands);
            std::string op;
            while (std::getline(op_stream, op, ',')) {
                size_t s = op.find_first_not_of(" \t");
                size_t e = op.find_last_not_of(" \t");
                op = (s==std::string::npos ? "" : op.substr(s, e-s+1));
                opnds.push_back(op);
            }
            
            std::string op_lower = opcode;
            for (auto &ch : op_lower) {
                ch = std::tolower(ch);
            }

            bool initializes = false;
            if (!opnds.empty()) {
                const std::string &dest = opnds[0];
                if (regs_used.find(dest) != regs_used.end()) {
                    if ((op_lower.rfind("mov", 0) == 0) || op_lower == "lea" || op_lower == "pop" || op_lower == "xchg" || op_lower == "and") {
                        initializes = true;
                    } else if ((op_lower == "sub" || op_lower == "sbb" || op_lower == "xor" ) && opnds.size() >= 2 && opnds[0] == opnds[1]) {
                        initializes = true;
                    }
                    
                    if (initializes) {
                        regs_used.erase(dest);
                        for (size_t j = 1; j < opnds.size(); ++j) {
                            const auto &src = opnds[j];
                            if (src != dest && std::regex_match(src, reg_rx)) {
                                regs_used.insert(src);
                            }
                        }
                    }
                }
            }
            
            if (regs_used.empty()) {
                break;
            }


        }

        out << "--- Slice Result ---\n";
        for(auto it=slice.rbegin(); it!=slice.rend(); ++it){
            out<<it->first<<"\n"<<it->second<<"\n\n";
        }
        out << "===========================================\n";
    }

}
