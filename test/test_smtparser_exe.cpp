#include <iostream>
#include <string>
#include <vector>
#include <chrono>
#include "../include/parser.h"
#include <fstream>

int main(int argc, char* argv[]){
    if (argc != 2) {
        std::cerr << "Usage: " << argv[0] << " <smt2_file>" << std::endl;
        return 1;
    }

    std::shared_ptr<SMTParser::Parser> parser = 
        std::make_shared<SMTParser::Parser>();
        // parser->setOption("keep_let", false);
    // the input file
    std::string input_file = argv[1];

    // Record start time
    auto start_time = std::chrono::high_resolution_clock::now();

    // parse the input file
    bool parse_success = parser->parse(input_file);

    // Record end time
    auto end_time = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end_time - start_time);

    if (parse_success) {
        std::cout << "PARSE_SUCCESS" << std::endl;
        
        // Print statistics
        auto assertions = parser->getAssertions();
        auto variables = parser->getVariables();
        auto functions = parser->getFunctions();
        
        std::cout << "ASSERTIONS:" << assertions.size() << std::endl;
        std::cout << "VARIABLES:" << variables.size() << std::endl;
        std::cout << "FUNCTIONS:" << functions.size() << std::endl;
        std::cout << "TIME:" << duration.count() << std::endl;

        std::ofstream ofs("./tmp.smt2");
        if (ofs.is_open()) {
            std::string smt2_content = parser->dumpSMT2();
            ofs << smt2_content;
            ofs.close();
            std::cout << "OUTPUT_FILE: ./tmp.smt2" << std::endl;
        } else {
            std::cout << "ERROR: Failed to open output file ./tmp.smt2" << std::endl;
        }

        return 0;
    } else {
        std::cout << "PARSE_FAILURE" << std::endl;
        std::cout << "TIME:" << duration.count() << std::endl;
        return 1;
    }
}