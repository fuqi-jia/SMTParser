/* -*- Header -*-
 * File/source conversion, including diagnostics, reports and output I/O.
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_TRANSLATION_CONVERT_HEADER
#define SOMTPARSER_TRANSLATION_CONVERT_HEADER

#include "somtparser/translation/language.h"

#include <iosfwd>
#include <optional>
#include <string>

namespace SOMTParser {

/** Settings for convert(). Unset profile/dialect select "default"/"gomt".
 *  Module exports reject explicitly selected query profiles or dialects. */
struct ConvertOptions {
    std::string language;
    std::optional<std::string> profile;
    std::optional<std::string> dialect;
    Lang::ParseOptions parse;
    std::string report;
    bool module = false;
};

struct ConvertResult {
    /** 0 success, 1 translation failure, 2 invalid settings, 3 I/O failure. */
    int exit_code = 0;
    std::string smt2;
    std::string diagnostics;
};

/** Convert without capturing a complete output script. Streams remain owned
 *  by the caller; output is flushed before success is returned. The input
 *  stream is read only for main_path == "-" without inline_source.
 *
 *  Link SOMTParser::languages; this function registers built-in languages.
 *  It does not parse command-line arguments or terminate the process.
 *  Diagnostics, report bytes and status codes retain the former converter's
 *  contract for the corresponding conversion settings. */
int convert(const Lang::SourceUnit& source, const ConvertOptions& options,
            std::istream& input, std::ostream& output, std::ostream& diagnostics);

/** Capture SMT-LIB and formatted diagnostics. For main_path == "-", read
 *  std::cin; callers needing another input stream can use the stream overload.
 *  Large outputs should use the stream overload to avoid a complete string. */
ConvertResult convert(const Lang::SourceUnit& source, const ConvertOptions& options = {});

} // namespace SOMTParser

#endif /* SOMTPARSER_TRANSLATION_CONVERT_HEADER */
