#!/bin/sh
cargo build --release || exit 1
export ONE_FILE=1
export PANIC_ON_FAIL=1
export RUST_BACKTRACE=1
NO_ACCOM=1 NO_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_ACCOM=1 NO_EXPORT=1 NO_CACHE=1 failed"
NO_ACCOM=1 NO_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_ACCOM=1 NO_EXPORT=1 failed"
NO_ACCOM=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_ACCOM=1 failed"
NO_ACCOM=1 VERIFY_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_ACCOM=1 VERIFY_EXPORT=1 NO_CACHE=1 failed"
NO_ACCOM=1 VERIFY_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_ACCOM=1 VERIFY_EXPORT=1 failed"
NO_ACCOM=1 VERIFY_EXPORT=1 XML_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_ACCOM=1 VERIFY_EXPORT=1 XML_EXPORT=1 NO_CACHE=1 failed"
NO_ACCOM=1 VERIFY_EXPORT=1 XML_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_ACCOM=1 VERIFY_EXPORT=1 XML_EXPORT=1 failed"
NO_ACCOM=1 XML_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_ACCOM=1 XML_EXPORT=1 NO_CACHE=1 failed"
NO_ACCOM=1 XML_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_ACCOM=1 XML_EXPORT=1 failed"
NO_CHECKER=1 NO_ACCOM=1 NO_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_CHECKER=1 NO_ACCOM=1 NO_EXPORT=1 NO_CACHE=1 failed"
NO_CHECKER=1 NO_ACCOM=1 NO_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_CHECKER=1 NO_ACCOM=1 NO_EXPORT=1 failed"
NO_CHECKER=1 NO_ACCOM=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_CHECKER=1 NO_ACCOM=1 failed"
NO_CHECKER=1 NO_ACCOM=1 VERIFY_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_CHECKER=1 NO_ACCOM=1 VERIFY_EXPORT=1 NO_CACHE=1 failed"
NO_CHECKER=1 NO_ACCOM=1 VERIFY_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_CHECKER=1 NO_ACCOM=1 VERIFY_EXPORT=1 failed"
NO_CHECKER=1 NO_ACCOM=1 VERIFY_EXPORT=1 XML_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_CHECKER=1 NO_ACCOM=1 VERIFY_EXPORT=1 XML_EXPORT=1 NO_CACHE=1 failed"
NO_CHECKER=1 NO_ACCOM=1 VERIFY_EXPORT=1 XML_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_CHECKER=1 NO_ACCOM=1 VERIFY_EXPORT=1 XML_EXPORT=1 failed"
NO_CHECKER=1 NO_ACCOM=1 XML_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_CHECKER=1 NO_ACCOM=1 XML_EXPORT=1 NO_CACHE=1 failed"
NO_CHECKER=1 NO_ACCOM=1 XML_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_CHECKER=1 NO_ACCOM=1 XML_EXPORT=1 failed"
NO_CHECKER=1 NO_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_CHECKER=1 NO_EXPORT=1 NO_CACHE=1 failed"
NO_CHECKER=1 NO_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_CHECKER=1 NO_EXPORT=1 failed"
NO_CHECKER=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_CHECKER=1 failed"
NO_CHECKER=1 VERIFY_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_CHECKER=1 VERIFY_EXPORT=1 NO_CACHE=1 failed"
NO_CHECKER=1 VERIFY_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_CHECKER=1 VERIFY_EXPORT=1 failed"
NO_CHECKER=1 VERIFY_EXPORT=1 XML_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_CHECKER=1 VERIFY_EXPORT=1 XML_EXPORT=1 NO_CACHE=1 failed"
NO_CHECKER=1 VERIFY_EXPORT=1 XML_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_CHECKER=1 VERIFY_EXPORT=1 XML_EXPORT=1 failed"
NO_CHECKER=1 XML_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_CHECKER=1 XML_EXPORT=1 NO_CACHE=1 failed"
NO_CHECKER=1 XML_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_CHECKER=1 XML_EXPORT=1 failed"
NO_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_EXPORT=1 NO_CACHE=1 failed"
NO_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_EXPORT=1 failed"
NO_NAME_CHECK=1 NO_ACCOM=1 NO_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_ACCOM=1 NO_EXPORT=1 NO_CACHE=1 failed"
NO_NAME_CHECK=1 NO_ACCOM=1 NO_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_ACCOM=1 NO_EXPORT=1 failed"
NO_NAME_CHECK=1 NO_ACCOM=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_ACCOM=1 failed"
NO_NAME_CHECK=1 NO_ACCOM=1 VERIFY_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_ACCOM=1 VERIFY_EXPORT=1 NO_CACHE=1 failed"
NO_NAME_CHECK=1 NO_ACCOM=1 VERIFY_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_ACCOM=1 VERIFY_EXPORT=1 failed"
NO_NAME_CHECK=1 NO_ACCOM=1 VERIFY_EXPORT=1 XML_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_ACCOM=1 VERIFY_EXPORT=1 XML_EXPORT=1 NO_CACHE=1 failed"
NO_NAME_CHECK=1 NO_ACCOM=1 VERIFY_EXPORT=1 XML_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_ACCOM=1 VERIFY_EXPORT=1 XML_EXPORT=1 failed"
NO_NAME_CHECK=1 NO_ACCOM=1 XML_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_ACCOM=1 XML_EXPORT=1 NO_CACHE=1 failed"
NO_NAME_CHECK=1 NO_ACCOM=1 XML_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_ACCOM=1 XML_EXPORT=1 failed"
NO_NAME_CHECK=1 NO_ANALYZER=1 NO_ACCOM=1 NO_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_ANALYZER=1 NO_ACCOM=1 NO_EXPORT=1 NO_CACHE=1 failed"
NO_NAME_CHECK=1 NO_ANALYZER=1 NO_ACCOM=1 NO_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_ANALYZER=1 NO_ACCOM=1 NO_EXPORT=1 failed"
NO_NAME_CHECK=1 NO_ANALYZER=1 NO_CHECKER=1 NO_ACCOM=1 NO_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_ANALYZER=1 NO_CHECKER=1 NO_ACCOM=1 NO_EXPORT=1 NO_CACHE=1 failed"
NO_NAME_CHECK=1 NO_ANALYZER=1 NO_CHECKER=1 NO_ACCOM=1 NO_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_ANALYZER=1 NO_CHECKER=1 NO_ACCOM=1 NO_EXPORT=1 failed"
NO_NAME_CHECK=1 NO_ANALYZER=1 NO_CHECKER=1 NO_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_ANALYZER=1 NO_CHECKER=1 NO_EXPORT=1 NO_CACHE=1 failed"
NO_NAME_CHECK=1 NO_ANALYZER=1 NO_CHECKER=1 NO_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_ANALYZER=1 NO_CHECKER=1 NO_EXPORT=1 failed"
NO_NAME_CHECK=1 NO_ANALYZER=1 NO_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_ANALYZER=1 NO_EXPORT=1 NO_CACHE=1 failed"
NO_NAME_CHECK=1 NO_ANALYZER=1 NO_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_ANALYZER=1 NO_EXPORT=1 failed"
NO_NAME_CHECK=1 NO_CHECKER=1 NO_ACCOM=1 NO_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_CHECKER=1 NO_ACCOM=1 NO_EXPORT=1 NO_CACHE=1 failed"
NO_NAME_CHECK=1 NO_CHECKER=1 NO_ACCOM=1 NO_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_CHECKER=1 NO_ACCOM=1 NO_EXPORT=1 failed"
NO_NAME_CHECK=1 NO_CHECKER=1 NO_ACCOM=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_CHECKER=1 NO_ACCOM=1 failed"
NO_NAME_CHECK=1 NO_CHECKER=1 NO_ACCOM=1 VERIFY_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_CHECKER=1 NO_ACCOM=1 VERIFY_EXPORT=1 NO_CACHE=1 failed"
NO_NAME_CHECK=1 NO_CHECKER=1 NO_ACCOM=1 VERIFY_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_CHECKER=1 NO_ACCOM=1 VERIFY_EXPORT=1 failed"
NO_NAME_CHECK=1 NO_CHECKER=1 NO_ACCOM=1 VERIFY_EXPORT=1 XML_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_CHECKER=1 NO_ACCOM=1 VERIFY_EXPORT=1 XML_EXPORT=1 NO_CACHE=1 failed"
NO_NAME_CHECK=1 NO_CHECKER=1 NO_ACCOM=1 VERIFY_EXPORT=1 XML_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_CHECKER=1 NO_ACCOM=1 VERIFY_EXPORT=1 XML_EXPORT=1 failed"
NO_NAME_CHECK=1 NO_CHECKER=1 NO_ACCOM=1 XML_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_CHECKER=1 NO_ACCOM=1 XML_EXPORT=1 NO_CACHE=1 failed"
NO_NAME_CHECK=1 NO_CHECKER=1 NO_ACCOM=1 XML_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_CHECKER=1 NO_ACCOM=1 XML_EXPORT=1 failed"
NO_NAME_CHECK=1 NO_CHECKER=1 NO_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_CHECKER=1 NO_EXPORT=1 NO_CACHE=1 failed"
NO_NAME_CHECK=1 NO_CHECKER=1 NO_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_CHECKER=1 NO_EXPORT=1 failed"
NO_NAME_CHECK=1 NO_CHECKER=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_CHECKER=1 failed"
NO_NAME_CHECK=1 NO_CHECKER=1 VERIFY_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_CHECKER=1 VERIFY_EXPORT=1 NO_CACHE=1 failed"
NO_NAME_CHECK=1 NO_CHECKER=1 VERIFY_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_CHECKER=1 VERIFY_EXPORT=1 failed"
NO_NAME_CHECK=1 NO_CHECKER=1 VERIFY_EXPORT=1 XML_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_CHECKER=1 VERIFY_EXPORT=1 XML_EXPORT=1 NO_CACHE=1 failed"
NO_NAME_CHECK=1 NO_CHECKER=1 VERIFY_EXPORT=1 XML_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_CHECKER=1 VERIFY_EXPORT=1 XML_EXPORT=1 failed"
NO_NAME_CHECK=1 NO_CHECKER=1 XML_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_CHECKER=1 XML_EXPORT=1 NO_CACHE=1 failed"
NO_NAME_CHECK=1 NO_CHECKER=1 XML_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_CHECKER=1 XML_EXPORT=1 failed"
NO_NAME_CHECK=1 NO_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_EXPORT=1 NO_CACHE=1 failed"
NO_NAME_CHECK=1 NO_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 NO_EXPORT=1 failed"
NO_NAME_CHECK=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 failed"
NO_NAME_CHECK=1 VERIFY_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 VERIFY_EXPORT=1 NO_CACHE=1 failed"
NO_NAME_CHECK=1 VERIFY_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 VERIFY_EXPORT=1 failed"
NO_NAME_CHECK=1 VERIFY_EXPORT=1 XML_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 VERIFY_EXPORT=1 XML_EXPORT=1 NO_CACHE=1 failed"
NO_NAME_CHECK=1 VERIFY_EXPORT=1 XML_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 VERIFY_EXPORT=1 XML_EXPORT=1 failed"
NO_NAME_CHECK=1 XML_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 XML_EXPORT=1 NO_CACHE=1 failed"
NO_NAME_CHECK=1 XML_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "NO_NAME_CHECK=1 XML_EXPORT=1 failed"
PARSER=1 NO_CHECKER=1 NO_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "PARSER=1 NO_CHECKER=1 NO_EXPORT=1 NO_CACHE=1 failed"
PARSER=1 NO_CHECKER=1 NO_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "PARSER=1 NO_CHECKER=1 NO_EXPORT=1 failed"
PARSER=1 NO_CHECKER=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "PARSER=1 NO_CHECKER=1 failed"
PARSER=1 NO_CHECKER=1 VERIFY_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "PARSER=1 NO_CHECKER=1 VERIFY_EXPORT=1 NO_CACHE=1 failed"
PARSER=1 NO_CHECKER=1 VERIFY_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "PARSER=1 NO_CHECKER=1 VERIFY_EXPORT=1 failed"
PARSER=1 NO_CHECKER=1 VERIFY_EXPORT=1 XML_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "PARSER=1 NO_CHECKER=1 VERIFY_EXPORT=1 XML_EXPORT=1 NO_CACHE=1 failed"
PARSER=1 NO_CHECKER=1 VERIFY_EXPORT=1 XML_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "PARSER=1 NO_CHECKER=1 VERIFY_EXPORT=1 XML_EXPORT=1 failed"
PARSER=1 NO_CHECKER=1 XML_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "PARSER=1 NO_CHECKER=1 XML_EXPORT=1 NO_CACHE=1 failed"
PARSER=1 NO_CHECKER=1 XML_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "PARSER=1 NO_CHECKER=1 XML_EXPORT=1 failed"
PARSER=1 NO_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "PARSER=1 NO_EXPORT=1 NO_CACHE=1 failed"
PARSER=1 NO_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "PARSER=1 NO_EXPORT=1 failed"
PARSER=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "PARSER=1 failed"
PARSER=1 VERIFY_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "PARSER=1 VERIFY_EXPORT=1 NO_CACHE=1 failed"
PARSER=1 VERIFY_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "PARSER=1 VERIFY_EXPORT=1 failed"
PARSER=1 VERIFY_EXPORT=1 XML_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "PARSER=1 VERIFY_EXPORT=1 XML_EXPORT=1 NO_CACHE=1 failed"
PARSER=1 VERIFY_EXPORT=1 XML_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "PARSER=1 VERIFY_EXPORT=1 XML_EXPORT=1 failed"
PARSER=1 XML_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "PARSER=1 XML_EXPORT=1 NO_CACHE=1 failed"
PARSER=1 XML_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "PARSER=1 XML_EXPORT=1 failed"
RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "failed"
VERIFY_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "VERIFY_EXPORT=1 NO_CACHE=1 failed"
VERIFY_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "VERIFY_EXPORT=1 failed"
VERIFY_EXPORT=1 XML_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "VERIFY_EXPORT=1 XML_EXPORT=1 NO_CACHE=1 failed"
VERIFY_EXPORT=1 XML_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "VERIFY_EXPORT=1 XML_EXPORT=1 failed"
XML_EXPORT=1 NO_CACHE=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "XML_EXPORT=1 NO_CACHE=1 failed"
XML_EXPORT=1 RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo "XML_EXPORT=1 failed"

# names = {"parser_enabled", "early_formats", "nameck_enabled",
#    "analyzer_enabled", "analyzer_full", "checker_enabled",
#    "accom_enabled", "verify_export", "xml_export", "exporter_enabled",
#     "cache_prel"};
# Association[Rule @@ # & /@ ({%, #}\[Transpose])] & /@
#   Tuples[{False, True}, Length[%]];
# f = (Implies[#["parser_enabled"],
#       #["accom_enabled"] && #["early_formats"] && #[
#         "nameck_enabled"]] &&
#      Implies[#["nameck_enabled"] || #["exporter_enabled"] || #[
#         "analyzer_full"], #["analyzer_enabled"]] &&
#      Implies[#["checker_enabled"] && #["analyzer_enabled"], #[
#        "analyzer_full"]] &&
#      Implies[#["xml_export"] || #["verify_export"], #[
#        "exporter_enabled"]] &&
#      Implies[#[
#        "exporter_enabled"], #["xml_export"] || #[
#         "verify_export"] || #["cache_prel"]]
#     (*Which[#["parser_enabled"],".miz",#["nameck_enabled"],".wsx",#[
#     "analyzer_enabled"],".msx",#["checker_enabled"],".xml",True,
#     "none"]==".wsx"*)
#     ) &;
# out = Select[%%, f];
# StringJoin@
#  Union[With[{p =
#        StringJoin[{If[#["parser_enabled"], "PARSER=1 ", ""],
#          If[! #["nameck_enabled"], "NO_NAME_CHECK=1 ", ""],
#          If[! #["analyzer_enabled"], "NO_ANALYZER=1 ", ""],
#          If[! #["checker_enabled"], "NO_CHECKER=1 ", ""],
#          If[! #["accom_enabled"], "NO_ACCOM=1 ", ""],
#          If[#["verify_export"], "VERIFY_EXPORT=1 ", ""],
#          If[#["xml_export"], "XML_EXPORT=1 ", ""],
#          If[! #["exporter_enabled"], "NO_EXPORT=1 ", ""],
#          If[! #["cache_prel"], "NO_CACHE=1 ", ""]}]},
#      p <>
#       "RUST_BACKTRACE=1 target/release/miz-rs $@ 2>> out.log || echo \
# \"" <> p <> "failed\"\n"] & /@ out]
