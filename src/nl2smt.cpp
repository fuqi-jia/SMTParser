/* -*- Source -*-
 * parseNL: NL -> Plan (JSON) -> Builder (DAG) or SMT2 fallback. Only compiled when BUILD_NL2SMT=ON.
 * LiteLLM Proxy (OpenAI-compatible HTTP) + cpp-httplib + nlohmann/json.
 */
#ifdef SMTLIBPARSER_ENABLE_NL2SMT

#include "parser.h"
#include "dag.h"
#include "kind.h"
#include "sort.h"
#include "objective.h"
#include "options.h"
#include "util.h"
#include "nl2smt.h"
#include <nlohmann/json.hpp>
#include <httplib.h>
#ifdef assert
#undef assert
#endif
#include <algorithm>
#include <cstdlib>
#include <fstream>
#include <sstream>
#include <string>
#include <unordered_map>
#include <vector>

#if defined(_WIN32) || defined(_WIN64)
#include <direct.h>
#else
#include <sys/stat.h>
#endif

namespace SMTParser {

namespace {

using json = nlohmann::json;

static std::string loadPrompt(const std::string& path, const char* defaultPrompt);
static void writeArtifact(const std::string& dir, const std::string& name, const std::string& content);

// ---------- Default prompts (embedded) ----------
// LD: Logical Decomposition — symbols, skeleton (and/or/not/implies + P1,P2,...), proposition map (Pi -> NL clause). No SMT AST, no SMT text.
const char* const DEFAULT_PROMPT_LD = R"(You are an expert in formal logic. Output ONLY valid JSON. No markdown, no explanation.

Logical Decomposition schema:
{
  "logic": "QF_LIA" or "QF_LRA" or "QF_BV" or null,
  "symbols": [ {"name": "x", "sort": {"kind": "Int"}}, {"name": "y", "sort": {"kind": "Real"}} ],
  "skeleton": { "op": "and", "args": [ "P1", { "op": "or", "args": [ "P2", "P3" ] } ] },
  "propositions": { "P1": "x is positive", "P2": "y is less than 10", "P3": "z equals zero" },
  "objective": { "sense": "min" or "max" or "none", "proposition": "P4" or "term": null }
}

skeleton: logic connectives "and", "or", "not", "implies" with args = proposition ids (e.g. "P1") or nested skeleton. Leaves are only P1, P2, ...
propositions: each key (P1, P2, ...) maps to one boolean constraint phrase. Every proposition must be a constraint, not a type; put type info in symbols only. Use logic QF_LRA when any variable is Real. No SMT, no code.

Translate the following natural language into this JSON (symbols + skeleton + propositions only):

<<<USER_INPUT>>>)";

// APT: Atomic Proposition Translation — one NL clause -> JSON expr tree (variable/const/op/args). Used per proposition.
const char* const DEFAULT_PROMPT_APT = R"(Output ONLY a JSON expression tree. No markdown, no explanation.

Format: {"op": "le", "args": [{"op": "var", "name": "x"}, {"op": "const", "sort": {"kind": "Int"}, "value": "0"}]}
Ops: var, const, and, or, not, implies, le, lt, ge, gt, add, sub, mul, ite. Sort: {"kind": "Int"}|{"kind": "Real"}|{"kind": "Bool"}.

Translate this single constraint into one JSON expr tree:

<<<PROPOSITION>>>)";

const char* const DEFAULT_PROMPT_REPAIR = R"(The previous SMT-LIB2 failed to parse. Fix it. Output ONLY corrected SMT-LIB2. No explanations. Preserve semantics. Do not introduce new symbols.

Parser error:
<<<ERROR_MESSAGE>>>

Plan (reference):
<<<PLAN_JSON>>>

Previous SMT2:
<<<PREVIOUS_SMT>>>

Fix the SMT-LIB2.)";

const char* const DEFAULT_PROMPT_LEGACY = R"(Translate the following natural language into valid SMT-LIB2. Output ONLY SMT-LIB2. No markdown, no explanations.

<<<USER_INPUT>>>)";

// ---------- HTTP LLM call ----------
static std::string getApiKey() {
    const char* k = std::getenv("NL2SMT_API_KEY");
    if (k && k[0] != '\0') return k;
    k = std::getenv("OPENAI_API_KEY");
    if (k && k[0] != '\0') return k;
    return "";
}

static std::string stripMarkdown(const std::string& s) {
    std::string t = s;
    while (!t.empty() && (t.back() == '\r' || t.back() == '\n')) t.pop_back();
    if (t.size() >= 3 && t.substr(0, 3) == "```") {
        size_t first = t.find('\n');
        if (first != std::string::npos) t = t.substr(first + 1);
        else t = t.substr(3);
    }
    if (t.size() >= 3 && t.substr(t.size() - 3) == "```") t = t.substr(0, t.size() - 3);
    while (!t.empty() && (t.back() == '\r' || t.back() == '\n')) t.pop_back();
    return t;
}

static bool callLLM(const std::string& endpoint, const std::string& path,
                    const std::string& model, double temperature,
                    const std::string& systemContent, const std::string& userContent,
                    int timeout_sec, std::string* outContent, std::string* outError) {
    std::string host;
    bool useSsl = false;
    if (endpoint.find("https://") == 0) {
        useSsl = true;
        size_t start = 8;
        size_t slash = endpoint.find('/', start);
        host = (slash == std::string::npos) ? endpoint.substr(start) : endpoint.substr(start, slash - start);
    } else if (endpoint.find("http://") == 0) {
        size_t start = 7;
        size_t slash = endpoint.find('/', start);
        host = (slash == std::string::npos) ? endpoint.substr(start) : endpoint.substr(start, slash - start);
    } else {
        if (outError) *outError = "Endpoint must start with http:// or https://";
        return false;
    }
    std::string requestPath = path.empty() ? "/" : path;
    size_t colon = host.find(':');
    std::string hostName = colon != std::string::npos ? host.substr(0, colon) : host;
    int port = 80;
    if (useSsl) port = 443;
    if (colon != std::string::npos && colon + 1 < host.size())
        port = std::stoi(host.substr(colon + 1));

    json body;
    body["model"] = model;
    body["temperature"] = temperature;
    body["messages"] = json::array({
        json::object({{"role", "system"}, {"content", systemContent}}),
        json::object({{"role", "user"}, {"content", userContent}})
    });
    std::string bodyStr = body.dump();

    httplib::Headers headers = {{"Content-Type", "application/json"}};
    std::string key = getApiKey();
    if (!key.empty()) headers.insert({"Authorization", "Bearer " + key});

    httplib::Result res;
#ifdef CPPHTTPLIB_OPENSSL_SUPPORT
    if (useSsl) {
        httplib::SSLClient cli(hostName, port);
        cli.set_connection_timeout(timeout_sec, 0);
        cli.set_read_timeout(timeout_sec, 0);
        cli.set_write_timeout(timeout_sec, 0);
        res = cli.Post(requestPath, headers, bodyStr, "application/json");
    } else
#endif
    {
        if (useSsl) {
            if (outError) *outError = "HTTPS requires build with OpenSSL (CPPHTTPLIB_OPENSSL_SUPPORT)";
            return false;
        }
        httplib::Client cli(hostName, port);
        cli.set_connection_timeout(timeout_sec, 0);
        cli.set_read_timeout(timeout_sec, 0);
        cli.set_write_timeout(timeout_sec, 0);
        res = cli.Post(requestPath, headers, bodyStr, "application/json");
    }
    if (!res) {
        if (outError) *outError = "HTTP request failed (connection/timeout)";
        return false;
    }
    if (res->status != 200) {
        if (outError) *outError = "HTTP " + std::to_string(res->status) + (res->body.empty() ? "" : ": " + res->body.substr(0, 200));
        return false;
    }
    try {
        json j = json::parse(res->body);
        if (j.contains("choices") && j["choices"].is_array() && !j["choices"].empty()) {
            auto& c = j["choices"][0];
            if (c.contains("message") && c["message"].contains("content"))
                *outContent = stripMarkdown(c["message"]["content"].get<std::string>());
            else { if (outError) *outError = "No content in response"; return false; }
        } else { if (outError) *outError = "Invalid response structure"; return false; }
    } catch (const std::exception& e) {
        if (outError) *outError = std::string("Parse response: ") + e.what();
        return false;
    }
    return true;
}

// ---------- Plan JSON -> Sort ----------
static std::shared_ptr<Sort> sortFromPlan(const json& sortJson, Parser* parser) {
    if (sortJson.is_string()) {
        std::string s = sortJson.get<std::string>();
        if (s == "Int") return SortManager::INT_SORT;
        if (s == "Real") return SortManager::REAL_SORT;
        if (s == "Bool") return SortManager::BOOL_SORT;
        if (s.size() > 7 && s.substr(0, 7) == "(BitVec ") {
            size_t n = static_cast<size_t>(std::stoull(s.substr(7)));
            return parser->getSortManager()->createBVSort(n);
        }
        return nullptr;
    }
    if (sortJson.is_object() && sortJson.contains("kind")) {
        std::string k = sortJson["kind"].get<std::string>();
        if (k == "Int") return SortManager::INT_SORT;
        if (k == "Real") return SortManager::REAL_SORT;
        if (k == "Bool") return SortManager::BOOL_SORT;
        if (k == "BV" && sortJson.contains("size"))
            return parser->getSortManager()->createBVSort(sortJson["size"].get<size_t>());
    }
    return nullptr;
}

// ---------- Op string -> NODE_KIND ----------
static NODE_KIND opToKind(const std::string& op) {
    static const std::unordered_map<std::string, NODE_KIND> map = {
        {"and", NODE_KIND::NT_AND}, {"or", NODE_KIND::NT_OR}, {"not", NODE_KIND::NT_NOT},
        {"=>", NODE_KIND::NT_IMPLIES}, {"implies", NODE_KIND::NT_IMPLIES},
        {"xor", NODE_KIND::NT_XOR},
        {"=", NODE_KIND::NT_EQ}, {"==", NODE_KIND::NT_EQ},
        {"distinct", NODE_KIND::NT_DISTINCT},
        {"<", NODE_KIND::NT_LT}, {"<=", NODE_KIND::NT_LE},
        {">", NODE_KIND::NT_GT}, {">=", NODE_KIND::NT_GE},
        {"le", NODE_KIND::NT_LE}, {"lt", NODE_KIND::NT_LT}, {"ge", NODE_KIND::NT_GE}, {"gt", NODE_KIND::NT_GT},
        {"+", NODE_KIND::NT_ADD}, {"add", NODE_KIND::NT_ADD},
        {"-", NODE_KIND::NT_SUB}, {"sub", NODE_KIND::NT_SUB},
        {"*", NODE_KIND::NT_MUL}, {"mul", NODE_KIND::NT_MUL},
        {"div", NODE_KIND::NT_DIV_INT}, {"/", NODE_KIND::NT_DIV_REAL},
        {"mod", NODE_KIND::NT_MOD}, {"%", NODE_KIND::NT_MOD},
        {"abs", NODE_KIND::NT_ABS},
        {"ite", NODE_KIND::NT_ITE},
        {"bvadd", NODE_KIND::NT_BV_ADD}, {"bvsub", NODE_KIND::NT_BV_SUB}, {"bvmul", NODE_KIND::NT_BV_MUL},
        {"bvand", NODE_KIND::NT_BV_AND}, {"bvor", NODE_KIND::NT_BV_OR}, {"bvxor", NODE_KIND::NT_BV_XOR},
        {"bvult", NODE_KIND::NT_BV_ULT}, {"bvule", NODE_KIND::NT_BV_ULE},
        {"bvugt", NODE_KIND::NT_BV_UGT}, {"bvuge", NODE_KIND::NT_BV_UGE},
        {"bvslt", NODE_KIND::NT_BV_SLT}, {"bvsle", NODE_KIND::NT_BV_SLE},
        {"bvsgt", NODE_KIND::NT_BV_SGT}, {"bvsge", NODE_KIND::NT_BV_SGE},
    };
    auto it = map.find(op);
    if (it != map.end()) return it->second;
    return NODE_KIND::NT_UNKNOWN;
}

// ---------- Build one Expr from plan JSON ----------
static std::shared_ptr<DAGNode> buildExpr(Parser* p, const json& j,
    const std::unordered_map<std::string, std::shared_ptr<DAGNode>>& syms,
    std::string* outError) {
    if (j.is_null()) return nullptr;
    if (j.contains("var")) {
        std::string name = j["var"].get<std::string>();
        auto it = syms.find(name);
        if (it != syms.end()) return it->second;
        if (outError) *outError = "Unknown variable: " + name;
        return nullptr;
    }
    if (j.contains("op")) {
        std::string op = j["op"].get<std::string>();
        if (op == "var") {
            if (!j.contains("name")) { if (outError) *outError = "var missing name"; return nullptr; }
            std::string name = j["name"].get<std::string>();
            auto it = syms.find(name);
            if (it != syms.end()) return it->second;
            if (outError) *outError = "Unknown variable: " + name;
            return nullptr;
        }
        if (op == "const") {
            if (!j.contains("sort") || !j.contains("value")) { if (outError) *outError = "const missing sort/value"; return nullptr; }
            std::shared_ptr<Sort> sort = sortFromPlan(j["sort"], p);
            if (!sort) { if (outError) *outError = "Unsupported const sort"; return nullptr; }
            if (sort->isBool()) {
                bool v = false;
                if (j["value"].is_boolean()) v = j["value"].get<bool>();
                else if (j["value"].is_string()) v = (j["value"].get<std::string>() == "true");
                return v ? NodeManager::getTrue() : NodeManager::getFalse();
            }
            if (sort->isInt()) {
                std::string v;
                if (j["value"].is_string()) {
                    v = j["value"].get<std::string>();
                    if (!TypeChecker::isInt(v)) {
                        if (TypeChecker::isReal(v)) {
                            double d = std::stod(v);
                            v = std::to_string(static_cast<long long>(d));
                        } else
                            v = "0";
                    }
                } else if (j["value"].is_number_integer())
                    v = std::to_string(j["value"].get<int>());
                else if (j["value"].is_number_float())
                    v = std::to_string(static_cast<long long>(j["value"].get<double>()));
                else
                    v = "0";
                return p->mkConstInt(v);
            }
            if (sort->isReal()) {
                if (j["value"].is_number_float()) return p->mkConstReal(j["value"].get<double>());
                std::string v = j["value"].is_string() ? j["value"].get<std::string>() : std::to_string(j["value"].get<double>());
                return p->mkConstReal(v);
            }
            if (outError) *outError = "Unsupported const sort for Builder";
            return nullptr;
        }
        if (op == "bvconst") {
            if (!j.contains("size") || !j.contains("value")) { if (outError) *outError = "bvconst missing size/value"; return nullptr; }
            size_t sz = j["size"].get<size_t>();
            std::string val = j["value"].get<std::string>();
            return p->mkConstBv(val, sz);
        }
        std::vector<std::shared_ptr<DAGNode>> args;
        if (j.contains("args") && j["args"].is_array())
            for (const auto& a : j["args"]) {
                auto child = buildExpr(p, a, syms, outError);
                if (!child) return nullptr;
                args.push_back(child);
            }
        NODE_KIND kind = opToKind(op);
        if (kind == NODE_KIND::NT_UNKNOWN) {
            if (outError) *outError = "Unsupported op: " + op;
            return nullptr;
        }
        if (kind == NODE_KIND::NT_NOT) {
            if (args.size() != 1) { if (outError) *outError = "not expects 1 arg"; return nullptr; }
            return p->mkNot(args[0]);
        }
        if (kind == NODE_KIND::NT_AND) {
            if (args.empty()) { if (outError) *outError = "and expects >=1 arg"; return nullptr; }
            return p->mkAnd(args);
        }
        if (kind == NODE_KIND::NT_OR) {
            if (args.empty()) { if (outError) *outError = "or expects >=1 arg"; return nullptr; }
            return p->mkOr(args);
        }
        if (kind == NODE_KIND::NT_IMPLIES) {
            if (args.size() != 2) { if (outError) *outError = "implies expects 2 args"; return nullptr; }
            return p->mkImplies(args[0], args[1]);
        }
        if (kind == NODE_KIND::NT_XOR) {
            if (args.size() < 2) return nullptr;
            return args.size() == 2 ? p->mkXor(args[0], args[1]) : p->mkXor(args);
        }
        if (kind == NODE_KIND::NT_ITE) {
            if (args.size() != 3) { if (outError) *outError = "ite expects 3 args"; return nullptr; }
            return p->mkIte(args[0], args[1], args[2]);
        }
        if (kind == NODE_KIND::NT_EQ) {
            if (args.size() < 2) { if (outError) *outError = "= expects 2 args"; return nullptr; }
            return p->mkEq(args);
        }
        if (kind == NODE_KIND::NT_DISTINCT) {
            if (args.size() < 2) { if (outError) *outError = "distinct expects 2 args"; return nullptr; }
            return p->mkDistinct(args);
        }
        if (kind == NODE_KIND::NT_LE || kind == NODE_KIND::NT_LT || kind == NODE_KIND::NT_GE || kind == NODE_KIND::NT_GT) {
            if (args.size() != 2) { if (outError) *outError = "comparison expects 2 args"; return nullptr; }
            if (kind == NODE_KIND::NT_LE) return p->mkLe(args[0], args[1]);
            if (kind == NODE_KIND::NT_LT) return p->mkLt(args[0], args[1]);
            if (kind == NODE_KIND::NT_GE) return p->mkGe(args[0], args[1]);
            if (kind == NODE_KIND::NT_GT) return p->mkGt(args[0], args[1]);
        }
        if (kind == NODE_KIND::NT_ADD) { if (args.size() < 2) return nullptr; return p->mkAdd(args); }
        if (kind == NODE_KIND::NT_SUB) { if (args.size() < 2) return nullptr; return p->mkSub(args); }
        if (kind == NODE_KIND::NT_MUL) { if (args.size() < 2) return nullptr; return p->mkMul(args); }
        if (kind == NODE_KIND::NT_DIV_INT) { if (args.size() != 2) return nullptr; return p->mkDivInt(args[0], args[1]); }
        if (kind == NODE_KIND::NT_DIV_REAL) { if (args.size() != 2) return nullptr; return p->mkDivReal(args[0], args[1]); }
        if (kind == NODE_KIND::NT_MOD) { if (args.size() != 2) return nullptr; return p->mkMod(args[0], args[1]); }
        if (kind == NODE_KIND::NT_ABS) { if (args.size() != 1) return nullptr; return p->mkAbs(args[0]); }
        std::shared_ptr<Sort> outSort = args.empty() ? SortManager::BOOL_SORT : args[0]->getSort();
        if (kind == NODE_KIND::NT_BV_ADD || kind == NODE_KIND::NT_BV_SUB || kind == NODE_KIND::NT_BV_MUL ||
            kind == NODE_KIND::NT_BV_AND || kind == NODE_KIND::NT_BV_OR || kind == NODE_KIND::NT_BV_XOR ||
            (kind >= NODE_KIND::NT_BV_ULT && kind <= NODE_KIND::NT_BV_SGE))
            outSort = args[0]->getSort();
        return p->mkApp(outSort, kind, args);
    }
    if (j.contains("const")) {
        auto v = j["const"];
        if (v.is_boolean()) return v.get<bool>() ? NodeManager::getTrue() : NodeManager::getFalse();
        if (v.is_number_integer()) return p->mkConstInt(v.get<int>());
        if (v.is_number_float()) return p->mkConstReal(v.get<double>());
        if (v.is_string()) {
            std::string s = v.get<std::string>();
            if (TypeChecker::isInt(s)) return p->mkConstInt(s);
            if (TypeChecker::isReal(s)) return p->mkConstReal(s);
        }
    }
    if (outError) *outError = "Unknown expr node";
    return nullptr;
}

// ---------- Build full problem from plan ----------
static bool buildFromPlan(Parser* p, const json& plan, std::string* planJsonOut, std::string* lastError) {
    if (!plan.contains("symbols") || !plan["symbols"].is_array()) {
        if (lastError) *lastError = "Plan missing symbols array";
        return false;
    }
    std::unordered_map<std::string, std::shared_ptr<DAGNode>> syms;
    for (const auto& sym : plan["symbols"]) {
        if (!sym.contains("name")) continue;
        std::string name = sym["name"].get<std::string>();
        std::shared_ptr<Sort> sort = sortFromPlan(sym.contains("sort") ? sym["sort"] : json("Int"), p);
        if (!sort) {
            if (lastError) *lastError = "Unsupported sort for symbol " + name;
            return false;
        }
        if (sort->isBool()) syms[name] = p->mkVarBool(name);
        else if (sort->isInt()) syms[name] = p->mkVarInt(name);
        else if (sort->isReal()) syms[name] = p->mkVarReal(name);
        else if (sort->isBv()) syms[name] = p->mkVarBv(name, sort->getBitWidth());
        else syms[name] = p->mkVar(sort, name);
    }
    if (plan.contains("constraints")) {
        const auto& cs = plan["constraints"];
        if (cs.is_array()) {
            for (const auto& c : cs) {
                if (!c.contains("expr")) continue;
                std::string err;
                auto node = buildExpr(p, c["expr"], syms, &err);
                if (!node) {
                    if (lastError) *lastError = err.empty() ? "Failed to build constraint" : err;
                    return false;
                }
                p->assert(node);
            }
        } else if (cs.is_object() && cs.contains("op")) {
            std::string err;
            auto node = buildExpr(p, cs, syms, &err);
            if (!node) {
                if (lastError) *lastError = err.empty() ? "Failed to build constraint" : err;
                return false;
            }
            p->assert(node);
        }
    }
    if (plan.contains("objective") && plan["objective"].is_object()) {
        const auto& obj = plan["objective"];
        std::string sense = obj.contains("sense") ? obj["sense"].get<std::string>() : "none";
        if (sense != "none" && obj.contains("term") && !obj["term"].is_null()) {
            std::string err;
            auto term = buildExpr(p, obj["term"], syms, &err);
            if (!term) {
                if (lastError) *lastError = err.empty() ? "Failed to build objective term" : err;
                return false;
            }
            OPT_KIND optKind = (sense == "max") ? OPT_KIND::OPT_MAXIMIZE : OPT_KIND::OPT_MINIMIZE;
            COMP_KIND comp = getDefaultCompareOperator(p->getOptions()->logic, optKind);
            auto singleObj = std::make_shared<SingleObjective>(optKind, term, comp, NodeManager::NULL_NODE, NodeManager::NULL_NODE, "");
            auto objective = std::make_shared<Objective>(optKind, "");
            objective->addObjective(singleObj);
            p->objectives.push_back(objective);
        }
    }
    if (planJsonOut) *planJsonOut = plan.dump();
    return true;
}

static bool parseJsonStrict(const std::string& s, json* out, std::string* err) {
    try {
        *out = json::parse(s);
        return true;
    } catch (const std::exception& e) {
        if (err) *err = e.what();
        return false;
    }
}

// ---------- Structured: build DAG from skeleton + proposition nodes ----------
static std::shared_ptr<DAGNode> buildFromSkeleton(const json& skel,
    const std::unordered_map<std::string, std::shared_ptr<DAGNode>>& propNodes,
    const std::unordered_map<std::string, std::shared_ptr<DAGNode>>* allPropNodes,
    const std::unordered_map<std::string, std::shared_ptr<DAGNode>>* syms,
    Parser* p, std::string* outError) {
    if (skel.is_string()) {
        std::string id = skel.get<std::string>();
        auto it = propNodes.find(id);
        if (it != propNodes.end()) return it->second;
        if (allPropNodes) {
            auto ait = allPropNodes->find(id);
            if (ait != allPropNodes->end() && ait->second->getSort() && ait->second->getSort()->isBool())
                return ait->second;
            if (propNodes.empty() && allPropNodes->size() == 1 && allPropNodes->begin()->second->getSort()
                && allPropNodes->begin()->second->getSort()->isBool())
                return allPropNodes->begin()->second;
        }
        if (syms) {
            auto sit = syms->find(id);
            if (sit != syms->end() && sit->second->getSort() && sit->second->getSort()->isBool())
                return sit->second;
        }
        if (!propNodes.empty()) {
            if (propNodes.size() == 1)
                return propNodes.begin()->second;
            size_t idx = 0;
            if (id.size() > 1 && (id[0] == 'P' || id[0] == 'p') && std::isdigit(static_cast<unsigned char>(id[1]))) {
                idx = static_cast<size_t>(std::atoi(id.c_str() + 1));
                if (idx >= 1) {
                    std::vector<std::string> keys;
                    for (const auto& e : propNodes) keys.push_back(e.first);
                    std::sort(keys.begin(), keys.end());
                    size_t i = idx - 1;
                    if (i >= keys.size()) i = keys.size() - 1;
                    return propNodes.find(keys[i])->second;
                }
            }
        }
        if (allPropNodes && !allPropNodes->empty() && id.size() > 1 && (id[0] == 'P' || id[0] == 'p') && std::isdigit(static_cast<unsigned char>(id[1]))) {
            size_t idx = static_cast<size_t>(std::atoi(id.c_str() + 1));
            if (idx >= 1) {
                std::vector<std::string> keys;
                for (const auto& e : *allPropNodes) keys.push_back(e.first);
                std::sort(keys.begin(), keys.end());
                size_t i = idx - 1;
                if (i >= keys.size()) i = keys.size() - 1;
                auto node = allPropNodes->find(keys[i])->second;
                if (node->getSort() && node->getSort()->isBool()) return node;
            }
        }
        if (outError) {
            std::string avail;
            for (const auto& e : propNodes) { if (!avail.empty()) avail += ", "; avail += e.first; }
            if (avail.empty() && allPropNodes) for (const auto& e : *allPropNodes) { if (!avail.empty()) avail += ", "; avail += e.first; }
            *outError = "Unknown proposition id: " + id + " (available: " + (avail.empty() ? "none" : avail) + ")";
        }
        return nullptr;
    }
    if (!skel.is_object() || !skel.contains("op")) {
        if (outError) *outError = "Skeleton node must be string (Pi) or {op, args}";
        return nullptr;
    }
    std::string op = skel["op"].get<std::string>();
    std::vector<std::shared_ptr<DAGNode>> args;
    if (skel.contains("args") && skel["args"].is_array()) {
        for (const auto& a : skel["args"]) {
            auto child = buildFromSkeleton(a, propNodes, allPropNodes, syms, p, outError);
            if (!child) return nullptr;
            args.push_back(child);
        }
    }
    if (op == "and") {
        if (args.empty()) return p->mkTrue();
        return p->mkAnd(args);
    }
    if (op == "or") {
        if (args.empty()) return p->mkFalse();
        return p->mkOr(args);
    }
    if (op == "not") {
        if (args.size() == 1) return p->mkNot(args[0]);
        if (args.size() == 0 && allPropNodes && allPropNodes->size() == 1) {
            auto node = allPropNodes->begin()->second;
            if (node->getSort() && node->getSort()->isBool()) return p->mkNot(node);
        }
        if (outError) *outError = "not requires exactly one arg (got " + std::to_string(args.size()) + ")";
        return nullptr;
    }
    if (op == "implies") {
        if (args.size() != 2) { if (outError) *outError = "implies requires two args"; return nullptr; }
        return p->mkImplies(args[0], args[1]);
    }
    if (outError) *outError = "Unsupported skeleton op: " + op;
    return nullptr;
}

// ---------- Shared: parse SMT2 string with optional repair (used by both Structured and DirectTextual) ----------
static bool parseSmt2WithRepair(Parser* self, std::string* smt2InOut, const std::string& planJsonForRepair,
    const smtlib::NL2SMTOptions& opt, smtlib::NL2SMTReport* rpt, const std::string& artifactDir) {
    std::string& smt2 = *smt2InOut;
    Parser temp;
    int repairRounds = 0;
    for (;;) {
        if (temp.parseStr(smt2)) {
            self->swapContent(temp);
            if (rpt) { rpt->ok = true; rpt->smt2 = smt2; rpt->repair_rounds = repairRounds; rpt->artifacts_dir_used = artifactDir; }
            return true;
        }
        std::string parseErr = "Parse failed";
        if (repairRounds < opt.max_repair) {
            std::string repairPrompt = loadPrompt(opt.prompt_repair_path, DEFAULT_PROMPT_REPAIR);
            size_t p1 = repairPrompt.find("<<<ERROR_MESSAGE>>>");
            size_t p2 = repairPrompt.find("<<<PLAN_JSON>>>");
            size_t p3 = repairPrompt.find("<<<PREVIOUS_SMT>>>");
            if (p1 != std::string::npos) repairPrompt.replace(p1, 19, parseErr);
            if (p2 != std::string::npos) repairPrompt.replace(p2, 15, planJsonForRepair);
            if (p3 != std::string::npos) repairPrompt.replace(p3, 18, smt2);
            std::string err;
            if (callLLM(opt.endpoint, opt.path, opt.model, opt.temperature, "Output only corrected SMT-LIB2.", repairPrompt, opt.timeout_sec, &smt2, &err))
                smt2 = stripMarkdown(smt2);
            if (!artifactDir.empty())
                writeArtifact(artifactDir, "repair_" + std::to_string(repairRounds) + ".smt2", smt2);
            repairRounds++;
            continue;
        }
        if (rpt) { rpt->smt2 = smt2; rpt->last_error = parseErr; rpt->repair_rounds = repairRounds; rpt->artifacts_dir_used = artifactDir; }
        return false;
    }
}

// ---------- Structured pipeline: LD -> APT -> Builder -> dump SMT2 -> parse + optional repair ----------
static bool run_structured_pipeline(Parser* self, const std::string& nl, const smtlib::NL2SMTOptions& opt,
    smtlib::NL2SMTReport* rpt, const std::string& artifactDir) {
    std::string ldJson;
    std::string systemPrompt = "You output only valid JSON. No markdown, no explanation.";
    std::string userPrompt = loadPrompt(opt.prompt_ld_path, DEFAULT_PROMPT_LD);
    size_t pos = userPrompt.find("<<<USER_INPUT>>>");
    if (pos != std::string::npos) userPrompt.replace(pos, 16, nl);
    std::string err;
    if (!callLLM(opt.endpoint, opt.path, opt.model, opt.temperature, systemPrompt, userPrompt, opt.timeout_sec, &ldJson, &err)) {
        if (rpt) rpt->last_error = "LD LLM failed: " + err;
        return false;
    }
    json ld;
    if (!parseJsonStrict(ldJson, &ld, &err) || !ld.is_object()) {
        if (rpt) rpt->last_error = "LD JSON failed: " + err;
        return false;
    }
    if (!ld.contains("symbols") || !ld["symbols"].is_array() || !ld.contains("skeleton") || !ld.contains("propositions")
        || !ld["propositions"].is_object()) {
        if (rpt) rpt->last_error = "LD must contain symbols, skeleton, propositions";
        return false;
    }
    if (!artifactDir.empty()) writeArtifact(artifactDir, "ld.json", ldJson);

    Parser temp;
    if (ld.contains("logic") && !ld["logic"].is_null())
        temp.getOptions()->logic = ld["logic"].get<std::string>();
    std::unordered_map<std::string, std::shared_ptr<DAGNode>> syms;
    for (const auto& sym : ld["symbols"]) {
        if (!sym.contains("name")) continue;
        std::string name = sym["name"].get<std::string>();
        std::shared_ptr<Sort> sort = sortFromPlan(sym.contains("sort") ? sym["sort"] : json("Int"), &temp);
        if (!sort) continue;
        if (sort->isBool()) syms[name] = temp.mkVarBool(name);
        else if (sort->isInt()) syms[name] = temp.mkVarInt(name);
        else if (sort->isReal()) syms[name] = temp.mkVarReal(name);
        else if (sort->isBv()) syms[name] = temp.mkVarBv(name, sort->getBitWidth());
        else syms[name] = temp.mkVar(sort, name);
    }

    std::string aptPromptTemplate = loadPrompt(opt.prompt_apt_path, DEFAULT_PROMPT_APT);
    std::unordered_map<std::string, std::shared_ptr<DAGNode>> propNodes;
    std::unordered_map<std::string, std::shared_ptr<DAGNode>> allPropNodes;
    for (auto it = ld["propositions"].begin(); it != ld["propositions"].end(); ++it) {
        std::string pid = it.key();
        if (!it.value().is_string()) continue;
        std::string propText = it.value().get<std::string>();
        std::string aptUser = aptPromptTemplate;
        size_t ap = aptUser.find("<<<PROPOSITION>>>");
        if (ap != std::string::npos) aptUser.replace(ap, 17, propText);
        std::string aptOut;
        if (!callLLM(opt.endpoint, opt.path, opt.model, opt.temperature, "Output only valid JSON.", aptUser, opt.timeout_sec, &aptOut, &err)) {
            if (rpt) rpt->last_error = "APT LLM failed for " + pid + ": " + err;
            return false;
        }
        json exprJson;
        if (!parseJsonStrict(aptOut, &exprJson, &err)) continue;
        std::string buildErr;
        auto node = buildExpr(&temp, exprJson, syms, &buildErr);
        if (!node) continue;
        allPropNodes[pid] = node;
        if (node->getSort() && node->getSort()->isBool())
            propNodes[pid] = node;
    }

    std::string buildErr;
    auto mainConstraint = buildFromSkeleton(ld["skeleton"], propNodes, &allPropNodes, &syms, &temp, &buildErr);
    if (!mainConstraint) {
        if (rpt) rpt->last_error = "Builder failed: " + buildErr;
        if (!artifactDir.empty()) {
            std::ostringstream dbg;
            dbg << "skeleton: " << ld["skeleton"].dump() << "\n";
            dbg << "propositions (LD keys): ";
            if (ld.contains("propositions") && ld["propositions"].is_object()) {
                for (auto it = ld["propositions"].begin(); it != ld["propositions"].end(); ++it)
                    dbg << it.key() << " ";
            }
            dbg << "\npropNodes (bool only): ";
            for (const auto& e : propNodes) dbg << e.first << " ";
            dbg << "\nallPropNodes: ";
            for (const auto& e : allPropNodes) dbg << e.first << " ";
            dbg << "\nbuildErr: " << buildErr << "\n";
            writeArtifact(artifactDir, "builder_debug.txt", dbg.str());
        }
        return false;
    }
    temp.assert(mainConstraint);

    if (ld.contains("objective") && ld["objective"].is_object()) {
        const auto& obj = ld["objective"];
        std::string sense = obj.contains("sense") ? obj["sense"].get<std::string>() : "none";
        if (sense != "none") {
            std::shared_ptr<DAGNode> termNode = nullptr;
            if (obj.contains("proposition") && obj["proposition"].is_string()) {
                std::string pk = obj["proposition"].get<std::string>();
                auto it = allPropNodes.find(pk);
                if (it != allPropNodes.end()) termNode = it->second;
                if (!termNode && !allPropNodes.empty() && pk.size() > 1 && (pk[0] == 'P' || pk[0] == 'p') && std::isdigit(static_cast<unsigned char>(pk[1]))) {
                    size_t idx = static_cast<size_t>(std::atoi(pk.c_str() + 1));
                    if (idx >= 1) {
                        std::vector<std::string> okeys;
                        for (const auto& e : allPropNodes) okeys.push_back(e.first);
                        std::sort(okeys.begin(), okeys.end());
                        size_t i = idx - 1;
                        if (i >= okeys.size()) i = okeys.size() - 1;
                        termNode = allPropNodes.find(okeys[i])->second;
                    }
                }
            }
            if (!termNode && obj.contains("term") && !obj["term"].is_null())
                termNode = buildExpr(&temp, obj["term"], syms, &buildErr);
            if (termNode) {
                OPT_KIND optKind = (sense == "max") ? OPT_KIND::OPT_MAXIMIZE : OPT_KIND::OPT_MINIMIZE;
                COMP_KIND comp = getDefaultCompareOperator(temp.getOptions()->logic, optKind);
                auto singleObj = std::make_shared<SingleObjective>(optKind, termNode, comp, NodeManager::NULL_NODE, NodeManager::NULL_NODE, "");
                auto objective = std::make_shared<Objective>(optKind, "");
                objective->addObjective(singleObj);
                temp.objectives.push_back(objective);
            }
        }
    }

    std::string smt2 = temp.dumpSMT2();
    if (!artifactDir.empty()) {
        writeArtifact(artifactDir, "emit.smt2", smt2);
        writeArtifact(artifactDir, "builder_status.txt", "ok");
    }
    if (rpt) rpt->plan_json = ldJson;
    bool ok = parseSmt2WithRepair(self, &smt2, ldJson, opt, rpt, artifactDir);
    if (ok && !temp.objectives.empty())
        self->objectives = temp.objectives;
    return ok;
}

// ---------- DirectTextual: legacy prompt -> SMT2 -> parse + optional repair ----------
static bool run_direct_textual(Parser* self, const std::string& nl, const smtlib::NL2SMTOptions& opt,
    smtlib::NL2SMTReport* rpt, const std::string& artifactDir) {
    std::string systemPrompt = "Output only valid SMT-LIB2. No markdown, no explanation.";
    std::string userPrompt = loadPrompt(opt.prompt_direct_path, DEFAULT_PROMPT_LEGACY);
    size_t pos = userPrompt.find("<<<USER_INPUT>>>");
    if (pos != std::string::npos) userPrompt.replace(pos, 16, nl);
    std::string smt2;
    std::string err;
    if (!callLLM(opt.endpoint, opt.path, opt.model, opt.temperature, systemPrompt, userPrompt, opt.timeout_sec, &smt2, &err)) {
        if (rpt) rpt->last_error = "Legacy LLM failed: " + err;
        return false;
    }
    smt2 = stripMarkdown(smt2);
    if (!artifactDir.empty()) writeArtifact(artifactDir, "emit.smt2", smt2);
    if (rpt) rpt->smt2 = smt2;
    return parseSmt2WithRepair(self, &smt2, "", opt, rpt, artifactDir);
}

static void writeArtifact(const std::string& dir, const std::string& name, const std::string& content) {
    if (dir.empty()) return;
    std::string path = (dir.back() == '/' || dir.back() == '\\') ? dir + name : dir + "/" + name;
    std::ofstream f(path);
    if (f) f << content;
}

static std::string loadPrompt(const std::string& path, const char* defaultPrompt) {
    if (path.empty()) return defaultPrompt;
    std::ifstream f(path);
    if (!f) return defaultPrompt;
    std::ostringstream os;
    os << f.rdbuf();
    return os.str();
}

} // anonymous namespace

// ---------- Parser::parseNL ----------
bool Parser::parseNL(const std::string& nl, const smtlib::NL2SMTOptions& opt, smtlib::NL2SMTReport* rpt) {
    if (rpt) { rpt->ok = false; rpt->repair_rounds = 0; rpt->plan_json.clear(); rpt->smt2.clear(); rpt->last_error.clear(); rpt->artifacts_dir_used.clear(); }
    if (nl.empty()) {
        if (rpt) rpt->last_error = "Empty NL input";
        return false;
    }
    std::string artifactDir = opt.artifact_dir;
    if (!artifactDir.empty() && artifactDir.back() != '/' && artifactDir.back() != '\\')
        artifactDir += '/';
    if (!artifactDir.empty())
        writeArtifact(artifactDir, "nl.txt", nl);

    switch (opt.strategy) {
    case smtlib::NLCompilationStrategy::Structured:
        return run_structured_pipeline(this, nl, opt, rpt, artifactDir);
    case smtlib::NLCompilationStrategy::DirectTextual:
        return run_direct_textual(this, nl, opt, rpt, artifactDir);
    }
    return false;
}

} // namespace SMTParser

#endif // SMTLIBPARSER_ENABLE_NL2SMT
