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

static std::string loadPrompt(const std::string& path);
static void writeArtifact(const std::string& dir, const std::string& name, const std::string& content);

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
static std::shared_ptr<Sort> sortFromPlan(const json& sortJson, Parser* p) {
    if (sortJson.is_string()) {
        std::string s = sortJson.get<std::string>();
        if (s == "Int") return SortManager::INT_SORT;
        if (s == "Real") return SortManager::REAL_SORT;
        if (s == "Bool") return SortManager::BOOL_SORT;
        if (s.size() > 7 && s.substr(0, 7) == "(BitVec ") return p->getSortManager()->createBVSort(static_cast<size_t>(std::stoull(s.substr(7))));
        return nullptr;
    }
    if (sortJson.is_object() && sortJson.contains("kind")) {
        std::string k = sortJson["kind"].get<std::string>();
        if (k == "Int") return SortManager::INT_SORT;
        if (k == "Real") return SortManager::REAL_SORT;
        if (k == "Bool") return SortManager::BOOL_SORT;
        if (k == "BV" && sortJson.contains("size")) return p->getSortManager()->createBVSort(sortJson["size"].get<size_t>());
    }
    return nullptr;
}

// Use kind.h getOperKind for op string -> NODE_KIND (single source of truth).

// Build const node from sort + value (op "const" with sort/value, or literal "const"). sort may be null to infer from value.
static std::shared_ptr<DAGNode> buildConst(Parser* p, const json& valueJson, std::shared_ptr<Sort> sort, const json* sortJson, std::string* outError) {
    if (sortJson && !sort) {
        sort = sortFromPlan(*sortJson, p);
        if (!sort) { if (outError) *outError = "Unsupported const sort"; return nullptr; }
    }
    if (valueJson.is_boolean())
        return valueJson.get<bool>() ? NodeManager::getTrue() : NodeManager::getFalse();
    if (valueJson.is_number_integer())
        return p->mkConstInt(valueJson.get<int>());
    if (valueJson.is_number_float())
        return p->mkConstReal(valueJson.get<double>());
    if (valueJson.is_string()) {
        std::string v = valueJson.get<std::string>();
        if (sort && sort->isBool())
            return (v == "true") ? NodeManager::getTrue() : NodeManager::getFalse();
        if (sort && sort->isInt()) {
            if (!TypeChecker::isInt(v)) {
                if (TypeChecker::isReal(v)) v = std::to_string(static_cast<long long>(std::stod(v)));
                else v = "0";
            }
            return p->mkConstInt(v);
        }
        if ((sort && sort->isReal()) || (!sort && TypeChecker::isReal(v)))
            return p->mkConstReal(v);
        if (!sort && TypeChecker::isInt(v))
            return p->mkConstInt(v);
    }
    if (outError) *outError = "Unsupported const value/sort";
    return nullptr;
}

// ---------- Build one Expr from plan JSON (var/const unified; ops via mkOper/mkApp, arity checked inside parser) ----------
static std::shared_ptr<DAGNode> buildExpr(Parser* p, const json& j,
    const std::unordered_map<std::string, std::shared_ptr<DAGNode>>& syms,
    std::string* outError) {
    if (j.is_null()) return nullptr;

    // Var: single form — name from "var" (string) or from "op":"var" + "name"
    std::string varName;
    if (j.contains("var") && j["var"].is_string())
        varName = j["var"].get<std::string>();
    else if (j.contains("op") && j["op"].get<std::string>() == "var" && j.contains("name"))
        varName = j["name"].get<std::string>();
    if (!varName.empty()) {
        auto it = syms.find(varName);
        if (it != syms.end()) return it->second;
        if (outError) *outError = "Unknown variable: " + varName;
        return nullptr;
    }

    // Const: literal j["const"] or op "const" / "bvconst"
    if (j.contains("const"))
        return buildConst(p, j["const"], nullptr, nullptr, outError);
    if (j.contains("op")) {
        std::string op = j["op"].get<std::string>();
        if (op == "const")
            return buildConst(p, j.contains("value") ? j["value"] : json(), nullptr, j.contains("sort") ? &j["sort"] : nullptr, outError);
        if (op == "bvconst") {
            if (!j.contains("size") || !j.contains("value")) { if (outError) *outError = "bvconst missing size/value"; return nullptr; }
            return p->mkConstBv(j["value"].get<std::string>(), j["size"].get<size_t>());
        }
    }

    // Ops: build args, then mkOper/mkEq/mkDistinct (parser checks arity)
    if (!j.contains("op")) { if (outError) *outError = "Unknown expr node"; return nullptr; }
    std::string op = j["op"].get<std::string>();
    std::vector<std::shared_ptr<DAGNode>> args;
    if (j.contains("args") && j["args"].is_array())
        for (const auto& a : j["args"]) {
            auto child = buildExpr(p, a, syms, outError);
            if (!child) return nullptr;
            args.push_back(child);
        }
    NODE_KIND kind = getOperKind(op);
    if (kind == NODE_KIND::NT_UNKNOWN) {
        if (outError) *outError = "Unsupported op: " + op;
        return nullptr;
    }
    std::shared_ptr<Sort> outSort = args.empty() ? SortManager::BOOL_SORT : args[0]->getSort();
    if (kind == NODE_KIND::NT_EQ) return p->mkEq(args);
    if (kind == NODE_KIND::NT_DISTINCT) return p->mkDistinct(args);
    if (kind == NODE_KIND::NT_LE || kind == NODE_KIND::NT_LT || kind == NODE_KIND::NT_GE || kind == NODE_KIND::NT_GT)
        outSort = SortManager::BOOL_SORT;
    else if (kind == NODE_KIND::NT_ADD || kind == NODE_KIND::NT_SUB || kind == NODE_KIND::NT_MUL)
        outSort = (outSort && (outSort->isInt() || outSort->isReal())) ? outSort : SortManager::INT_SORT;
    else if (kind == NODE_KIND::NT_DIV_INT) outSort = SortManager::INT_SORT;
    else if (kind == NODE_KIND::NT_DIV_REAL) outSort = SortManager::REAL_SORT;
    else if (kind == NODE_KIND::NT_NOT || kind == NODE_KIND::NT_ABS)
        outSort = args.empty() ? outSort : args[0]->getSort();
    else if (kind == NODE_KIND::NT_AND || kind == NODE_KIND::NT_OR || kind == NODE_KIND::NT_IMPLIES || kind == NODE_KIND::NT_XOR)
        outSort = SortManager::BOOL_SORT;
    else if (kind == NODE_KIND::NT_ITE)
        outSort = args.size() > 1 ? args[1]->getSort() : outSort;
    else if (kind >= NODE_KIND::NT_BV_ADD && kind <= NODE_KIND::NT_BV_SGE)
        outSort = args.empty() ? outSort : args[0]->getSort();
    return p->mkOper(outSort, kind, args);
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
        if (!sort) { if (lastError) *lastError = "Unsupported sort for symbol " + name; return false; }
        syms[name] = p->mkVar(sort, name);
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
    // Skeleton may contain var/num/compare when LD embeds full expressions (e.g. case 13)
    if (op == "var") {
        if (!syms || !skel.contains("name")) {
            if (outError) *outError = "var missing name or syms";
            return nullptr;
        }
        std::string name = skel["name"].get<std::string>();
        auto it = syms->find(name);
        if (it != syms->end()) return it->second;
        if (outError) *outError = "Unknown variable in skeleton: " + name;
        return nullptr;
    }
    if (op == "num") {
        if (!skel.contains("value")) {
            if (outError) *outError = "num missing value";
            return nullptr;
        }
        return buildConst(p, skel["value"], nullptr, nullptr, outError);
    }
    NODE_KIND compKind = getOperKind(op);
    if (compKind == NODE_KIND::NT_LE || compKind == NODE_KIND::NT_LT ||
        compKind == NODE_KIND::NT_GE || compKind == NODE_KIND::NT_GT) {
        if (args.size() != 2) {
            if (outError) *outError = "comparison requires 2 args (got " + std::to_string(args.size()) + ")";
            return nullptr;
        }
        return p->mkOper(SortManager::BOOL_SORT, compKind, args[0], args[1]);
    }
    if (compKind == NODE_KIND::NT_EQ) {
        if (args.size() < 2) {
            if (outError) *outError = "= requires 2 args";
            return nullptr;
        }
        return p->mkEq(args);
    }
    if (op == "add" || op == "sub" || op == "mul") {
        NODE_KIND arithKind = getOperKind(op);
        if (args.size() < 2) {
            if (outError) *outError = op + " requires at least 2 args";
            return nullptr;
        }
        std::shared_ptr<Sort> s = args[0]->getSort();
        if (!s || (!s->isInt() && !s->isReal())) s = SortManager::INT_SORT;
        return p->mkOper(s, arithKind, args);
    }
    // LD sometimes returns skeleton as {"op": "P1"} instead of "P1"; treat as proposition id
    if (op.size() >= 2 && (op[0] == 'P' || op[0] == 'p') && std::isdigit(static_cast<unsigned char>(op[1]))) {
        auto it = propNodes.find(op);
        if (it != propNodes.end()) return it->second;
        if (allPropNodes) {
            auto ait = allPropNodes->find(op);
            if (ait != allPropNodes->end() && ait->second->getSort() && ait->second->getSort()->isBool())
                return ait->second;
        }
        if (outError) *outError = "Unknown proposition id: " + op;
        return nullptr;
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
            std::string repairPrompt = loadPrompt(opt.prompt_repair_path);
            if (repairPrompt.empty()) { if (rpt) rpt->last_error = "prompt_repair_path not set or file not found"; return false; }
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

static bool objectiveTermValid(const std::shared_ptr<DAGNode>& n) {
    return n && n->getKind() != NODE_KIND::NT_ERROR && n->getKind() != NODE_KIND::NT_NULL && n->getSort();
}

// ---------- Structured pipeline: LD -> APT -> Builder -> dump SMT2 -> parse + optional repair ----------
static bool run_structured_pipeline(Parser* self, const std::string& nl, const smtlib::NL2SMTOptions& opt,
    smtlib::NL2SMTReport* rpt, const std::string& artifactDir) {
    std::string ldJson;
    std::string userPrompt = loadPrompt(opt.prompt_ld_path);
    if (userPrompt.empty()) { if (rpt) rpt->last_error = "prompt_ld_path not set or file not found"; return false; }
    std::string systemPrompt = "You output only valid JSON. No markdown, no explanation.";
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
        syms[name] = temp.mkVar(sort, name);
    }

    std::string aptPromptTemplate = loadPrompt(opt.prompt_apt_path);
    if (aptPromptTemplate.empty()) { if (rpt) rpt->last_error = "prompt_apt_path not set or file not found"; return false; }
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
        bool parsed = parseJsonStrict(aptOut, &exprJson, &err);
        std::string buildErr;
        std::shared_ptr<DAGNode> node = parsed ? buildExpr(&temp, exprJson, syms, &buildErr) : nullptr;
        if (!node) {
            callLLM(opt.endpoint, opt.path, opt.model, opt.temperature, "Output only valid JSON.", aptUser, opt.timeout_sec, &aptOut, &err);
            exprJson = json();
            parsed = parseJsonStrict(aptOut, &exprJson, &err);
            node = parsed ? buildExpr(&temp, exprJson, syms, &buildErr) : nullptr;
        }
        if (!node) continue;
        allPropNodes[pid] = node;
        if (node->getSort() && node->getSort()->isBool())
            propNodes[pid] = node;
    }

    std::string buildErr;
    auto mainConstraint = buildFromSkeleton(ld["skeleton"], propNodes, &allPropNodes, &syms, &temp, &buildErr);
    if (!mainConstraint) {
        std::string dbgLine;
        {
            std::string skelStr = ld["skeleton"].dump();
            if (skelStr.size() > 200) skelStr = skelStr.substr(0, 197) + "...";
            std::string ldKeys, propKeys, allKeys;
            if (ld.contains("propositions") && ld["propositions"].is_object())
                for (auto it = ld["propositions"].begin(); it != ld["propositions"].end(); ++it)
                    ldKeys += it.key() + " ";
            for (const auto& e : propNodes) propKeys += e.first + " ";
            for (const auto& e : allPropNodes) allKeys += e.first + " ";
            dbgLine = " [Structured debug] skeleton=" + skelStr + " ; LD_propositions=" + (ldKeys.empty() ? "none" : ldKeys)
                    + " ; propNodes=" + (propKeys.empty() ? "none" : propKeys) + " ; allPropNodes=" + (allKeys.empty() ? "none" : allKeys);
        }
        if (rpt) {
            rpt->last_error = "Builder failed: " + buildErr + dbgLine;
            rpt->debug_info = "skeleton=" + ld["skeleton"].dump();
        }
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

    bool objectiveInPlan = false;
    bool objectiveBuilt = false;
    if (ld.contains("objective") && ld["objective"].is_object()) {
        const auto& obj = ld["objective"];
        std::string sense = obj.contains("sense") ? obj["sense"].get<std::string>() : "none";
        if (sense != "none") {
            objectiveInPlan = true;
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
                if (!objectiveTermValid(termNode)) termNode = nullptr;
            }
            if (!termNode && obj.contains("term") && !obj["term"].is_null()) {
                termNode = buildExpr(&temp, obj["term"], syms, &buildErr);
                if (!objectiveTermValid(termNode)) termNode = nullptr;
            }
            if (!termNode && syms.size() == 1) {
                std::shared_ptr<DAGNode> single = syms.begin()->second;
                if (objectiveTermValid(single)) termNode = single;
            }
            if (termNode && objectiveTermValid(termNode)) {
                objectiveBuilt = true;
                OPT_KIND optKind = (sense == "max") ? OPT_KIND::OPT_MAXIMIZE : OPT_KIND::OPT_MINIMIZE;
                COMP_KIND comp = getDefaultCompareOperator(temp.getOptions()->logic, optKind);
                auto singleObj = std::make_shared<SingleObjective>(optKind, termNode, comp, NodeManager::NULL_NODE, NodeManager::NULL_NODE, "");
                auto objective = std::make_shared<Objective>(optKind, "");
                objective->addObjective(singleObj);
                temp.objectives.push_back(objective);
            }
        }
    }
    if (rpt && objectiveInPlan && !objectiveBuilt)
        rpt->debug_info = "Structured: objective in LD (min/max) but term not built";

    std::string smt2 = temp.dumpSMT2();
    if (!artifactDir.empty()) {
        writeArtifact(artifactDir, "emit.smt2", smt2);
        writeArtifact(artifactDir, "builder_status.txt", "ok");
    }
    if (rpt) rpt->plan_json = ldJson;
    bool ok = parseSmt2WithRepair(self, &smt2, ldJson, opt, rpt, artifactDir);
    // Use builder objectives only when parse did not produce any (parsed objectives use self's node manager and dump correctly)
    if (ok && !temp.objectives.empty() && self->objectives.empty())
        self->objectives = temp.objectives;
    return ok;
}

// Infer QF_LIA / QF_LRA / QF_LIRA from declared variable sorts when logic is UNKNOWN_LOGIC.
static void inferLogicFromDeclared(Parser* self) {
    if (!self || !self->getOptions()) return;
    if (self->getOptions()->getLogic() != "UNKNOWN_LOGIC") return;
    std::vector<std::shared_ptr<DAGNode>> vars = self->getDeclaredVariables();
    bool hasInt = false, hasReal = false;
    for (const auto& v : vars) {
        if (!v || !v->getSort()) continue;
        if (v->getSort()->isInt()) hasInt = true;
        else if (v->getSort()->isReal()) hasReal = true;
    }
    if (hasInt && hasReal) self->getOptions()->setLogic("QF_LIRA");
    else if (hasReal) self->getOptions()->setLogic("QF_LRA");
    else if (hasInt) self->getOptions()->setLogic("QF_LIA");
}

// ---------- DirectTextual: legacy prompt -> SMT2 -> parse + optional repair ----------
static bool run_direct_textual(Parser* self, const std::string& nl, const smtlib::NL2SMTOptions& opt,
    smtlib::NL2SMTReport* rpt, const std::string& artifactDir) {
    std::string userPrompt = loadPrompt(opt.prompt_direct_path);
    if (userPrompt.empty()) { if (rpt) rpt->last_error = "prompt_direct_path not set or file not found"; return false; }
    std::string systemPrompt = "Output only valid SMT-LIB2. No markdown, no explanation.";
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
    bool ok = parseSmt2WithRepair(self, &smt2, "", opt, rpt, artifactDir);
    if (ok) inferLogicFromDeclared(self);
    return ok;
}

static void writeArtifact(const std::string& dir, const std::string& name, const std::string& content) {
    if (dir.empty()) return;
    std::string path = (dir.back() == '/' || dir.back() == '\\') ? dir + name : dir + "/" + name;
    std::ofstream f(path);
    if (f) f << content;
}

static std::string loadPrompt(const std::string& path) {
    if (path.empty()) return "";
    std::ifstream f(path);
    if (!f) return "";
    std::ostringstream os;
    os << f.rdbuf();
    return os.str();
}

} // anonymous namespace

// ---------- Parser::parseNL ----------
bool Parser::parseNL(const std::string& nl, const smtlib::NL2SMTOptions& opt, smtlib::NL2SMTReport* rpt) {
    if (rpt) { rpt->ok = false; rpt->repair_rounds = 0; rpt->plan_json.clear(); rpt->smt2.clear(); rpt->last_error.clear(); rpt->artifacts_dir_used.clear(); rpt->debug_info.clear(); }
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
