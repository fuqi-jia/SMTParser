# NL2SMT：自然语言 → Prompt + 大模型 → SMT

NL2SMT 是 SMTParser 的**自然语言前端**：**Prompt + 调用大模型** 得到 SMT-LIB2 文本，再用**现有 parser 直接解析**，得到 DAG（assertions/objectives）。

- **不重复造轮子**：type 就是 parser 的 **Sort**（declare-fun 的 sort）；表达式、理论全部用 parser 已支持的 SMT-LIB2，不另做一套 type 或 atom parser，也不局限在算术理论。
- **不做**手写字符串/关键词切分，完全依赖 LLM 生成标准 SMT-LIB2。

---

## 1. 流程

```
自然语言输入
  → 拼装 Prompt（系统提示词 + 用户输入）
  → 调用 LLM（外部命令或 HTTP）
  → 模型输出 SMT-LIB2 文本
  → 写入临时文件 → parser->parse(文件)
  → assertions / objectives 进入 parser，可 dumpSMT2() / toString()
```

- **Prompt**：见 `prompt.txt`。要求模型只输出合法 SMT-LIB2，且**与 parser 能力一致**：用标准 Sort（Int/Real/Bool/BV/FP/String/Array 等），用 parser 支持的各理论（LIA/LRA/BV/FP/S/A 等），不发明额外 type 或表达式语法。
- **LLM 调用**：由 `llm_caller` 执行配置好的命令（如 `python llm_call.py <输入文件>`），读取 stdout 作为 SMT-LIB2。
- **解析**：对模型输出去 markdown 后写临时 `.smt2`，用 `parser->parse(path)` 得到 DAG。

---

## 2. 目录与文件（apps 内，与 src 隔离）

```
apps/nl2smt/
  prompt.txt              # 系统提示词：自然语言 → 只输出 SMT-LIB2
  llm_call.py             # 调用 OpenAI 兼容 API，读输入文件，打印 SMT-LIB2 到 stdout
  mock_llm.sh             # 测试用：不调 API，直接打印固定 SMT-LIB2
  llm_caller.h /.cpp      # C++：执行配置命令，读 stdout，返回字符串
  nl2smt.h /.cpp          # NL2SMTCompiler：callLLM → 临时文件 → parser->parse
  demo_nl2smt.cpp         # Demo
  test_nl2smt.cpp         # 单元测试（默认用 mock_llm.sh，无需 API key）
```

---

## 3. 环境与配置

**必须二选一**：

- **NL2SMT_LLM_SCRIPT**：`llm_call.py` 的完整路径，例如  
  `export NL2SMT_LLM_SCRIPT=/path/to/apps/nl2smt/llm_call.py`  
  内部会执行：`python "$NL2SMT_LLM_SCRIPT" <临时输入文件>`
- **NL2SMT_LLM_CMD**：完整命令（会再追加一个参数：临时输入文件路径）。  
  例如：`export NL2SMT_LLM_CMD="sh /path/to/apps/nl2smt/mock_llm.sh"`（测试用）

**LLM 脚本/API（以 llm_call.py 为例）**：

- **OPENAI_API_KEY**：API key（OpenAI 或兼容服务）。
- **OPENAI_API_BASE**：可选，兼容接口 base URL（如本地/代理）。
- **NL2SMT_MODEL**：模型名，默认 `gpt-4o-mini`。
- **NL2SMT_PROMPT_FILE**：可选，覆盖默认的 `prompt.txt` 路径。

安装 Python 依赖（任选其一）：

```bash
pip install openai
# 或
pip install requests
```

---

## 4. 使用

```bash
# 编译（BUILD_NL2SMT=ON）
cmake -DBUILD_NL2SMT=ON .. && make

# 使用前设置 LLM（二选一）
export NL2SMT_LLM_SCRIPT=/path/to/SMTParser/apps/nl2smt/llm_call.py
export OPENAI_API_KEY=sk-...

# CLI
./smtparser --nl "x is integer and x > 0, minimize x"
./smtparser --nl input.txt

# Demo
./demo_nl2smt "x is int, y is int, x + y < 5"

# 测试（无需 API：用 mock）
./test_nl2smt
```

---

## 5. Prompt 与模型行为

- `prompt.txt` 规定：只输出 SMT-LIB2，不要解释、不要 markdown 代码块。
- 若模型仍输出 markdown，`llm_caller` 会去掉首尾 \`\`\` 再交给 parser。
- 若 parser 报错，`compile()` 返回 false，`report()` 中会提示“解析 LLM 输出失败”，需检查模型是否严格按 SMT-LIB2 输出。

---

## 6. CMake

- `option(BUILD_NL2SMT "Build NL2SMT frontend (in apps)" OFF)`  
- **ON**：编译 `llm_caller.cpp`、`nl2smt.cpp`，并链接进可执行文件 `smtparser`、`demo_nl2smt`、`test_nl2smt`；不编入核心库。
- **OFF**：不编译 nl2smt 相关目标。

---

## 7. 小结

- **Type = Sort**：不另做 type 系统，parser 的 Sort（declare-fun 的 sort）就是类型。
- **不重复实现表达式/理论**：不写 atom parser 或只支持算术的小前端；parser 已支持 Core/LIA/LRA/BV/FP/String/Array 等，LLM 只负责生成符合这些理论的 SMT-LIB2，由 parser 统一解析。
- NL2SMT = **Prompt + LLM 调用 + parser->parse**，实现全在 **apps/nl2smt/**，与 **src** 隔离；结果通过现有 `dumpSMT2()` / `toString()` 输出。
