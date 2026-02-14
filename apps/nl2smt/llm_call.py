#!/usr/bin/env python3
"""
NL2SMT LLM caller: Tree-Plan → Emit → Repair three-phase, or legacy single-shot.
Uses LiteLLM when installed (pip install litellm), else OpenAI SDK or requests. See LITELLM.md.

Usage:
  # Three-phase (Tree-Plan → Emit → Repair)
  python llm_call.py plan <nl_file>              # NL → JSON plan (stdout)
  python llm_call.py emit <plan_file>            # Plan JSON → SMT-LIB2 (stdout)
  python llm_call.py repair <err_file> <plan_file> <smt_file>  # Fix SMT (stdout)

  # Legacy: single file = NL → SMT-LIB2 (uses prompt.txt)
  python llm_call.py <input_file>
  echo "x is int and x > 0, minimize x" | python llm_call.py -

Env:
  OPENAI_API_KEY       - API key (required for OpenAI)
  OPENAI_API_BASE      - Optional base URL
  NL2SMT_MODEL         - Model name (default: gpt-4o-mini)
  Prompt paths (see README §2): single-shot uses only NL2SMT_PROMPT_FILE;
  three-phase uses only NL2SMT_PROMPT_PLAN / _EMIT / _REPAIR (default: script dir).
  NL2SMT_PROMPT_FILE   - Legacy (default: prompt.txt)
  NL2SMT_PROMPT_PLAN   - Plan (default: prompt_plan.txt)
  NL2SMT_PROMPT_EMIT   - Emit (default: prompt_emit.txt)
  NL2SMT_PROMPT_REPAIR - Repair (default: prompt_repair.txt)
"""

import os
import sys


def load_prompt(prompt_path: str, fallback: str = "") -> str:
    if os.path.isfile(prompt_path):
        with open(prompt_path, "r", encoding="utf-8") as f:
            return f.read().strip()
    return fallback


def call_llm(system_prompt: str, user_content: str) -> str:
    """Call LLM; prefer LiteLLM if installed, else OpenAI SDK, else requests. Returns assistant content (stripped)."""
    model = os.environ.get("NL2SMT_MODEL", "gpt-4o-mini")
    messages = [
        {"role": "system", "content": system_prompt},
        {"role": "user", "content": user_content},
    ]
    temperature = 0.1

    # Prefer LiteLLM when available (multi-model, proxy-friendly)
    try:
        import litellm
        response = litellm.completion(
            model=model,
            messages=messages,
            temperature=temperature,
        )
        return (response.choices[0].message.content or "").strip()
    except ImportError:
        pass
    except Exception as e:
        print(f"LiteLLM call failed: {e}", file=sys.stderr)
        raise

    api_key = os.environ.get("OPENAI_API_KEY", "")
    api_base = os.environ.get("OPENAI_API_BASE", "")

    try:
        import openai
    except ImportError:
        try:
            import requests
        except ImportError:
            print("Need litellm, openai, or requests. Install: pip install litellm", file=sys.stderr)
            sys.exit(1)
        url = (api_base.rstrip("/") + "/chat/completions") if api_base else "https://api.openai.com/v1/chat/completions"
        headers = {"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"}
        payload = {
            "model": model,
            "messages": messages,
            "temperature": temperature,
        }
        r = requests.post(url, json=payload, headers=headers, timeout=90)
        r.raise_for_status()
        out = r.json()["choices"][0]["message"]["content"].strip()
    else:
        client_kw = {}
        if api_base:
            client_kw["base_url"] = api_base
        client = openai.OpenAI(api_key=api_key or None, **client_kw)
        resp = client.chat.completions.create(
            model=model,
            messages=messages,
            temperature=temperature,
        )
        out = (resp.choices[0].message.content or "").strip()
    return out


def strip_markdown_code_block(s: str) -> str:
    s = s.strip()
    if s.startswith("```"):
        lines = s.split("\n")
        if lines[0].startswith("```"):
            lines = lines[1:]
        if lines and lines[-1].strip() == "```":
            lines = lines[:-1]
        s = "\n".join(lines)
    return s.strip()


def run_plan(script_dir: str, nl_content: str) -> str:
    prompt_path = os.environ.get("NL2SMT_PROMPT_PLAN") or os.path.join(script_dir, "prompt_plan.txt")
    system = load_prompt(
        prompt_path,
        "Output only valid JSON constraint plan. No explanations, no markdown."
    )
    system = system.replace("<<<USER_INPUT>>>", nl_content)
    user_content = "Translate the above natural language into a constraint plan (JSON only)."
    out = call_llm(system, user_content)
    return strip_markdown_code_block(out)


def run_emit(script_dir: str, plan_json: str) -> str:
    prompt_path = os.environ.get("NL2SMT_PROMPT_EMIT") or os.path.join(script_dir, "prompt_emit.txt")
    system = load_prompt(
        prompt_path,
        "Generate only valid SMT-LIB2 from the given JSON plan. No explanations, no markdown."
    )
    system = system.replace("<<<PLAN_JSON>>>", plan_json)
    user_content = plan_json
    out = call_llm(system, user_content)
    return strip_markdown_code_block(out)


def run_repair(script_dir: str, error_message: str, plan_json: str, previous_smt: str) -> str:
    prompt_path = os.environ.get("NL2SMT_PROMPT_REPAIR") or os.path.join(script_dir, "prompt_repair.txt")
    system = load_prompt(
        prompt_path,
        "Fix the SMT-LIB2. Output only corrected SMT-LIB2. No explanations, no markdown."
    )
    system = system.replace("<<<ERROR_MESSAGE>>>", error_message)
    system = system.replace("<<<PLAN_JSON>>>", plan_json)
    system = system.replace("<<<PREVIOUS_SMT>>>", previous_smt)
    user_content = f"Error:\n{error_message}\n\nPrevious SMT-LIB2:\n{previous_smt}"
    out = call_llm(system, user_content)
    return strip_markdown_code_block(out)


def main():
    if len(sys.argv) < 2:
        print("Usage: llm_call.py [plan|emit|repair] <file(s)> | llm_call.py <nl_file|->", file=sys.stderr)
        sys.exit(1)

    script_dir = os.path.dirname(os.path.abspath(__file__))
    mode = sys.argv[1].lower()

    if mode == "plan":
        if len(sys.argv) < 3:
            print("Usage: llm_call.py plan <nl_file>", file=sys.stderr)
            sys.exit(1)
        path = sys.argv[2]
        if path == "-":
            nl_content = sys.stdin.read().strip()
        else:
            with open(path, "r", encoding="utf-8") as f:
                nl_content = f.read().strip()
        if not nl_content:
            print("Empty input.", file=sys.stderr)
            sys.exit(1)
        out = run_plan(script_dir, nl_content)
        print(out)
        return

    if mode == "emit":
        if len(sys.argv) < 3:
            print("Usage: llm_call.py emit <plan_file>", file=sys.stderr)
            sys.exit(1)
        with open(sys.argv[2], "r", encoding="utf-8") as f:
            plan_json = f.read().strip()
        if not plan_json:
            print("Empty plan.", file=sys.stderr)
            sys.exit(1)
        out = run_emit(script_dir, plan_json)
        print(out)
        return

    if mode == "repair":
        if len(sys.argv) < 5:
            print("Usage: llm_call.py repair <err_file> <plan_file> <smt_file>", file=sys.stderr)
            sys.exit(1)
        with open(sys.argv[2], "r", encoding="utf-8") as f:
            error_message = f.read().strip()
        with open(sys.argv[3], "r", encoding="utf-8") as f:
            plan_json = f.read().strip()
        with open(sys.argv[4], "r", encoding="utf-8") as f:
            previous_smt = f.read().strip()
        out = run_repair(script_dir, error_message, plan_json, previous_smt)
        print(out)
        return

    # Legacy: single argument = NL file (or - for stdin) → SMT-LIB2
    inp = sys.argv[1]
    if inp == "-":
        user_text = sys.stdin.read().strip()
    else:
        with open(inp, "r", encoding="utf-8") as f:
            user_text = f.read().strip()
    if not user_text:
        print("Empty input.", file=sys.stderr)
        sys.exit(1)

    prompt_path = os.environ.get("NL2SMT_PROMPT_FILE") or os.path.join(script_dir, "prompt.txt")
    system_prompt = load_prompt(
        prompt_path,
        "You are a converter from natural language to SMT-LIB2. Output ONLY valid SMT-LIB2. No other text."
    )
    out = call_llm(system_prompt, user_text)
    print(strip_markdown_code_block(out))


if __name__ == "__main__":
    main()
