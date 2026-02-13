#!/usr/bin/env python3
"""
NL2SMT LLM caller: reads natural language from file, calls OpenAI-compatible API,
prints SMT-LIB2 to stdout. Use from C++ nl2smt (e.g. popen) or standalone.

Usage:
  python llm_call.py <input_file>   # input_file contains the user's natural language
  echo "x is int and x > 0, minimize x" | python llm_call.py -

Env:
  OPENAI_API_KEY       - API key (required for OpenAI)
  OPENAI_API_BASE      - Optional base URL (e.g. for local/server: http://localhost:8080/v1)
  NL2SMT_MODEL         - Model name (default: gpt-4o-mini)
  NL2SMT_PROMPT_FILE   - Optional path to system prompt file (default: prompt.txt next to script)
"""

import os
import sys

def load_prompt(prompt_path: str) -> str:
    if os.path.isfile(prompt_path):
        with open(prompt_path, "r", encoding="utf-8") as f:
            return f.read().strip()
    return (
        "You are a converter from natural language to SMT-LIB2. "
        "Given the user's description, output ONLY valid SMT-LIB2: set-logic, declare-fun, assert, minimize/maximize, check-sat, exit. No other text."
    )

def main():
    if len(sys.argv) < 2:
        print("Usage: llm_call.py <input_file|->", file=sys.stderr)
        sys.exit(1)
    inp = sys.argv[1]
    if inp == "-":
        user_text = sys.stdin.read().strip()
    else:
        with open(inp, "r", encoding="utf-8") as f:
            user_text = f.read().strip()
    if not user_text:
        print("Empty input.", file=sys.stderr)
        sys.exit(1)

    script_dir = os.path.dirname(os.path.abspath(__file__))
    prompt_path = os.environ.get("NL2SMT_PROMPT_FILE") or os.path.join(script_dir, "prompt.txt")
    system_prompt = load_prompt(prompt_path)
    model = os.environ.get("NL2SMT_MODEL", "gpt-4o-mini")
    api_key = os.environ.get("OPENAI_API_KEY", "")
    api_base = os.environ.get("OPENAI_API_BASE", "")

    try:
        import openai
    except ImportError:
        try:
            import requests
        except ImportError:
            print("Need openai or requests. Install: pip install openai", file=sys.stderr)
            sys.exit(1)
        # Fallback: raw HTTP
        url = (api_base.rstrip("/") + "/chat/completions") if api_base else "https://api.openai.com/v1/chat/completions"
        headers = {"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"}
        payload = {
            "model": model,
            "messages": [
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_text},
            ],
            "temperature": 0.1,
        }
        r = requests.post(url, json=payload, headers=headers, timeout=60)
        r.raise_for_status()
        out = r.json()["choices"][0]["message"]["content"].strip()
    else:
        client_kw = {}
        if api_base:
            client_kw["base_url"] = api_base
        client = openai.OpenAI(api_key=api_key or None, **client_kw)
        resp = client.chat.completions.create(
            model=model,
            messages=[
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_text},
            ],
            temperature=0.1,
        )
        out = (resp.choices[0].message.content or "").strip()

    # Strip markdown code block if present
    if out.startswith("```"):
        lines = out.split("\n")
        if lines[0].startswith("```"):
            lines = lines[1:]
        if lines and lines[-1].strip() == "```":
            lines = lines[:-1]
        out = "\n".join(lines)
    print(out)

if __name__ == "__main__":
    main()
