#!/usr/bin/env python3
"""
NL2SMT LLM caller: Tree-Plan → Emit → Repair three-phase, or legacy single-shot.
LiteLLM-only version (recommended): unified config, no 'export' needed.

Usage:
  # Three-phase (Tree-Plan → Emit → Repair)
  python llm_call.py plan <nl_file>              # NL → JSON plan (stdout)
  python llm_call.py emit <plan_file>            # Plan JSON → SMT-LIB2 (stdout)
  python llm_call.py repair <err_file> <plan_file> <smt_file>  # Fix SMT (stdout)

  # Legacy: single file = NL → SMT-LIB2 (uses prompt.txt)
  python llm_call.py <input_file>
  echo "x is int and x > 0, minimize x" | python llm_call.py -

Config (INI):
  Default search order:
    1) --config PATH
    2) env NL2SMT_CONFIG
    3) <script_dir>/llm.conf

INI format:
  [nl2smt]
  provider = openai
  model = openai/gpt-4o-mini
  api_key = ...
  api_base =
  use_responses = false
  reasoning_effort = medium
  temperature = 0.0
  timeout_sec = 90
  max_retries = 2
  debug = false

Prompt paths:
  single-shot uses only NL2SMT_PROMPT_FILE (default: prompt.txt).
  three-phase uses only NL2SMT_PROMPT_PLAN / _EMIT / _REPAIR (default: script dir).
"""

from __future__ import annotations

import os
import sys
import time
import configparser
from typing import Optional, Dict, Any

# LiteLLM is the only dependency for LLM calls.
try:
    from litellm import completion, responses
except Exception as e:
    print("ERROR: LiteLLM is required. Install: pip install litellm", file=sys.stderr)
    print(f"Import error: {e}", file=sys.stderr)
    sys.exit(1)


# ----------------------------
# config / utils
# ----------------------------

def _str2bool(s: str, default: bool = False) -> bool:
    if s is None:
        return default
    v = s.strip().lower()
    if v in ("1", "true", "yes", "y", "on"):
        return True
    if v in ("0", "false", "no", "n", "off"):
        return False
    return default


def locate_config_path(argv: list[str], script_dir: str) -> Optional[str]:
    # --config PATH
    if "--config" in argv:
        i = argv.index("--config")
        if i + 1 >= len(argv):
            print("ERROR: --config requires a path", file=sys.stderr)
            sys.exit(1)
        return argv[i + 1]

    # env NL2SMT_CONFIG
    p = os.environ.get("NL2SMT_CONFIG", "").strip()
    if p:
        return p

    # default <script_dir>/llm.conf, or <script_dir>/../config/llm.conf (prompts in apps/config/prompts/)
    for candidate in (
        os.path.join(script_dir, "llm.conf"),
        os.path.normpath(os.path.join(script_dir, "..", "config", "llm.conf")),
    ):
        if os.path.isfile(candidate):
            return candidate
    return None


def load_ini_config(path: Optional[str]) -> Dict[str, str]:
    cfg: Dict[str, str] = {}
    if not path:
        return cfg
    if not os.path.isfile(path):
        print(f"ERROR: config file not found: {path}", file=sys.stderr)
        sys.exit(1)

    parser = configparser.ConfigParser()
    parser.read(path, encoding="utf-8")

    if "nl2smt" not in parser:
        print(f"ERROR: missing [nl2smt] section in config: {path}", file=sys.stderr)
        sys.exit(1)

    sec = parser["nl2smt"]
    for k in sec:
        cfg[k.strip()] = sec.get(k, fallback="").strip()
    return cfg


def load_text_file(path: str) -> str:
    with open(path, "r", encoding="utf-8") as f:
        return f.read()


def load_prompt(prompt_path: str, fallback: str = "") -> str:
    if os.path.isfile(prompt_path):
        return load_text_file(prompt_path).strip()
    return fallback


def strip_markdown_code_block(s: str) -> str:
    s = (s or "").strip()
    if s.startswith("```"):
        lines = s.split("\n")
        # remove first fence
        if lines and lines[0].startswith("```"):
            lines = lines[1:]
        # remove last fence
        if lines and lines[-1].strip() == "```":
            lines = lines[:-1]
        s = "\n".join(lines)
    return s.strip()


def read_input_maybe_stdin(path: str) -> str:
    if path == "-":
        return sys.stdin.read().strip()
    return load_text_file(path).strip()


def _debug_print(debug: bool, msg: str) -> None:
    if debug:
        print(f"[nl2smt][llm_call] {msg}", file=sys.stderr)


# ----------------------------
# LiteLLM call
# ----------------------------

def call_llm_litellm(
    cfg: Dict[str, str],
    system_prompt: str,
    user_content: str,
) -> str:
    """
    LiteLLM-only caller with unified config, no env exports required.
    - Uses completion() by default
    - Uses responses() when use_responses=true
    - Retries on transient errors (simple backoff)
    """
    model = cfg.get("model", "") or "openai/gpt-4o-mini"
    api_key = cfg.get("api_key", "")
    api_base = cfg.get("api_base", "")
    use_responses = _str2bool(cfg.get("use_responses", ""), False)
    reasoning_effort = cfg.get("reasoning_effort", "") or "medium"
    temperature = float(cfg.get("temperature", "0.0") or "0.0")
    timeout_sec = float(cfg.get("timeout_sec", "90") or "90")
    max_retries = int(cfg.get("max_retries", "2") or "2")
    debug = _str2bool(cfg.get("debug", ""), False)

    if not model:
        raise RuntimeError("Missing model in config [nl2smt].model")
    # api_key may be optional for local proxy; keep it optional.

    messages = [
        {"role": "system", "content": system_prompt},
        {"role": "user", "content": user_content},
    ]

    kwargs: Dict[str, Any] = {
        "model": model,
        "messages": messages,
        "temperature": temperature,
        "timeout": timeout_sec,
    }
    # LiteLLM supports passing api_key/api_base directly (recommended: avoid global env).
    if api_key:
        kwargs["api_key"] = api_key
    if api_base:
        kwargs["api_base"] = api_base

    last_err: Optional[Exception] = None
    for attempt in range(max_retries + 1):
        try:
            if use_responses:
                _debug_print(debug, f"responses(model={model}, api_base={api_base or 'default'})")
                resp = responses(
                    **kwargs,
                    reasoning_effort=reasoning_effort,
                )
                out = (resp.choices[0].message.content or "").strip()
                return out
            else:
                _debug_print(debug, f"completion(model={model}, api_base={api_base or 'default'})")
                resp = completion(**kwargs)
                out = (resp.choices[0].message.content or "").strip()
                return out
        except Exception as e:
            last_err = e
            if attempt >= max_retries:
                break
            # simple exponential-ish backoff
            sleep_s = min(2.0 ** attempt, 8.0)
            _debug_print(debug, f"call failed (attempt {attempt+1}/{max_retries+1}): {e} ; retry in {sleep_s}s")
            time.sleep(sleep_s)

    raise RuntimeError(f"LLM call failed after {max_retries+1} attempts: {last_err}")


# ----------------------------
# phase runners
# ----------------------------

def _default_prompts_dir(script_dir: str) -> str:
    return os.path.normpath(os.path.join(script_dir, "..", "config", "prompts"))


def run_plan(script_dir: str, cfg: Dict[str, str], nl_content: str) -> str:
    prompt_path = os.environ.get("NL2SMT_PROMPT_PLAN") or os.path.join(_default_prompts_dir(script_dir), "prompt_plan.txt")
    system = load_prompt(prompt_path, "Output only valid JSON constraint plan. No explanations, no markdown.")
    # Prefer: NL in USER content, not system. Keep system as rules-only.
    user_content = nl_content
    out = call_llm_litellm(cfg, system, user_content)
    return strip_markdown_code_block(out)


def run_emit(script_dir: str, cfg: Dict[str, str], plan_json: str) -> str:
    prompt_path = os.environ.get("NL2SMT_PROMPT_EMIT") or os.path.join(_default_prompts_dir(script_dir), "prompt_emit.txt")
    system = load_prompt(prompt_path, "Generate only valid SMT-LIB2 from the given JSON plan. No explanations, no markdown.")
    user_content = plan_json
    out = call_llm_litellm(cfg, system, user_content)
    return strip_markdown_code_block(out)


def run_repair(script_dir: str, cfg: Dict[str, str], error_message: str, plan_json: str, previous_smt: str) -> str:
    prompt_path = os.environ.get("NL2SMT_PROMPT_REPAIR") or os.path.join(_default_prompts_dir(script_dir), "prompt_repair.txt")
    system = load_prompt(prompt_path, "Fix the SMT-LIB2. Output only corrected SMT-LIB2. No explanations, no markdown.")
    # Put all context in USER content; keep system as rules.
    user_content = (
        "PARSER_ERROR:\n" + error_message.strip() +
        "\n\nPLAN_JSON:\n" + plan_json.strip() +
        "\n\nPREVIOUS_SMT:\n" + previous_smt.strip()
    )
    out = call_llm_litellm(cfg, system, user_content)
    return strip_markdown_code_block(out)


def run_legacy(script_dir: str, cfg: Dict[str, str], nl_text: str) -> str:
    prompt_path = os.environ.get("NL2SMT_PROMPT_FILE") or os.path.join(_default_prompts_dir(script_dir), "prompt.txt")
    system = load_prompt(prompt_path, "You are a converter from natural language to SMT-LIB2. Output ONLY valid SMT-LIB2. No other text.")
    user_content = nl_text
    out = call_llm_litellm(cfg, system, user_content)
    return strip_markdown_code_block(out)


# ----------------------------
# main
# ----------------------------

def main() -> None:
    argv = sys.argv[1:]
    if not argv:
        print("Usage: llm_call.py [--config PATH] [plan|emit|repair] <file(s)> | llm_call.py [--config PATH] <nl_file|->",
              file=sys.stderr)
        sys.exit(1)

    # remove --config from argv for mode parsing, but still locate it
    script_dir = os.path.dirname(os.path.abspath(__file__))
    config_path = locate_config_path(sys.argv, script_dir)
    cfg = load_ini_config(config_path)

    # Resolve relative prompt paths from config and set env so run_* find them
    if config_path:
        config_dir = os.path.dirname(os.path.abspath(config_path))
        prompt_keys = [
            ("prompt_file", "NL2SMT_PROMPT_FILE"),
            ("prompt_plan", "NL2SMT_PROMPT_PLAN"),
            ("prompt_emit", "NL2SMT_PROMPT_EMIT"),
            ("prompt_repair", "NL2SMT_PROMPT_REPAIR"),
        ]
        for cfg_key, env_key in prompt_keys:
            val = cfg.get(cfg_key, "").strip()
            if val and not os.path.isabs(val):
                val = os.path.normpath(os.path.join(config_dir, val))
            if val:
                os.environ[env_key] = val

    # strip --config PATH from argv
    if "--config" in argv:
        i = argv.index("--config")
        argv = argv[:i] + argv[i+2:]

    mode = argv[0].lower()

    if mode == "plan":
        if len(argv) < 2:
            print("Usage: llm_call.py [--config PATH] plan <nl_file|->", file=sys.stderr)
            sys.exit(1)
        nl_content = read_input_maybe_stdin(argv[1])
        if not nl_content:
            print("Empty input.", file=sys.stderr)
            sys.exit(1)
        print(run_plan(script_dir, cfg, nl_content))
        return

    if mode == "emit":
        if len(argv) < 2:
            print("Usage: llm_call.py [--config PATH] emit <plan_file>", file=sys.stderr)
            sys.exit(1)
        plan_json = read_input_maybe_stdin(argv[1])
        if not plan_json:
            print("Empty plan.", file=sys.stderr)
            sys.exit(1)
        print(run_emit(script_dir, cfg, plan_json))
        return

    if mode == "repair":
        if len(argv) < 4:
            print("Usage: llm_call.py [--config PATH] repair <err_file> <plan_file> <smt_file>", file=sys.stderr)
            sys.exit(1)
        error_message = read_input_maybe_stdin(argv[1])
        plan_json = read_input_maybe_stdin(argv[2])
        previous_smt = read_input_maybe_stdin(argv[3])
        print(run_repair(script_dir, cfg, error_message, plan_json, previous_smt))
        return

    # Legacy mode: single argument is NL file (or -)
    nl_text = read_input_maybe_stdin(argv[0])
    if not nl_text:
        print("Empty input.", file=sys.stderr)
        sys.exit(1)
    print(run_legacy(script_dir, cfg, nl_text))


if __name__ == "__main__":
    main()
