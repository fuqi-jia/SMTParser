#!/usr/bin/env bash
# Start LiteLLM proxy for NL2SMT. Reads port and model from .config/llm.conf if present.
# Usage: ./llm.sh [port] [model]
#   If no args: use .config/llm.conf (endpoint → port, model); default port 4000, model openai/gpt-4o-mini.
#   If port/model missing or config missing: use defaults above.

set -e
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CONFIG="$REPO_ROOT/.config/llm.conf"
PORT=4000
MODEL="openai/gpt-4o-mini"

if [[ -f "$CONFIG" ]]; then
  # endpoint = http://127.0.0.1:4000  -> 4000
  p=$(grep -E '^[[:space:]]*endpoint[[:space:]]*=' "$CONFIG" 2>/dev/null | sed -n 's/.*:\([0-9][0-9]*\).*/\1/p' | head -1)
  [[ -n "$p" ]] && PORT="$p"
  # model = openrouter/deepseek/...
  m=$(grep -E '^[[:space:]]*model[[:space:]]*=' "$CONFIG" 2>/dev/null | sed 's/^[^=]*=[[:space:]]*//;s/[[:space:]]*$//' | head -1)
  [[ -n "$m" ]] && MODEL="$m"
fi
[[ -n "$1" ]] && PORT="$1"
[[ -n "$2" ]] && MODEL="$2"

# OpenRouter models need OPENROUTER_API_KEY; use api_key from .config/llm.conf if set and env not set
if [[ "$MODEL" == openrouter/* ]]; then
  if [[ -z "${OPENROUTER_API_KEY:-}" ]] && [[ -f "$CONFIG" ]]; then
    key=$(grep -E '^[[:space:]]*api_key[[:space:]]*=' "$CONFIG" 2>/dev/null | sed 's/^[^=]*=[[:space:]]*//;s/[[:space:]]*$//' | head -1)
    if [[ -n "$key" ]]; then
      export OPENROUTER_API_KEY="$key"
    fi
  fi
  if [[ -z "${OPENROUTER_API_KEY:-}" ]]; then
    echo "OpenRouter model ($MODEL) requires OPENROUTER_API_KEY. Set it in .config/llm.conf (api_key = ...) or: export OPENROUTER_API_KEY=sk-or-..."
    exit 1
  fi
fi

if ! command -v litellm >/dev/null 2>&1; then
  echo "LiteLLM not found. Install with:"
  echo "  pip install \"litellm[proxy]\" python-multipart"
  echo "Then run ./llm.sh again."
  exit 1
fi
if ! python3 -c "import multipart" 2>/dev/null; then
  echo "python-multipart not found (required by LiteLLM proxy). Install with:"
  echo "  pip install python-multipart"
  echo "Or install all deps: pip install \"litellm[proxy]\" python-multipart"
  echo "Then run ./llm.sh again."
  exit 1
fi

echo "Starting LiteLLM proxy: port=$PORT model=$MODEL"
echo "NL2SMT config should use endpoint=http://127.0.0.1:$PORT (see .config/llm.conf)"
echo "Press Ctrl+C to stop."
exec litellm --port "$PORT" --model "$MODEL"
