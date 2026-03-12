#!/usr/bin/env bash
set -euo pipefail

sudo apt-get update
sudo apt-get install -y curl git zstd

if [ ! -x "$HOME/.elan/bin/elan" ]; then
  curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
fi

export PATH="$HOME/.elan/bin:$PATH"

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"
lake exe cache get
lake build
