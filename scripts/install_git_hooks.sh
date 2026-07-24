#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

git config core.hooksPath .githooks

chmod +x .githooks/pre-commit || true
chmod +x .githooks/pre-push || true

printf 'Installed repo git hooks: core.hooksPath=.githooks\n'
