#!/usr/bin/env bash
# Set up a fresh Linux machine (e.g. a Claude Code cloud environment) to build the
# development.  The paper is kept in a separate repository with its own TeX setup.
#
#   bash ci/setup-cloud.sh
#
# Skipped when already installed.  Afterwards new shells load ~/.nonint-env;
# build with ci/build.sh.
set -euo pipefail
dir="$(cd "$(dirname "$0")" && pwd)"

for rc in "$HOME/.bashrc" "$HOME/.profile"; do
  grep -qs "nonint-env" "$rc" || echo '[ -f "$HOME/.nonint-env" ] && . "$HOME/.nonint-env"' >> "$rc"
done

bash "$dir/setup-rocq.sh"
