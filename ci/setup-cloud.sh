#!/usr/bin/env bash
# Set up a fresh Linux machine (e.g. a Claude Code cloud environment).
#
#   bash ci/setup-cloud.sh          # both
#   bash ci/setup-cloud.sh rocq     # proofs only
#   bash ci/setup-cloud.sh tex      # paper only
#
# Each part is skipped when already installed.  Afterwards new shells load
# ~/.nonint-env; build with ci/build.sh.
set -euo pipefail
dir="$(cd "$(dirname "$0")" && pwd)"
parts="${*:-rocq tex}"

for rc in "$HOME/.bashrc" "$HOME/.profile"; do
  grep -qs "nonint-env" "$rc" || echo '[ -f "$HOME/.nonint-env" ] && . "$HOME/.nonint-env"' >> "$rc"
done

for part in $parts; do
  case "$part" in
    rocq) bash "$dir/setup-rocq.sh" ;;
    tex)  bash "$dir/setup-tex.sh" ;;
    *) echo "unknown part: $part (use rocq or tex)" >&2; exit 2 ;;
  esac
done
