#!/usr/bin/env bash
# Build the development, then run the axiom check.
#
#   bash ci/build.sh
#
# The build is incremental: make recompiles only changed files and their
# dependents.  The paper is kept in a separate repository; its code links read
# theories/ from a checkout of this one.
set -euo pipefail
cd "$(dirname "$0")/.."
# shellcheck disable=SC1091
[ -f "$HOME/.nonint-env" ] && . "$HOME/.nonint-env"

[ Makefile -nt _CoqProject ] || rocq makefile -f _CoqProject -o Makefile
make -j"$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 2)"
sh ci/check_axioms.sh | tail -1
