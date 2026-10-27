#!/usr/bin/env bash
# Build what is relevant.
#
#   bash ci/build.sh            # only what the uncommitted changes affect
#   bash ci/build.sh proofs     # the development, then the axiom check
#   bash ci/build.sh paper      # tex/main.pdf
#   bash ci/build.sh all
#
# Both builds are incremental: make recompiles only changed files and their
# dependents, and latexmk reruns only when a source changed.  The paper depends
# on theories/ too: its code links carry line numbers (tex/mechlinks.py).
set -euo pipefail
cd "$(dirname "$0")/.."
# shellcheck disable=SC1091
[ -f "$HOME/.nonint-env" ] && . "$HOME/.nonint-env"

build_proofs() {
  [ Makefile -nt _CoqProject ] || rocq makefile -f _CoqProject -o Makefile
  make -j"$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 2)"
  sh ci/check_axioms.sh | tail -1
}

build_paper() {
  (cd tex && latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex >/dev/null) &&
    echo "Paper: tex/main.pdf"
}

targets="${1:-changed}"
if [ "$targets" = changed ]; then
  files="$( { git diff --name-only HEAD; git ls-files --others --exclude-standard; } | sort -u)"
  targets=""
  echo "$files" | grep -qE '^(theories/|_CoqProject$|ci/axioms\.v$|ci/check_axioms\.sh$)' &&
    targets="$targets proofs"
  echo "$files" | grep -qE '^(tex/|theories/.*\.v$)' && targets="$targets paper"
  [ -n "$targets" ] || { echo "Nothing to build."; exit 0; }
fi
[ "$targets" = all ] && targets="proofs paper"

for t in $targets; do
  case "$t" in
    proofs) build_proofs ;;
    paper)  build_paper ;;
    *) echo "unknown target: $t (use proofs, paper or all)" >&2; exit 2 ;;
  esac
done
