#!/usr/bin/env bash
# Install the Rocq toolchain on a fresh Linux machine: Rocq 9.0.1, MathComp
# 2.5.0, Hierarchy Builder 1.10.1, deriving 0.2.2, paco 4.2.3, in an opam
# switch named [nonint].  Re-running skips everything already installed.  The
# first run compiles MathComp from source and takes a while.
set -euo pipefail

SUDO=""
if [ "$(id -u)" -ne 0 ] && command -v sudo >/dev/null 2>&1; then SUDO="sudo"; fi

if command -v apt-get >/dev/null 2>&1; then
  missing=""
  for p in opam make gcc unzip bubblewrap curl m4 pkg-config libgmp-dev python3; do
    dpkg -s "$p" >/dev/null 2>&1 || missing="$missing $p"
  done
  if [ -n "$missing" ]; then
    $SUDO apt-get update -qq
    # shellcheck disable=SC2086
    $SUDO apt-get install -y -qq $missing
  fi
fi

export OPAMYES=1
[ -d "$HOME/.opam" ] || opam init --bare --disable-sandboxing -n
if ! opam switch list --short 2>/dev/null | grep -qx nonint; then
  # An opam-built compiler, as locally.  The system OCaml would mix the
  # distribution's OCaml libraries with opam's, which breaks some builds.
  opam switch create nonint ocaml-base-compiler.5.4.0
fi
eval "$(opam env --switch=nonint --set-switch)"

pkgs="rocq-core.9.0.1 rocq-stdlib.9.0.0 rocq-mathcomp-ssreflect.2.5.0
      rocq-hierarchy-builder.1.10.1 coq-deriving.0.2.2 coq-paco.4.2.3"
# shellcheck disable=SC2086
if ! opam list --installed --silent $pkgs 2>/dev/null; then
  opam repo add rocq-released https://rocq-prover.org/opam/released --all-switches 2>/dev/null || true
  opam update -q
  # shellcheck disable=SC2086
  opam install -q $pkgs
fi

grep -qs "opam env --switch=nonint" "$HOME/.nonint-env" ||
  echo 'eval "$(opam env --switch=nonint --set-switch)"' >> "$HOME/.nonint-env"
echo "Rocq toolchain ready."
