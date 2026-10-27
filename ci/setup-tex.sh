#!/usr/bin/env bash
# Install TinyTeX, a minimal pdfLaTeX, with only the packages and fonts the
# paper uses.  Re-running skips everything already installed.
set -euo pipefail

TEXBIN="$HOME/.TinyTeX/bin/x86_64-linux"
[ -x "$TEXBIN/pdflatex" ] || curl -fsSL "https://yihui.org/tinytex/install-bin-unix.sh" | sh

pkgs="latexmk ieeetran cleveref mathtools booktabs listings mathpartir pgf
      amsfonts amscls etoolbox refcount rerunfilecheck epstopdf-pkg url psnfss
      times courier helvetic symbol xcolor hyperref"
# Install only what is missing.
missing=""
for p in $pkgs; do
  "$TEXBIN/tlmgr" info --only-installed "$p" 2>/dev/null | grep -q "^installed: *Yes" ||
    missing="$missing $p"
done
# shellcheck disable=SC2086
[ -z "$missing" ] || "$TEXBIN/tlmgr" install $missing

command -v python3 >/dev/null 2>&1 || echo "warning: python3 is needed for tex/mechlinks.py"

grep -qs "TinyTeX" "$HOME/.nonint-env" ||
  echo 'export PATH="$HOME/.TinyTeX/bin/x86_64-linux:$PATH"' >> "$HOME/.nonint-env"
echo "TeX ready."
