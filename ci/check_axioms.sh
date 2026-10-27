#!/bin/sh
# Print the assumptions of the paper's results and fail on any assumption other
# than the lattice parameters definitions.d and definitions.L.
set -e
rocq compile -Q . NonInterference ci/axioms.v > ci/axioms.out 2>&1
cat ci/axioms.out
# Each assumption is printed as "name : type", starting at column 0.
unexpected=$(grep -E '^[A-Za-z_][A-Za-z0-9_.]* :' ci/axioms.out | grep -vE '^definitions\.(d|L) :' || true)
if [ -n "$unexpected" ]; then
  echo "Unexpected assumptions:"
  echo "$unexpected"
  exit 1
fi
echo "OK: no assumptions beyond the lattice parameters."
