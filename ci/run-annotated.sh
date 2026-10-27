#!/usr/bin/env bash
# Run a command in GitHub Actions; if it fails, attach the last 60 lines of its
# output to the run as an error annotation, which can be read without logging in.
#
#   bash ci/run-annotated.sh "title" command args...
set -uo pipefail
title="$1"; shift
log="$(mktemp)"
"$@" 2>&1 | tee "$log"
status=${PIPESTATUS[0]}
if [ "$status" -ne 0 ]; then
  # Annotation messages encode %, CR and LF.
  msg="$(tail -n 60 "$log" | sed -e 's/%/%25/g' -e 's/\r/%0D/g' | awk '{printf "%s%%0A", $0}')"
  echo "::error title=$title (exit $status)::$msg"
fi
exit "$status"
