#!/bin/sh
set -eu

reward=0
mkdir -p /logs/verifier

write_fallback_report() {
    if [ ! -s /logs/verifier/ctrf.json ]; then
        cat > /logs/verifier/ctrf.json <<'JSON'
{"results":{"tool":{"name":"pytest-json-ctrf"},"summary":{"tests":0,"passed":0,"failed":0,"skipped":0,"pending":0,"other":0,"start":"","stop":"","suites":0},"tests":[]}}
JSON
    fi
}

finish() {
    write_fallback_report
    printf '%s\n' "$reward" > /logs/verifier/reward.txt
}
trap finish EXIT

set +e
pytest -vv --ctrf=/logs/verifier/ctrf.json /tests/test_submission.py
rc=$?
set -e

if [ "$rc" -eq 0 ]; then
    reward=1
fi
exit 0
