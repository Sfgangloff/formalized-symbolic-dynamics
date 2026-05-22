#!/usr/bin/env bash
set -e

FAIL=0

# Match `pattern` only against Lean source content, stripping out `/- ... -/`
# block comments (including the `/-! ... -/` and `/-- ... -/` docstring forms)
# and `--` line comments first. Tracks block-comment state across lines.
check_forbidden () {
  local folder="$1"
  local pattern="$2"
  local description="$3"

  local matches
  matches=$(
    find "$folder" -name "*.lean" -print0 2>/dev/null | \
    while IFS= read -r -d '' file; do
      awk -v file="$file" -v pat="$pattern" '
        BEGIN { in_block = 0 }
        {
          line = $0
          rebuilt = ""
          i = 1
          n = length(line)
          while (i <= n) {
            two = substr(line, i, 2)
            if (in_block) {
              if (two == "-/") { in_block = 0; i += 2 } else { i += 1 }
            } else if (two == "/-") {
              in_block = 1; i += 2
            } else {
              rebuilt = rebuilt substr(line, i, 1); i += 1
            }
          }
          dd = index(rebuilt, "--")
          if (dd > 0) rebuilt = substr(rebuilt, 1, dd - 1)
          if (rebuilt ~ pat) print file ":" NR ":" $0
        }
      ' "$file"
    done
  )

  if [ -n "$matches" ]; then
    echo "$matches"
    echo
    echo "Forbidden construct detected in $folder"
    echo "Rule violated: $description"
    echo
    FAIL=1
  fi
}

echo "Checking SymbolicDynamics policy..."

#
# axioms/: only axioms allowed
#

check_forbidden \
  "SymbolicDynamics/axioms" \
  '^[[:space:]]*(theorem|lemma|def|definition)[[:space:]]' \
  "No theorem/lemma/def/definition allowed in axioms"

#
# dependencies/: no axioms
#

check_forbidden \
  "SymbolicDynamics/dependencies" \
  '^[[:space:]]*axiom[[:space:]]' \
  "No axiom allowed in dependencies"

#
# papers/: no axioms
#

check_forbidden \
  "SymbolicDynamics/papers" \
  '^[[:space:]]*axiom[[:space:]]' \
  "No axiom allowed in papers"

if [ "$FAIL" -ne 0 ]; then
  echo "SymbolicDynamics policy check FAILED."
  exit 1
fi

echo "SymbolicDynamics policy check PASSED."
