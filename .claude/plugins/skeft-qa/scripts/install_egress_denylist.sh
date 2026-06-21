#!/usr/bin/env bash
# Install the LOCAL web-egress denylist from the committed template, if absent.
# The local file is gitignored and may hold operator/private literals — never commit it.
set -euo pipefail
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SAMPLE="$DIR/research_egress_denylist.sample.txt"
LOCAL="$DIR/research_egress_denylist.txt"

if [ -e "$LOCAL" ]; then
  echo "local denylist already present: $LOCAL"
  exit 0
fi
cp "$SAMPLE" "$LOCAL"
echo "installed $LOCAL from template."
echo "Now edit it: uncomment + fill in the operator-identity / firewall rows"
echo "(and, in the private repo, the proprietary substrate-term rows from docs/vectors/)."
