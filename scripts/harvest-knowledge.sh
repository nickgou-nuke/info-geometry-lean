#!/usr/bin/env bash
# Harvest knowledge from Wikipedia → knowledge_base.json
# Usage: ./scripts/harvest-knowledge.sh "Virasoro algebra central extension"

set -euo pipefail
QUERY="$*"
[ -z "$QUERY" ] && { echo "Usage: $0 <search query>"; exit 1; }

cd "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/.."

echo "📡 Harvesting: $QUERY"

# Fetch Wikipedia
encoded=$(python3 -c "import urllib.parse; print(urllib.parse.quote('''$QUERY'''))")
curl -s "https://en.wikipedia.org/w/api.php?action=query&prop=extracts&exintro=true&explaintext=true&titles=${encoded}&format=json" \
  -o /tmp/wiki_harvest.json 2>/dev/null

# Show + Index in one Python call
source .venv/bin/activate 2>/dev/null || true
python3 - "$QUERY" << 'PYEOF'
import json, os, urllib.request, sys

query = sys.argv[1]
kb_file = 'knowledge_base.json'

# Load Wikipedia
with open('/tmp/wiki_harvest.json') as f:
    data = json.load(f)

for pid, page in data.get('query',{}).get('pages',{}).items():
    if pid != '-1':
        title = page.get('title','?')
        extract = page.get('extract','')
        desc = page.get('description','')
        print(f'  📄 Wikipedia: {title}')
        if desc: print(f'     {desc}')
        if extract: print(f'     {extract[:200]}...')

        # Index into KB
        kb = json.load(open(kb_file)) if os.path.exists(kb_file) else []
        entry = {
            'title': title,
            'content': extract[:2000],
            'source': 'wikipedia',
            'tags': query.lower().split(),
            'status': 'literature'
        }
        if not any(e.get('title') == title for e in kb):
            kb.append(entry)
            print(f'  ✅ Indexed')
        else:
            print(f'  ⚡ Already in KB')
        json.dump(kb, open(kb_file, 'w'), indent=2)
        print(f'  💾 KB: {len(kb)} entries')
PYEOF
