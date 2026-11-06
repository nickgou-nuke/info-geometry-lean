#!/usr/bin/env bash
# Idempotent launcher & healthcheck for the InfoGeometry Auto-Ontology + Local vLLM stack:
#   - 127.0.0.1:58051/v1  -> local vLLM forwarder to 127.0.0.1:18765/v1 (nvidia/Qwen3.8-27B-NVFP4)
#   - localhost:5433      -> auto-ontology-postgres Docker container (306,503 Lean terms, 2,085,736 edges)
#   - localhost:3001      -> auto_ontology.server FastAPI REST API
#   - localhost:3002      -> auto_ontology.ingestion_service
#   - localhost:3003/mcp  -> auto-ontology-mcp FastMCP server
#   - localhost:3000      -> auto-ontology Next.js frontend & OAuth server
set -euo pipefail

AO_ROOT="/home/goutev/repos/auto-ontology-src"
NODE_BIN="/home/goutev/.nvm/versions/node/v22.22.2/bin"
PNPM_BIN="/home/goutev/.local/bin"

echo "[1/6] Ensuring populated Postgres container (auto-ontology-postgres on :5433) is running..."
docker start auto-ontology-postgres >/dev/null

echo "[2/6] Stopping any conflicting empty compose containers from external_refs/auto-ontology..."
docker stop auto-ontology-frontend auto-ontology auto-ontology-ingestion-service >/dev/null 2>&1 || true

echo "[3/6] Ensuring local LLM forwarder http://127.0.0.1:58051/v1 -> 127.0.0.1:18765/v1 is active..."
if ! ss -tln | grep -q ':58051 '; then
  systemctl --user stop auto-ontology-llm-58051.service >/dev/null 2>&1 || true
  systemd-run --user --unit=auto-ontology-llm-58051 --collect \
    socat TCP-LISTEN:58051,bind=127.0.0.1,reuseaddr,fork TCP:127.0.0.1:18765
fi

echo "[4/6] Ensuring Auto-Ontology Backend (:3001) and Ingestion (:3002) are active..."
if ! ss -tln | grep -q ':3001 '; then
  systemctl --user stop auto-ontology-backend.service >/dev/null 2>&1 || true
  systemd-run --user --unit=auto-ontology-backend --working-directory="$AO_ROOT" --collect \
    /bin/bash -c "set -a && source .env && set +a && exec $AO_ROOT/.venv-ao/bin/python -m auto_ontology.server"
fi

if ! ss -tln | grep -q ':3002 '; then
  systemctl --user stop auto-ontology-ingestion.service >/dev/null 2>&1 || true
  systemd-run --user --unit=auto-ontology-ingestion --working-directory="$AO_ROOT" --collect \
    /bin/bash -c "set -a && source .env && set +a && exec $AO_ROOT/.venv-ao/bin/python -m auto_ontology.ingestion_service"
fi

echo "[5/6] Ensuring Auto-Ontology MCP (:3003) and Next.js Frontend (:3000) are active..."
if ! ss -tln | grep -q ':3003 '; then
  systemctl --user stop auto-ontology-mcp.service >/dev/null 2>&1 || true
  systemd-run --user --unit=auto-ontology-mcp --working-directory="$AO_ROOT" --collect \
    /bin/bash -c "set -a && source .env && set +a && exec $AO_ROOT/.venv-ao/bin/auto-ontology-mcp"
fi

if ! ss -tln | grep -q ':3000 '; then
  systemctl --user stop auto-ontology-frontend.service >/dev/null 2>&1 || true
  systemd-run --user --unit=auto-ontology-frontend --working-directory="$AO_ROOT/frontend" --collect \
    /bin/bash -c "export PATH=\"$NODE_BIN:$PNPM_BIN:\$PATH\" && set -a && source ../.env && set +a && export PYTHON_API_URL=http://localhost:3001 && exec $NODE_BIN/npx next dev -p 3000"
fi

sleep 3
echo "[6/6] Verifying endpoints..."
echo "  - LLM (127.0.0.1:58051/v1/models): $(curl -sf http://127.0.0.1:58051/v1/models | head -c 120)..."
echo "  - Auto-Ontology REST (:3001 total InfoGeometry terms): $(curl -sf 'http://localhost:3001/api/terms?query=InfoGeometry&limit=1' | python3 -c 'import sys,json; print(json.load(sys.stdin).get("total"))')"
echo "  - Auto-Ontology Ingestion (:3002/health/live): $(curl -sf http://localhost:3002/health/live)"
ss -tlnp | grep -E ':(58051|5433|3000|3001|3002|3003)\b'
