from pathlib import Path
import sys
import os

sys.path.insert(0, os.getcwd())
from tools.infra.pauli_authority_bridge import get_authority_data, ARANGO_URL, ARANGO_USER, ARANGO_PASSWORD

print(f"Testing ArangoDB at {ARANGO_URL} as {ARANGO_USER}...")
root = Path(os.getcwd())
try:
    data = get_authority_data(root)
    print(f"Success! Found {len(data)} declarations.")
except Exception as e:
    print(f"Failed: {e}")
