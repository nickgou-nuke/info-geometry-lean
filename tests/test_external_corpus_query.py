from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

SCRIPT = Path('tools/infra/query_external_corpus.py')
CORPUS = Path('external_refs/LeanMillenniumPrizeProblems')


def run(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(SCRIPT), *args],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )


def test_lists_discovered_corpora() -> None:
    proc = run('--list')
    assert proc.returncode == 0, proc.stdout + proc.stderr
    payload = json.loads(proc.stdout)
    assert any(Path(p).name == 'pyw' for p in payload['corpora'])


def test_queries_lmpm_corpus_for_millennium() -> None:
    proc = run('--corpus', str(CORPUS), 'millennium', '--limit', '3')
    assert proc.returncode == 0, proc.stdout + proc.stderr
    payload = json.loads(proc.stdout)
    assert payload['corpus'].endswith('external_refs/LeanMillenniumPrizeProblems')
    names = [row['name'] for row in payload['results']]
    assert names and all('name' in row for row in payload['results'])
