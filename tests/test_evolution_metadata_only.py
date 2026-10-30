"""Metadata-only extraction preserves messages and never invents diff counts."""
import json
import subprocess

import pytest

from tools.infra.evolution_extract import stream_to_jsonl


def test_metadata_only_keeps_stat_like_prose_and_binds_resume_mode(tmp_path):
    repo = tmp_path / 'repo'
    repo.mkdir()
    def git(*args):
        return subprocess.run(['git', *args], cwd=repo, check=True,
                              capture_output=True, text=True).stdout.strip()
    git('init')
    git('config', 'user.email', 'test@example.invalid')
    git('config', 'user.name', 'Test')
    (repo / 'file').write_text('content\n')
    git('add', 'file')
    git('commit', '-m', 'Example', '-m', ' 1 file changed, 2 insertions(+)')
    out = tmp_path / 'metadata.jsonl'
    assert stream_to_jsonl(repo, out, metadata_only=True) == 1
    row = json.loads(out.read_text())
    assert row['sha'] == git('rev-parse', 'HEAD')
    assert '1 file changed, 2 insertions(+)' in row['body']
    assert row['diff_stats_status'] == 'not_collected'
    assert all(row[field] is None for field in ('files_changed', 'insertions', 'deletions'))
    assert stream_to_jsonl(repo, out, metadata_only=True, resume=True) == 1
    with pytest.raises(RuntimeError, match='extraction mode'):
        stream_to_jsonl(repo, out, resume=True)
