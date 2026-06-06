#!/usr/bin/env python3
"""GraphRAG context gatherer — pulls related declarations from ArangoDB DAG."""
from pathlib import Path

def gather_context(repo_root: Path, file_path: str, line: int, max_decls: int = 20) -> str:
    """Gather DAG context: related declarations, dependencies, neighbors."""
    import sys
    sys.path.insert(0, str(repo_root))
    from tools.infra.arango_env import *
    from tools.infra.hive_arango_queue import aql
    load_repo_arango_env(repo_root)
    ep = arango_endpoint()
    db = arango_database("hive_live")
    usr = arango_username()
    pwd = arango_password("alexandria_root")

    # Extract module from file path
    module = file_path.replace("lean/", "").replace(".lean", "").replace("/", ".")
    parts = []

    # Query: get declarations near this file (by module prefix)
    try:
        rows = aql(ep, db, usr, pwd, f"""
            FOR d IN hive_declarations
              FILTER d.module LIKE @prefix
              SORT d.module ASC
              LIMIT {max_decls}
              RETURN {{module: d.module, name: d.name, type: d.type}}
        """, {"prefix": module.split(".")[0] + "%"})
        if rows:
            parts.append(f"Related declarations (DAG neighborhood of {module}):")
            for r in rows[:max_decls]:
                parts.append(f"  {r.get('module','?')}.{r.get('name','?')} : {r.get('type','?')}")
    except Exception:
        parts.append(f"(DAG query unavailable for {module})")

    # Fallback: scan the file for imports and definitions
    try:
        fpath = repo_root / file_path
        if fpath.exists():
            code = fpath.read_text(errors="replace")
            import re
            imports = re.findall(r'^import\s+(.+)$', code, re.M)
            if imports:
                parts.append(f"\nImports ({len(imports)}):")
                for imp in imports[:20]:
                    parts.append(f"  import {imp}")
            defs = re.findall(r'^(?:theorem|lemma|def|structure|inductive|class)\s+(\S+)', code, re.M)
            if defs:
                parts.append(f"\nDefinitions in file ({len(defs)}):")
                for d in defs[:30]:
                    parts.append(f"  {d}")
    except Exception:
        pass

    return "\n".join(parts) if parts else "(no DAG context available)"
