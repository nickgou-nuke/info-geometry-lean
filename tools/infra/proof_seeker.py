#!/usr/bin/env python3
"""Proof Seeker — searches literature, internet, and mathlib for existing proofs.

When a GEPA-evolved skill fails a task, the Seeker attempts to find a genuine
mathematical proof for the target theorem by searching all available sources,
then digests the results into a candidate Lean proof.

Usage:
    python3 tools/infra/proof_seeker.py \\
        --target "mellin_theta_eq_completed_zeta" \\
        --context-file lean/InfoGeometry/Canonical/ZetaFunctionalEquationLayer.lean \\
        --output lean/InfoGeometry/Canonical/ZetaFunctionalEquationLayer_proof.lean
"""

from __future__ import annotations

import hashlib
import json
import logging
import os
import re
import subprocess
import sys
import time
from dataclasses import dataclass, field, asdict
from datetime import datetime
from pathlib import Path
from typing import Any, Optional

logger = logging.getLogger("proof_seeker")

_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]
_SEARCH_CACHE = _REPO / "quarantine" / "proof_seeker" / "search_cache"


# ---------------------------------------------------------------------------
# Models
# ---------------------------------------------------------------------------

@dataclass
class SearchResult:
    """A single search result from any source."""
    source: str              # "mathlib", "arxiv", "web", "alexandria"
    title: str
    url: str = ""
    snippet: str = ""
    relevance: float = 0.5
    content_path: Path | None = None


@dataclass
class ProofCandidate:
    """A candidate proof generated from search results."""
    source_results: list[SearchResult] = field(default_factory=list)
    proof_lean: str = ""        # The candidate Lean proof code
    proof_natural: str = ""     # Natural language proof sketch
    confidence: float = 0.0     # 0-1 how confident the digester is
    formalization_attempts: int = 0


# ---------------------------------------------------------------------------
# Proof Seeker
# ---------------------------------------------------------------------------

class ProofSeeker:
    """Searches multiple sources for existing proofs matching a target theorem.

    Sources (in order of authority):
    1. mathlib / LeanSearch — by type signature or theorem name
    2. Alexandria — already-ingested literature corpus
    3. arXiv — papers matching the theorem domain
    4. Web — forum posts, blog proofs, StackExchange
    """

    def __init__(self):
        _SEARCH_CACHE.mkdir(parents=True, exist_ok=True)

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def search(
        self,
        target_name: str,
        *,
        module_hint: str = "",
        type_signature: str = "",
        max_results: int = 10,
    ) -> list[SearchResult]:
        """Search all sources for proofs matching *target_name*.

        Returns merged and deduplicated results sorted by relevance.
        """
        logger.info("Searching for '%s' (module: %s)", target_name, module_hint)

        results: list[SearchResult] = []

        # 1. Search mathlib via LeanSearch
        if type_signature:
            results.extend(self._search_leansearch(type_signature, max_results // 2))

        # 2. Search mathlib by name
        results.extend(self._search_loogle(target_name, max_results // 3))

        # 3. Search Alexandria corpus
        results.extend(self._search_alexandria(target_name, module_hint))

        # 4. Search arXiv
        results.extend(self._search_arxiv(target_name, max_results // 2))

        # Deduplicate by title
        seen: set[str] = set()
        deduped = []
        for r in results:
            key = hashlib.sha256(r.title.encode()).hexdigest()[:16]
            if key not in seen:
                seen.add(key)
                deduped.append(r)

        deduped.sort(key=lambda r: -r.relevance)
        logger.info("Found %d unique results (from %d raw)", len(deduped), len(results))
        return deduped[:max_results]

    @staticmethod
    def _extract_latex_theorems(text: str, max_chars: int = 2000) -> str:
        """Extract theorem/lemma/proof environments from LaTeX source."""
        import re
        parts = []
        # Extract \begin{theorem}...\end{theorem} and similar
        for env in ["theorem", "lemma", "proposition", "corollary", "definition", "proof"]:
            for m in re.finditer(
                rf"\\(begin|end)\{{{env}\}}.*?(?=\\(begin|end)\{{{env}\}}|\Z)",
                text, re.DOTALL | re.IGNORECASE
            ):
                parts.append(m.group()[:max_chars // 4])
                if sum(len(p) for p in parts) >= max_chars:
                    break
        # Fallback: extract display math
        if not parts:
            for m in re.finditer(r"\$\$.*?\$\$", text, re.DOTALL)[:5]:
                parts.append(m.group())
        return "\n\n".join(parts)[:max_chars]

    def digest(
        self,
        results: list[SearchResult],
        target_name: str,
        context_code: str,
    ) -> ProofCandidate:
        """Generate a candidate Lean proof using DeepSeek as coding agent.

        DeepSeek already knows the mathematics — no arXiv search needed.
        The prompt includes the target name, docstring context, and surrounding
        Lean code so DeepSeek can generate a proof using the structure's fields.
        """
        logger.info("Generating proof candidate for '%s' via DeepSeek coding agent", target_name)

        short_ctx = context_code[:1200].strip() if context_code else ""

        prompt = (
            f"Lean proof generation.\n\n"
            f"Target: `{target_name}`\n"
            f"Context:\n```lean4\n{short_ctx}\n```\n"
            f"Write a complete Lean proof for `{target_name}` using the structure's "
            f"existing fields. The proof must compile with `lake build`. "
            f"Return JSON: {{\"proof_sketch\": \"...\", \"lean_code\": \"...\"}}"
        )

        # Load env vars for Pi and load the skill
        self._load_hermes_env()
        skill_path = _REPO / "skills" / "closure-debt-proof" / "SKILL.md"
        skill_arg = ["--skill", str(skill_path)] if skill_path.exists() else []

        try:
            result = subprocess.run(
                ["pi", "-p", prompt,
                 "--provider", "deepseek", "--model", "deepseek-v4-flash",
                 "--no-session", "--no-tools"] + skill_arg,
                capture_output=True, text=True, timeout=180,
            )
            output = (result.stdout or "") + (result.stderr or "")
        except Exception as exc:
            logger.warning("Digestion LLM failed: %s", exc)
            return ProofCandidate(
                source_results=results,
                confidence=0.0,
                formalization_attempts=0,
            )

        # Parse JSON from Hermes output
        m = re.search(r"\{.*\}", output, re.DOTALL)
        lean_code = ""
        proof_sketch = ""
        confidence = 0.3

        if m:
            try:
                data = json.loads(m.group())
                lean_code = data.get("lean_code", "")
                proof_sketch = data.get("proof_sketch", "")
                if lean_code:
                    confidence = 0.6
            except json.JSONDecodeError:
                pass

        # Fallback: extract Lean code blocks
        if not lean_code:
            blocks = re.findall(r"```(?:lean4|lean)\s*\n(.*?)```", output, re.DOTALL)
            if blocks:
                lean_code = "\n\n".join(blocks)
                confidence = 0.5

        return ProofCandidate(
            source_results=results,
            proof_lean=lean_code,
            proof_natural=proof_sketch,
            confidence=confidence,
            formalization_attempts=0,
        )

    def formalize(
        self,
        candidate: ProofCandidate,
        target_file: Path,
        target_line: int,
        max_iterations: int = 3,
    ) -> bool:
        """Iteratively refine the candidate proof using compiler errors.

        Acts as a coding agent: write → compile → read errors → fix → repeat.
        Returns True if the file compiles within *max_iterations* attempts.
        """
        if not candidate.proof_lean:
            logger.warning("No Lean code to formalize")
            return False

        original = target_file.read_text(encoding="utf-8")
        lines = original.split("\n")
        if target_line > len(lines):
            logger.warning("Target line %d exceeds file length", target_line)
            return False

        proof_lines = candidate.proof_lean.strip().split("\n")

        for attempt in range(max_iterations):
            logger.info("  Formalization attempt %d/%d", attempt + 1, max_iterations)

            # Backup
            backup = target_file.with_suffix(".lean.bak")
            target_file.rename(backup)

            try:
                # Write the proof
                new_lines = lines[:target_line - 1] + proof_lines + lines[target_line:]
                target_file.write_text("\n".join(new_lines), encoding="utf-8")

                # Compile
                result = subprocess.run(
                    ["lake", "env", "lean", str(target_file)],
                    capture_output=True, text=True, timeout=120,
                    cwd=str(_REPO),
                )

                if result.returncode == 0:
                    logger.info("  ✓ Compilation SUCCESS (attempt %d)", attempt + 1)
                    backup.unlink(missing_ok=True)
                    return True

                # Compilation failed — read errors and fix
                raw_stderr = (result.stderr or "")[:2000]
                error_output = "\n".join(
                    l for l in raw_stderr.split("\n")
                    if not l.strip().startswith("note:") and not l.strip().startswith("to ")
                )  # last 20 meaningful lines
                logger.info("  ✗ Compilation FAILED — fixing...")

                # Build a fix prompt with the error
                current_code = target_file.read_text(encoding="utf-8")
                fix_prompt = (
                    f"Lean compilation error. Fix the proof at `{target_file.name}:{target_line}`.\n"
                    f"Error:\n```\n{error_output}\n```\n"
                    f"Code:\n```lean4\n{current_code[:2000]}\n```\n"
                    f"Return ONLY the fixed Lean code for the proof block, no markdown fences."
                )

                # Use Pi as the lightweight coding agent for iterative fixes
                fix_result = subprocess.run(
                    ["pi", "-p", fix_prompt,
                     "--provider", "deepseek", "--model", "deepseek-v4-flash",
                     "--no-session", "--no-tools"],
                    capture_output=True, text=True, timeout=120,
                )
                fix_output = (fix_result.stdout or "") + (fix_result.stderr or "")

                # Extract the fixed proof
                import re as _re
                blocks = _re.findall(r"```(?:lean4|lean)?\s*\n(.*?)```", fix_output, _re.DOTALL)
                if blocks:
                    proof_lines = "\n".join(b.strip() for b in blocks).split("\n")
                else:
                    proof_lines = fix_output.strip().split("\n")

            except Exception as exc:
                logger.error("  Formalization error: %s", exc)
                target_file.write_text(original, encoding="utf-8")
                backup.unlink(missing_ok=True)
                return False
            finally:
                # Always restore the original between attempts
                if backup.exists():
                    target_file.write_text(original, encoding="utf-8")
                    backup.unlink(missing_ok=True)

        logger.warning("  All %d formalization attempts failed", max_iterations)
        return False

    # ------------------------------------------------------------------
    # Search backends
    # ------------------------------------------------------------------

    def _search_leansearch(self, query: str, limit: int) -> list[SearchResult]:
        """Search mathlib via LeanSearch.net."""
        cache_key = hashlib.sha256(f"leansearch:{query}".encode()).hexdigest()[:16]
        cache_path = _SEARCH_CACHE / f"leansearch_{cache_key}.json"
        if cache_path.exists():
            return self._load_cache(cache_path)

        results = []
        try:
            import urllib.request, json as _json
            req = urllib.request.Request(
                "https://leansearch.net/api/search",
                data=json.dumps({"query": query, "limit": limit}).encode(),
                headers={"Content-Type": "application/json"},
            )
            resp = urllib.request.urlopen(req, timeout=10)
            data = _json.loads(resp.read())
            for item in data.get("results", []):
                results.append(SearchResult(
                    source="mathlib",
                    title=item.get("name", item.get("decl", "?")),
                    url=item.get("url", ""),
                    snippet=item.get("doc", "")[:500],
                    relevance=item.get("score", 0.5),
                ))
            self._save_cache(cache_path, results)
        except Exception as exc:
            logger.debug("LeanSearch failed: %s", exc)
        return results

    def _search_loogle(self, query: str, limit: int) -> list[SearchResult]:
        """Search mathlib via Loogle."""
        cache_key = hashlib.sha256(f"loogle:{query}".encode()).hexdigest()[:16]
        cache_path = _SEARCH_CACHE / f"loogle_{cache_key}.json"
        if cache_path.exists():
            return self._load_cache(cache_path)

        results = []
        try:
            import urllib.request, json as _json
            # Loogle has a JSON API
            req = urllib.request.Request(
                f"https://loogle.lean-lang.org/?q={urllib.parse.quote(query)}&json=true",
                headers={"Accept": "application/json"},
            )
            resp = urllib.request.urlopen(req, timeout=10)
            data = _json.loads(resp.read())
            for item in data if isinstance(data, list) else data.get("results", []):
                results.append(SearchResult(
                    source="mathlib",
                    title=item.get("name", item.get("decl", query)),
                    url=item.get("url", f"https://loogle.lean-lang.org/?q={query}"),
                    snippet=item.get("doc", "")[:500],
                    relevance=0.7,
                ))
            self._save_cache(cache_path, results)
        except Exception as exc:
            logger.debug("Loogle search failed: %s", exc)
        return results

    def _search_alexandria(self, target: str, module_hint: str) -> list[SearchResult]:
        """Search the Alexandria-ingested literature corpus."""
        results = []
        alexandria_dir = _REPO / "alexandria" / "documents"
        if not alexandria_dir.exists():
            return results

        keywords = set(re.findall(r"[A-Za-z]{4,}", target))
        for f in alexandria_dir.rglob("*.md"):
            try:
                text = f.read_text(errors="replace")
                matches = sum(1 for kw in keywords if kw.lower() in text.lower())
                if matches >= 2:
                    results.append(SearchResult(
                        source="alexandria",
                        title=f.name,
                        snippet=text[:500],
                        relevance=matches / max(1, len(keywords)),
                    ))
            except Exception:
                continue

        return results

    def _search_arxiv(self, query: str, limit: int) -> list[SearchResult]:
        """Search arXiv for papers matching the query."""
        cache_key = hashlib.sha256(f"arxiv:{query}".encode()).hexdigest()[:16]
        cache_path = _SEARCH_CACHE / f"arxiv_{cache_key}.json"
        if cache_path.exists():
            return self._load_cache(cache_path)

        results = []
        try:
            import urllib.request, xml.etree.ElementTree as ET
            url = f"http://export.arxiv.org/api/query?search_query=all:{urllib.parse.quote(query)}&max_results={limit}"
            resp = urllib.request.urlopen(url, timeout=15)
            root = ET.fromstring(resp.read())
            ns = {"atom": "http://www.w3.org/2005/Atom"}
            for entry in root.findall("atom:entry", ns):
                title = entry.findtext("atom:title", "", ns).strip()
                summary = entry.findtext("atom:summary", "", ns).strip()
                link = entry.find("atom:id", ns)
                url_text = link.text if link is not None else ""
                results.append(SearchResult(
                    source="arxiv",
                    title=title[:200],
                    url=url_text,
                    snippet=summary[:500],
                    relevance=0.4,
                ))
            self._save_cache(cache_path, results)
        except Exception as exc:
            logger.debug("arXiv search failed: %s", exc)
        return results

    # ------------------------------------------------------------------
    # Cache
    # ------------------------------------------------------------------

    def _load_cache(self, path: Path) -> list[SearchResult]:
        try:
            data = json.loads(path.read_text())
            return [SearchResult(**item) for item in data]
        except Exception:
            return []

    def _save_cache(self, path: Path, results: list[SearchResult]) -> None:
        try:
            path.write_text(json.dumps([asdict(r) for r in results], indent=2))
        except Exception as exc:
            logger.debug("Cache save failed: %s", exc)

    @staticmethod
    def _load_hermes_env() -> None:
        env_path = Path.home() / ".hermes" / ".env"
        if not env_path.exists():
            return
        try:
            import dotenv
            dotenv.load_dotenv(env_path)
        except ImportError:
            for line in env_path.read_text().splitlines():
                line = line.strip()
                if not line or line.startswith("#") or "=" not in line:
                    continue
                key, _, val = line.partition("=")
                if key and val and not os.environ.get(key):
                    os.environ[key] = val.strip().strip("'\"")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> None:
    import argparse
    parser = argparse.ArgumentParser(description="Proof Seeker — find proofs from literature")
    parser.add_argument("--target", required=True, help="Theorem name to search for")
    parser.add_argument("--type-sig", help="Type signature for LeanSearch")
    parser.add_argument("--context-file", type=Path, help="Lean file containing the target")
    parser.add_argument("--output", type=Path, help="Output file for candidate proof")
    parser.add_argument("--search-only", action="store_true", help="Only search, don't digest")
    parser.add_argument("--formalize", action="store_true", help="Attempt to write proof into file")
    parser.add_argument("--line", type=int, default=0, help="Line number for formalization")
    args = parser.parse_args()

    logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(name)s] %(message)s")

    seeker = ProofSeeker()

    # Search
    results = seeker.search(args.target, module_hint=str(args.context_file or ""))
    print(f"Search results: {len(results)}")
    for r in results[:5]:
        print(f"  [{r.source:10s}] {r.title[:80]}")
        if r.url:
            print(f"           {r.url}")

    if args.search_only or not results:
        return

    # Digest
    context_code = ""
    if args.context_file and args.context_file.exists():
        context_code = args.context_file.read_text(encoding="utf-8")

    candidate = seeker.digest(results, args.target, context_code)
    print(f"\nProof candidate (confidence: {candidate.confidence:.2f}):")
    if candidate.proof_natural:
        print(f"  Sketch: {candidate.proof_natural[:200]}")
    if candidate.proof_lean:
        print(f"  Lean code ({len(candidate.proof_lean)} chars):")
        print(f"  {candidate.proof_lean[:500]}")

    # Formalize
    if args.formalize and args.context_file and args.line > 0:
        success = seeker.formalize(candidate, args.context_file, args.line)
        print(f"\nFormalization: {'✓ SUCCESS' if success else '✗ FAILED'}")

    # Save output
    if args.output:
        combined = {
            "target": args.target,
            "search_results": [asdict(r) for r in results[:10]],
            "proof_sketch": candidate.proof_natural,
            "lean_code": candidate.proof_lean,
            "confidence": candidate.confidence,
        }
        args.output.write_text(json.dumps(combined, indent=2))
        print(f"\nSaved: {args.output}")


if __name__ == "__main__":
    main()
