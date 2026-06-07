#!/usr/bin/env python3
"""
Two-stage autonomous proof pipeline with SEPARATE lanes:

  proof-search ──[Google AI]──→ google-enriched ──[ChatGPT]──→ ready-to-code

Google stage → uses tools/infra/chatgpt_browser_harness_driver.py pattern
ChatGPT stage → uses chatgpt.com via browser-harness

Each has its OWN sentinel, OWN tab, NO cross-contamination.
"""
from __future__ import annotations
import json, logging, os, sys, time, subprocess, tempfile
from pathlib import Path

_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]
sys.path.insert(0, str(_REPO))

from tools.infra.arango_env import *
from tools.infra.hive_arango_queue import aql, claim_next_task, update_task_status
from tools.infra.lean_audit_prompt import build_lean_fix_prompt, extract_replacement_lean
from tools.infra.gepa_real_eval import _normalize_lean_file_path

try:
    from tools.infra.agent_message_ledger import record_message
except Exception:  # pragma: no cover - observation must never block workers.
    record_message = None

logger = logging.getLogger("pipeline")

POLL = 3
LEASE = 900

# ── Shared helpers ─────────────────────────────────────────────────────

def _resolve_file(task: dict) -> Path | None:
    pkt = task.get("runtime_goal_packet") or {}
    f = pkt.get("formal_target", "") or ""
    m = (pkt.get("module_hint", "") or "").replace(".", "/") + ".lean"
    import re; ma = re.search(r"(\S+\.lean):(\d+)", f)
    fp = ma.group(1) if ma else m
    fp = _normalize_lean_file_path(fp)
    p = _REPO / fp
    return p if p.exists() else None

def _claim(queue: str, kind: str, worker: str) -> dict | None:
    load_repo_arango_env(_REPO)
    return claim_next_task(
        arango_endpoint(), arango_database("hive_live"),
        arango_username(), arango_password("alexandria_root"),
        worker_id=worker, queue_name=queue, lease_seconds=LEASE, task_kind=kind)

def _save(task: dict, queue: str, kind: str, worker: str, extra: dict):
    load_repo_arango_env(_REPO)
    update_task_status(
        arango_endpoint(), arango_database("hive_live"),
        arango_username(), arango_password("alexandria_root"),
        task_key_value=task["_key"], worker_id=worker, status="pending",
        extra_fields={"queue_name": queue, "task_kind": kind, "runtime_goal_packet": extra})

def _pending(queue: str) -> int:
    load_repo_arango_env(_REPO)
    r = aql(arango_endpoint(), arango_database("hive_live"),
            arango_username(), arango_password("alexandria_root"),
            f"FOR t IN hive_tasks FILTER t.queue_name == '{queue}' FILTER t.status == 'pending' COLLECT WITH COUNT INTO n RETURN n", {})
    return r[0] if r else 0


# ── Stage 1: GOOGLE AI ─────────────────────────────────────────────────

GOOGLE_SCRIPT = _REPO / "tools" / "infra" / "google_ai_driver.py"
# ^ Reuse the same CDP driver for Google AI — just change the URL
GOOGLE_SENTINEL = "/tmp/google_ai_tab_ready"

def run_google_stage(once: bool = False):
    """Google AI Stage — separate lane, google.com/ai tab."""
    while True:
        try:
            task = _claim("proof-search", "proof.search", "google-stage")
            if task is None:
                n = _pending("proof-search")
                logger.info("[Google] No tasks. %d pending.", n)
                if once: break
                time.sleep(POLL); continue

            pkt = task.get("runtime_goal_packet") or {}
            target = pkt.get("formal_target", "")[:200]
            import re
            m = re.search(r"`([^`]+)`", target)
            theorem = m.group(1) if m else "unknown"

            prompt = (
                f"Explain in detail the rigorous mathematics behind, "
                f"do not comment just explain the math and then provide encoding into lean4 formal language: "
                f"{theorem}"
            )

            logger.info("[Google] Query: %s (%d chars)", theorem, len(prompt))

            # Write prompt to temp file for browser-harness driver
            pf = tempfile.NamedTemporaryFile(mode='w', suffix='.txt', delete=False)
            pf.write(prompt); pf.close()
            rf = tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False, prefix='google_')
            rf.close()

            env = os.environ.copy()
            env["GOOGLE_AI_PROMPT_FILE"] = pf.name
            env["GOOGLE_AI_RESULT_JSON"] = rf.name
            env["GOOGLE_AI_URL"] = "https://google.com/ai"
            env["GOOGLE_AI_TIMEOUT_SECONDS"] = "120"

            # Create sentinel for tab reuse
            open(GOOGLE_SENTINEL, "w").close()

            started = time.monotonic()
            proc = subprocess.run(
                ["browser-harness", "-c",
                 f"import sys; sys.path.insert(0, '{_REPO}'); exec(open('{GOOGLE_SCRIPT}').read())"],
                env=env, capture_output=True, text=True, timeout=180,
            )
            reply = Path(rf.name).read_text()[:4000] if Path(rf.name).exists() else ""
            if record_message is not None:
                try:
                    record_message(
                        source_tool="pipeline_workers.py",
                        source_file="tools/infra/pipeline_workers.py",
                        channel="pipeline_google_stage",
                        provider="browser-harness",
                        model="google_ai",
                        platform="google_ai",
                        prompt_text=prompt,
                        response_text=reply or (proc.stdout or "") + (proc.stderr or ""),
                        success=(proc.returncode == 0 and bool(reply.strip())),
                        latency_ms=(time.monotonic() - started) * 1000.0,
                        correlation_id=str(task.get("_key", "")),
                        metadata={
                            "task_key": task.get("_key", ""),
                            "theorem": theorem,
                            "returncode": proc.returncode,
                            "failure_pattern": "" if proc.returncode == 0 else (proc.stderr or "")[:160],
                        },
                    )
                except Exception:
                    pass
            os.unlink(pf.name)
            os.unlink(rf.name)

            logger.info("[Google] Got %d chars", len(reply))

            rp = dict(pkt)
            rp["google_context"] = reply
            rp["theorem"] = theorem
            _save(task, "google-enriched", "google.enriched", "google-stage", rp)
            logger.info("[Google] → google-enriched")
            if once: break

        except KeyboardInterrupt: break
        except Exception as e:
            logger.error("[Google] %s", e)
            time.sleep(10)


# ── Stage 2: CHATGPT ───────────────────────────────────────────────────

CHATGPT_SCRIPT = _REPO / "tools" / "infra" / "chatgpt_browser_harness_driver.py"
CHATGPT_SENTINEL = "/tmp/chatgpt_audit_tab_ready"

def run_chatgpt_stage(once: bool = False):
    """ChatGPT Stage — separate lane, chatgpt.com tab."""
    while True:
        try:
            task = _claim("google-enriched", "google.enriched", "chatgpt-stage")
            if task is None:
                n = _pending("google-enriched")
                logger.info("[ChatGPT] No tasks. %d pending.", n)
                if once: break
                time.sleep(POLL); continue

            pkt = task.get("runtime_goal_packet") or {}
            theorem = pkt.get("theorem", "unknown")
            gctx = pkt.get("google_context", "")
            fp = _resolve_file(task)

            context_code = fp.read_text() if fp else ""
            if gctx:
                context_code += (
                    "\n/* Google AI context:\n"
                    f"{gctx[:2500]}\n"
                    "*/\n"
                )
            prompt = build_lean_fix_prompt(
                target_name=theorem,
                context_code=context_code,
                target_file=str(fp) if fp else None,
            )

            logger.info("[ChatGPT] Sending '%s' (%d chars)", theorem, len(prompt))

            pf = tempfile.NamedTemporaryFile(mode='w', suffix='.txt', delete=False)
            pf.write(prompt); pf.close()
            rf = tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False, prefix='chatgpt_')
            rf.close()

            env = os.environ.copy()
            env["CHATGPT_PROMPT_FILE"] = pf.name
            env["CHATGPT_RESULT_JSON"] = rf.name
            env["CHATGPT_URL"] = "https://chatgpt.com"
            env["CHATGPT_TIMEOUT_SECONDS"] = "300"

            open(CHATGPT_SENTINEL, "w").close()

            started = time.monotonic()
            proc = subprocess.run(
                ["browser-harness", "-c",
                 f"import sys; sys.path.insert(0, '{_REPO}'); exec(open('{CHATGPT_SCRIPT}').read()); _main()"],
                env=env, capture_output=True, text=True, timeout=360,
            )
            reply = Path(rf.name).read_text()[:8000] if Path(rf.name).exists() else ""
            replacement = extract_replacement_lean(reply)
            if record_message is not None:
                try:
                    record_message(
                        source_tool="pipeline_workers.py",
                        source_file="tools/infra/pipeline_workers.py",
                        channel="pipeline_chatgpt_stage",
                        provider="browser-harness",
                        model="chatgpt",
                        platform="chatgpt",
                        prompt_text=prompt,
                        response_text=reply or (proc.stdout or "") + (proc.stderr or ""),
                        success=(proc.returncode == 0 and bool(reply.strip())),
                        latency_ms=(time.monotonic() - started) * 1000.0,
                        correlation_id=str(task.get("_key", "")),
                        metadata={
                            "task_key": task.get("_key", ""),
                            "theorem": theorem,
                            "returncode": proc.returncode,
                            "replacement_chars": len(replacement),
                            "failure_pattern": "" if proc.returncode == 0 else (proc.stderr or "")[:160],
                        },
                    )
                except Exception:
                    pass
            os.unlink(pf.name)
            os.unlink(rf.name)

            logger.info("[ChatGPT] Got %d chars; replacement %d chars", len(reply), len(replacement))

            rp = dict(pkt)
            rp["chatgpt_response"] = reply
            rp["chatgpt_code"] = replacement or reply
            _save(task, "ready-to-code", "ready.to.code", "chatgpt-stage", rp)
            logger.info("[ChatGPT] → ready-to-code")
            if once: break

        except KeyboardInterrupt: break
        except Exception as e:
            logger.error("[ChatGPT] %s", e)
            time.sleep(10)


if __name__ == "__main__":
    import argparse
    p = argparse.ArgumentParser()
    p.add_argument("--stage", choices=["google","chatgpt","all"], default="all")
    p.add_argument("--once", action="store_true")
    args = p.parse_args()
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(message)s", datefmt="%H:%M:%S")
    if args.stage in ("google","all"):
        logger.info("=== GOOGLE STAGE ===")
        run_google_stage(once=args.once)
    if args.stage in ("chatgpt","all"):
        logger.info("=== CHATGPT STAGE ===")
        run_chatgpt_stage(once=args.once)
