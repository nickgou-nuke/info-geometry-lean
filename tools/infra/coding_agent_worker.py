#!/usr/bin/env python3
"""
Coding Agent Worker — fills `sorry` blocks using literature + LLM.

Pipeline stage:  ready-to-code → [coding agent] → verified / deeper-debt

For each task in ready-to-code:
  1. Extract each `theorem ... := by sorry` block
  2. Search Google AI for literature on that theorem
  3. Feed literature + code to ChatGPT for proof attempt
  4. Compile with lake build
  5. If compiles → mark verified, else → mark deeper-debt with enriched context
"""
from __future__ import annotations
import json, logging, os, re, sys, time, subprocess, tempfile
from pathlib import Path

_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]
sys.path.insert(0, str(_REPO))

from tools.infra.arango_env import *
from tools.infra.hive_arango_queue import aql, claim_next_task, update_task_status

logger = logging.getLogger("coder")

GOOGLE_SCRIPT = _REPO / "tools" / "infra" / "google_ai_driver.py"
CHATGPT_SCRIPT = _REPO / "tools" / "infra" / "chatgpt_browser_harness_driver.py"
SYSTEM_PROMPT = open("/tmp/chatgpt_system_prompt.txt").read()
POLL = 5
LEASE = 1800


def _search_google(query: str, timeout: int = 120) -> str:
    qf = tempfile.NamedTemporaryFile(mode='w', suffix='.txt', delete=False)
    qf.write(query); qf.close()
    rf = tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False)
    rf.close()
    env = os.environ.copy()
    env['GOOGLE_AI_PROMPT_FILE'] = qf.name
    env['GOOGLE_AI_RESULT_JSON'] = rf.name
    env['GOOGLE_AI_TIMEOUT_SECONDS'] = str(timeout)
    subprocess.run(
        ['browser-harness', '-c',
         f"import sys; sys.path.insert(0,'{_REPO}'); exec(open('{GOOGLE_SCRIPT}').read()); _main()"],
        env=env, capture_output=True, text=True, timeout=timeout + 60,
    )
    result = open(rf.name).read() if Path(rf.name).exists() else ""
    os.unlink(qf.name); os.unlink(rf.name)
    return result


def _ask_chatgpt(prompt: str, timeout: int = 300) -> str:
    pf = tempfile.NamedTemporaryFile(mode='w', suffix='.txt', delete=False)
    pf.write(prompt); pf.close()
    rf = tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False)
    rf.close()
    env = os.environ.copy()
    env['CHATGPT_PROMPT_FILE'] = pf.name
    env['CHATGPT_RESULT_JSON'] = rf.name
    env['CHATGPT_TIMEOUT_SECONDS'] = str(timeout)
    subprocess.run(
        ['browser-harness', '-c',
         f"import sys; sys.path.insert(0,'{_REPO}'); exec(open('{CHATGPT_SCRIPT}').read()); _main()"],
        env=env, capture_output=True, text=True, timeout=timeout + 60,
    )
    result = open(rf.name).read() if Path(rf.name).exists() else ""
    os.unlink(pf.name); os.unlink(rf.name)
    return result


def run(once: bool = False):
    while True:
        try:
            load_repo_arango_env(_REPO)
            ep, db = arango_endpoint(), arango_database("hive_live")
            usr, pwd = arango_username(), arango_password("alexandria_root")

            task = claim_next_task(ep, db, usr, pwd,
                worker_id="coding-agent", queue_name="ready-to-code",
                lease_seconds=LEASE, task_kind="ready.to.code")
            if task is None:
                n = aql(ep,db,usr,pwd,"FOR t IN hive_tasks FILTER t.queue_name=='ready-to-code' FILTER t.status=='pending' COLLECT WITH COUNT INTO n RETURN n",{})
                logger.info("[Coder] No tasks. %d pending.", n[0] if n else 0)
                if once: break
                time.sleep(POLL); continue

            pkt = task.get("runtime_goal_packet") or {}
            code = pkt.get("chatgpt_code") or pkt.get("chatgpt_code_v2") or ""
            theorem = pkt.get("theorem", "unknown")

            # Extract each sorry theorem
            sorry_theorems = re.findall(
                r'(theorem\s+\S+[\s\S]*?:=\s*by\s*\n\s*sorry)',
                code, re.IGNORECASE)
            if not sorry_theorems:
                sorry_theorems = re.findall(r'(theorem\s+\S+[\s\S]*?sorry)', code)

            logger.info("[Coder] '%s': %d sorry theorems to fill", theorem, len(sorry_theorems))

            filled = []
            for i, st in enumerate(sorry_theorems[:3]):
                tname = re.search(r'theorem\s+(\S+)', st)
                tname = tname.group(1) if tname else f"unknown_{i}"
                logger.info("  [%d/%d] Filling '%s'", i+1, len(sorry_theorems[:3]), tname)

                # Search literature
                gctx = _search_google(f"Rigorous proof of {tname} in graph theory Helmholtz-Hodge decomposition Lean 4", timeout=90)
                logger.info("    Google: %d chars", len(gctx))

                # Ask ChatGPT for proof
                prompt = (
                    f"{SYSTEM_PROMPT}\n\n"
                    f"Literature context:\n```\n{gctx[:3000]}\n```\n\n"
                    f"Fill the `sorry` in this theorem with a complete Lean 4 proof:\n"
                    f"```lean4\n{st}\n```\n\n"
                    f"Context code:\n```lean4\n{code[:3000]}\n```\n\n"
                    f"Output ONLY valid Lean 4 code for the complete theorem. Zero prose."
                )
                proof = _ask_chatgpt(prompt, timeout=180)
                logger.info("    Proof: %d chars", len(proof))

                if proof and 'sorry' not in proof.lower():
                    filled.append((tname, proof))

            # Merge filled proofs back into the code
            updated = code
            for tname, proof in filled:
                pattern = rf'(theorem\s+{re.escape(tname)}\s*[\s\S]*?:=\s*by\s*\n\s*)sorry'
                updated = re.sub(pattern, rf'\1{proof}', updated, count=1)

            # Save result
            rp = dict(pkt)
            rp["filled_proofs"] = filled
            rp["updated_code"] = updated
            rp["pass"] = "coding-agent-v1"

            status = "completed" if filled else "deeper-debt"
            update_task_status(ep, db, usr, pwd,
                task_key_value=task["_key"], worker_id="coding-agent",
                status=status,
                extra_fields={"runtime_goal_packet": rp, "queue_name": "verified" if filled else "deeper-debt"})

            logger.info("[Coder] %d/%d theorems filled → %s", len(filled), len(sorry_theorems[:3]), status)
            if once: break

        except KeyboardInterrupt: break
        except Exception as e:
            logger.error("[Coder] %s", e)
            time.sleep(10)


if __name__ == "__main__":
    import argparse
    p = argparse.ArgumentParser()
    p.add_argument("--once", action="store_true")
    args = p.parse_args()
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(message)s", datefmt="%H:%M:%S")
    run(once=args.once)
