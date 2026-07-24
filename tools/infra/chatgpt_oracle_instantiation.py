#!/usr/bin/env python3
"""
ChatGPT Oracle Browser Harness Instantiation Module

Instantiates the ChatGPT Socratic Oracle client via browser-harness (CDP WebSocket)
connected to the active Chrome DevTools session.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]


class ChatGPTOracleBrowserHarness:
    """Live instantiation of ChatGPT Oracle via browser-harness."""

    def __init__(self, cdp_ws: str | None = None, url: str | None = None):
        self.cdp_ws = cdp_ws or os.environ.get("BU_CDP_WS", "ws://127.0.0.1:38527/devtools/browser")
        self.url = url or "https://chatgpt.com/?temporary-chat=true"
        self.output_json = REPO_ROOT / "artifacts" / "oracle" / "live_instantiation_response.json"
        self.output_json.parent.mkdir(parents=True, exist_ok=True)

    def is_connected(self) -> bool:
        """Check if WebSocket port is reachable."""
        try:
            import asyncio
            import websockets
            async def _test():
                async with websockets.connect(self.cdp_ws):
                    pass
            asyncio.run(_test())
            return True
        except Exception:
            return False

    def query(self, prompt_text: str) -> dict[str, Any]:
        """Send prompt directly to open ChatGPT tab and fetch DOM response."""
        read_code = "(() => { const text = document.body.innerText; const start = text.indexOf('Hypothesis:'); return start !== -1 ? { ok: true, snippet: text.slice(start) } : { ok: true, snippet: text.slice(-600) }; })()"
        script = f"""
import time, json, os

cdp_ws = {json.dumps(self.cdp_ws)}
prompt = {json.dumps(prompt_text)}
read_expr = {json.dumps(read_code)}

print("Connecting browser-harness to CDP:", cdp_ws)
page = new_tab({json.dumps(self.url)})
time.sleep(2)

print("Inserting prompt into #prompt-textarea...")
expr = f'''(() => {{
  const el = document.querySelector('#prompt-textarea') || document.querySelector('div[contenteditable="true"]');
  if (!el) return {{ ok: false, reason: "no input area" }};
  el.focus();
  el.innerHTML = '<p>' + {{json.dumps(prompt)}}.replace(/\\\\n/g, '<br>') + '</p>';
  el.dispatchEvent(new InputEvent('input', {{ bubbles: true, inputType: 'insertText' }}));
  
  const btn = document.querySelector('button[data-testid="send-button"]') || document.querySelector('#composer-submit-button') || document.querySelector('button[aria-label="Send prompt"]');
  if (btn) {{
    btn.disabled = false;
    btn.click();
    return {{ ok: true, btn: true }};
  }}
  return {{ ok: true, btn: false }};
}})()'''

res = js(expr)
print("Insertion & Submit:", res)

print("Waiting 10s for Oracle response...")
time.sleep(10)

out = js(read_expr)
print("ORACLE RESPONSE:", out)
"""

        env = os.environ.copy()
        env["BU_CDP_WS"] = self.cdp_ws

        res = subprocess.run(
            ["/home/goutev/.local/bin/browser-harness"],
            input=script,
            cwd=REPO_ROOT,
            env=env,
            capture_output=True,
            text=True,
            timeout=120,
        )

        result_data = {
            "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "cdp_ws": self.cdp_ws,
            "stdout": res.stdout,
            "stderr": res.stderr,
            "success": res.returncode == 0,
        }

        self.output_json.write_text(json.dumps(result_data, indent=2), encoding="utf-8")
        return result_data


def main():
    oracle = ChatGPTOracleBrowserHarness()
    print("⚡ Instantiating ChatGPT Oracle via browser-harness...")
    print(f"   CDP WebSocket: {oracle.cdp_ws}")
    print(f"   Connection Active: {oracle.is_connected()}")

    test_prompt = """Hypothesis: Bost-Connes Partition Function Divergence
Rationale: Zeta function non-summability at beta = 1 forces phase transition across UHF colimit.
Apex: InfoGeometry.Canonical.BCPartitionFunction.bc_partition_divergence_at_one

Please audit this formal intent and provide your verdict (BREAKTHROUGH / MINOR / REJECT) with a one-line mathematical rationale."""

    res = oracle.query(test_prompt)
    print("\n📜 Execution Response:")
    print("=" * 60)
    print(res["stdout"])
    print("=" * 60)


if __name__ == "__main__":
    main()
