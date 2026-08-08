import time
import base64

js("location.reload();")
print("Reloading page to clear previous state...")
time.sleep(5)

prompt_text = """[*] Querying AST topological DAG for 'FilteredColimit'...
[*] Querying AST topological DAG for 'FibAnyon'...

[+] Assembled Contextual Prompt for the Oracle:

You are the Intuition Oracle for an Automath pipeline.
Your job is to propose a rigorous mathematical hypothesis and its Lean 4 implementation.
Do not hallucinate external dependencies. You must strictly align with the provided causal cone.

=== EXTRACTED CAUSAL CONE ===

Declaration: InfiniteLightConeConfColimit.AnalyticColimitComparisonSocket.deRhamCommutesWithFilteredColimit
----------------------------------------
Declaration: InfiniteLightConeConfColimit.deRhamCommutesWithFilteredColimit
----------------------------------------


No direct formalizations found in the DAG for 'FibAnyon'. We are at the frontier.

=== YOUR GOAL ===
Formulate the Pentagon Identity for Fibonacci Anyons within the existing Filtered Colimit structure.

Provide only the valid Lean 4 code to implement this hypothesis. The pipeline will test your code natively."""
encoded_prompt = base64.b64encode(prompt_text.encode('utf-8')).decode('utf-8')

js_code = f"""
(() => {{
  const decoded = decodeURIComponent(escape(window.atob('{encoded_prompt}')));
  const el = document.querySelector('#prompt-textarea');
  if (el) {{
      el.focus();
      document.execCommand('insertText', false, decoded);
  }} else {{
      console.error("Could not find #prompt-textarea");
  }}
}})();
"""
js(js_code)

time.sleep(1)
js("const btn = document.querySelector('button[data-testid=\"send-button\"]'); if(btn) btn.click();")
print("Prompt sent successfully!")
