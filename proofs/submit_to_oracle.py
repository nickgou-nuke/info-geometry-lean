import time
new_tab("https://chatgpt.com")
print("Waiting for page load...")
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
safe_prompt = prompt_text.replace('\n', '\n').replace('"', '\"')

print("Injecting prompt into ChatGPT UI...")
js(f'document.querySelector("#prompt-textarea").innerHTML = "<p>" + "{safe_prompt}" + "</p>"')
time.sleep(1)
js('document.querySelector("button[data-testid=\"send-button\"]").click()')
print("Prompt sent!")
