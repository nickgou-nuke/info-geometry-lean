#!/usr/bin/env python3
import sys
import base64
import subprocess
import time
from pathlib import Path

def generate_oracle_prompt(context_files, goal):
    prompt = "You are the Intuition Oracle for an Automath pipeline.\n"
    prompt += "Your job is to propose a rigorous mathematical hypothesis and its Lean 4 implementation.\n"
    prompt += "Do not hallucinate external dependencies. You must strictly align with the provided causal cone.\n\n"
    prompt += "=== CAUSAL CONE (EXACT SOURCE CONTEXT) ===\n\n"
    
    for file_path in context_files:
        p = Path(file_path)
        if p.exists():
            prompt += f"--- {p.name} ---\n"
            prompt += p.read_text() + "\n\n"
        else:
            print(f"[-] Warning: Context file {file_path} not found.")

    prompt += "=== YOUR GOAL ===\n"
    prompt += goal + "\n\n"
    prompt += "Provide only the valid Lean 4 code to implement this hypothesis. The pipeline will test your code natively.\n"
    return prompt

def inject_via_browser_harness(prompt_text):
    print("[*] Base64 encoding prompt to bypass ProseMirror DOM restrictions...")
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

    bh_script = f"""
import time
new_tab("https://chatgpt.com")
print("[*] Waiting for ChatGPT to load...")
time.sleep(4)

print("[*] Injecting Contextual Causal Cone into Oracle...")
js(\"\"\"{js_code}\"\"\")

time.sleep(1)
js("(() => {{ const btn = document.querySelector('button[data-testid=\\"send-button\\"]'); if(btn) btn.click(); }})();")
print("[+] Context successfully submitted to the Oracle!")
"""
    
    print("[*] Launching browser-harness...")
    process = subprocess.Popen(['browser-harness'], stdin=subprocess.PIPE, text=True)
    process.communicate(input=bh_script)

def main():
    if len(sys.argv) < 3:
        print("Usage: python socratic_pipeline.py <goal_string> <context_file_1> [context_file_2 ...]")
        sys.exit(1)

    goal = sys.argv[1]
    context_files = sys.argv[2:]

    print(f"[*] Assembling Causal Cone from {len(context_files)} files...")
    prompt = generate_oracle_prompt(context_files, goal)
    
    inject_via_browser_harness(prompt)
    print("\n[+] Socratic Injection Complete.")
    print("[!] Await the Oracle's response in your browser.")
    print("[!] Save the generated code to a .lean file and run 'lake env lean <file.lean>' to verify in the Crucible.")

if __name__ == "__main__":
    main()
