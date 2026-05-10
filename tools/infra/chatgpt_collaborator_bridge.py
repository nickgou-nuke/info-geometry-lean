#!/usr/bin/env python3
import subprocess
import argparse
import sys
import json

def ask_chatgpt(prompt_text):
    with open('/tmp/chatgpt_prompt.txt', 'w') as f:
        f.write(prompt_text)
    
    harness_script = """
import json
with open('/tmp/chatgpt_prompt.txt', 'r') as f:
    text = f.read()

safe_prompt = json.dumps(text)

# Use the currently active tab where the user is already logged in and ready
ensure_real_tab()

# Target the main chat input
# ChatGPT uses a contenteditable div
js(f'''
var el = document.getElementById("prompt-textarea");
el.innerHTML = "";
el.innerText = {safe_prompt};
el.dispatchEvent(new Event("input", {{ bubbles: true }}));
''')

wait(1)
js('document.querySelector(\\'button[data-testid="send-button"]\\').click()')

# Wait for the generation to complete. 
print("Waiting for generation to finish...")
wait(5)
wait_for_element('button[data-testid="send-button"]', timeout=180, visible=True)

# Extract the last assistant message
script = '''
var responses = document.querySelectorAll('div[data-message-author-role="assistant"]');
if (responses.length > 0) {
    responses[responses.length - 1].innerText;
} else {
    "ERROR: Could not extract response from the DOM.";
}
'''
response_text = js(script)
print("--- CHATGPT RESPONSE ---")
print(response_text)
"""
    try:
        result = subprocess.run(
            ["browser-harness", "-c", harness_script],
            capture_output=True,
            text=True,
            check=True
        )
        return result.stdout
    except subprocess.CalledProcessError as e:
        print(f"Browser harness failed to communicate with ChatGPT: {e.stderr}", file=sys.stderr)
        return None

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Delegate a complex auditing task to ChatGPT via Browser Harness.")
    parser.add_argument("prompt", help="The prompt or code to send to ChatGPT")
    args = parser.parse_args()
    
    response = ask_chatgpt(args.prompt)
    if response:
        print(response)