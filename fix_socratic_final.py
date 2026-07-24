#!/usr/bin/env python3
import re

with open("tools/infra/automath_pipeline.py", "r") as f:
    content = f.read()

# Find the old SocraticVerifier class
match = re.search(r'(class SocraticVerifier:.*?)(?=\nclass \w+:)', content, re.DOTALL)
if not match:
    print("ERROR: Could not find SocraticVerifier class")
    exit(1)

old_class = match.group(0)
print(f"Found old class, length: {len(old_class)}")

# Build new class without triple quotes in the script
new_class = 'class SocraticVerifier:\n'
new_class += '    """Socratic verifier -- critique + repair via browser-harness (ChatGPT)."""\n\n'
new_class += '    def __init__(self):\n'
new_class += '        pass\n\n'
new_class += '    def critique(self, hypothesis: Hypothesis) -> str:\n'
new_class += '        """Run Socratic critique via browser-harness + ChatGPT."""\n'
new_class += '        try:\n'
new_class += '            prompt = self._build_critique_prompt(hypothesis)\n'
new_class += '            with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as f:\n'
new_class += '                f.write(prompt)\n'
new_class += '                prompt_file = f.name\n'
new_class += '            try:\n'
new_class += '                env = os.environ.copy()\n'
new_class += '                env["CHATGPT_PROMPT_FILE"] = prompt_file\n'
new_class += '                env["BU_CDP_WS"] = os.environ.get("BU_CDP_WS", "")\n'
new_class += '                env["CHATGPT_URL"] = "https://chatgpt.com/?temporary-chat=true"\n'
new_class += '                env["CHATGPT_RESULT_JSON"] = "/tmp/socratic_browser_result.json"\n'
new_class += '                env["CHATGPT_TIMEOUT_SECONDS"] = "600"\n'
new_class += '                env["CHATGPT_POLL_SECONDS"] = "5"\n\n'
new_class += '                result = subprocess.run(\n'
new_class += '                    [\n'
new_class += '                        "browser-harness", "-c",\n'
new_class += '                        f\'import sys; sys.path.insert(0, "{REPO_ROOT}"); '\n'
new_class += '                        f\'exec(open("tools/infra/chatgpt_browser_harness_driver.py").read()); _main()\'\n'
new_class += '                    ],\n'
new_class += '                    cwd=REPO_ROOT,\n'
new_class += '                    env={**os.environ, "CHATGPT_PROMPT_FILE": prompt_file, "BU_CDP_WS": os.environ.get("BU_CDP_WS", ""), "CHATGPT_URL": "https://chatgpt.com/?temporary-chat=true", "CHATGPT_RESULT_JSON": "/tmp/socratic_browser_result.json", "CHATGPT_TIMEOUT_SECONDS": "600", "CHATGPT_POLL_SECONDS": "5"},\n'
new_class += '                    capture_output=True,\n'
new_class += '                    text=True,\n'
new_class += '                    timeout=600,\n'
new_class += '                )\n\n'
new_class += '                result_file = Path("/tmp/socratic_browser_result.json")\n'
new_class += '                if result_file.exists():\n'
new_class += '                    return result_file.read_text()\n'
new_class += '                return result.stdout or "No response"\n'
new_class += '            finally:\n'
new_class += '                os.unlink(prompt_file)\n'
new_class += '        except subprocess.TimeoutExpired:\n'
new_class += '            return "Socratic critique timeout (600s)"\n'
new_class += '        except Exception as e:\n'
new_class += '            return f"Socratic critique error: {e}"\n\n'
new_class += '    def _build_critique_prompt(self, hypothesis: Hypothesis) -> str:\n'
new_class += '        return f"""Socratic critique of mathematical hypothesis:\n\n'
new_class += 'HYPOTHESIS: {hypothesis.statement}\n'
new_class += 'RATIONALE: {hypothesis.rationale}\n'
new_class += 'OBJECTS: {", ".join(hypothesis.mathematical_objects)}\n'
new_class += 'SOURCE APEX: {hypothesis.source_apex}\n\n'
new_class += 'Provide a structured critique:\n'
new_class += '1. Mathematical soundness (true/false/uncertain)\n'
new_class += '2. Missing assumptions\n'
new_class += '3. Potential counterexamples\n'
new_class += '4. Suggested formalization approach in Lean 4\n'
new_class += '5. Related existing theorems in infogeometry DAG (if known)\n'
new_class += '"""\n\n'
new_class += '    def repair(self, hypothesis: Hypothesis, lean_errors: str) -> str:\n'
new_class += '        """Get repair suggestion via browser-harness + ChatGPT."""\n'
new_class += '        try:\n'
new_class += '            prompt = f"""Lean 4 compilation errors for hypothesis:\n{hypothesis.statement}\n\n'
new_class += 'ERRORS:\n{lean_errors}\n\n'
new_class += 'Provide a concrete repair patch:\n'
new_class += '- Identify the exact Lean syntax/type error\n'
new_class += '- Suggest the corrected Lean code\n'
new_class += '- Explain the mathematical correction\n'
new_class += '"""\n'
new_class += '            with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as f:\n'
new_class += '                f.write(prompt)\n'
new_class += '                prompt_file = f.name\n'
new_class += '            try:\n'
new_class += '                env = os.environ.copy()\n'
new_class += '                env["CHATGPT_PROMPT_FILE"] = prompt_file\n'
new_class += '                env["BU_CDP_WS"] = os.environ.get("BU_CDP_WS", "")\n'
new_class += '                env["CHATGPT_URL"] = "https://chatgpt.com/?temporary-chat=true"\n'
new_class += '                env["CHATGPT_RESULT_JSON"] = "/tmp/socratic_browser_result.json"\n'
new_class += '                env["CHATGPT_TIMEOUT_SECONDS"] = "600"\n'
new_class += '                env["CHATGPT_POLL_SECONDS"] = "5"\n\n'
new_class += '                result = subprocess.run(\n'
new_class += '                    [\n'
new_class += '                        "browser-harness", "-c",\n'
new_class += '                        f\'import sys; sys.path.insert(0, "{REPO_ROOT}"); '\n'
new_class += '                        f\'exec(open("tools/infra/chatgpt_browser_harness_driver.py").read()); _main()\'\n'
new_class += '                    ],\n'
new_class += '                    cwd=REPO_ROOT,\n'
new_class += '                    env={**os.environ, "CHATGPT_PROMPT_FILE": prompt_file, "BU_CDP_WS": os.environ.get("BU_CDP_WS", ""), "CHATGPT_URL": "https://chatgpt.com/?temporary-chat=true", "CHATGPT_RESULT_JSON": "/tmp/socratic_browser_result.json", "CHATGPT_TIMEOUT_SECONDS": "600", "CHATGPT_POLL_SECONDS": "5"},\n'
new_class += '                    capture_output=True,\n'
new_class += '                    text=True,\n'
new_class += '                    timeout=600,\n'
new_class += '                )\n\n'
new_class += '                result_file = Path("/tmp/socratic_browser_result.json")\n'
new_class += '                if result_file.exists():\n'
new_class += '                    return result_file.read_text()\n'
new_class += '                return result.stdout or "No response"\n'
new_class += '            finally:\n'
new_class += '                os.unlink(prompt_file)\n'
new_class += '        except subprocess.TimeoutExpired:\n'
new_class += '            return "Socratic repair timeout (600s)"\n'
new_class += '        except Exception as e:\n'
new_class += '            return f"Socratic repair error: {e}""""\n'

# Read and replace
with open("tools/infra/automath_pipeline.py", "r") as f:
    content = f.read()

# Find and replace
old_pattern = r'class SocraticVerifier:.*?(?=\nclass \w+:)'
new_content = re.sub(r'class SocraticVerifier:.*?(?=\nclass \w+:)', 
    '''class SocraticVerifier:
    """Socratic verifier -- critique + repair via browser-harness (ChatGPT)."""

    def __init__(self):
        pass

    def critique(self, hypothesis: Hypothesis) -> str:
        """Run Socratic critique via browser-harness + ChatGPT."""
        try:
            prompt = self._build_critique_prompt(hypothesis)
            with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as f:
                f.write(prompt)
                prompt_file = f.name
            try:
                env = os.environ.copy()
                env["CHATGPT_PROMPT_FILE"] = prompt_file
                env["BU_CDP_WS"] = os.environ.get("BU_CDP_WS", "")
                env["CHATGPT_URL"] = "https://chatgpt.com/?temporary-chat=true"
                env["CHATGPT_RESULT_JSON"] = "/tmp/socratic_browser_result.json"
                env["CHATGPT_TIMEOUT_SECONDS"] = "600"
                env["CHATGPT_POLL_SECONDS"] = "5"

                result = subprocess.run(
                    [
                        "browser-harness", "-c",
                        f'import sys; sys.path.insert(0, "{REPO_ROOT}"); '
                        f'exec(open("tools/infra/chatgpt_browser_harness_driver.py").read()); _main()'
                    ],
                    cwd=REPO_ROOT,
                    env={**os.environ, "CHATGPT_PROMPT_FILE": prompt_file, "BU_CDP_WS": os.environ.get("BU_CDP_WS", ""), "CHATGPT_URL": "https://chatgpt.com/?temporary-chat=true", "CHATGPT_RESULT_JSON": "/tmp/socratic_browser_result.json", "CHATGPT_TIMEOUT_SECONDS": "600", "CHATGPT_POLL_SECONDS": "5"},
                    capture_output=True,
                    text=True,
                    timeout=600,
                )

                result_file = Path("/tmp/socratic_browser_result.json")
                if result_file.exists():
                    return result_file.read_text()
                return result.stdout or "No response"
            finally:
                os.unlink(prompt_file)
        except subprocess.TimeoutExpired:
            return "Socratic critique timeout (600s)"
        except Exception as e:
            return f"Socratic critique error: {e}"

    def _build_critique_prompt(self, hypothesis: Hypothesis) -> str:
        return f"""Socratic critique of mathematical hypothesis:

HYPOTHESIS: {hypothesis.statement}
RATIONALE: {hypothesis.rationale}
OBJECTS: {", ".join(hypothesis.mathematical_objects)}
SOURCE APEX: {hypothesis.source_apex}

Provide a structured critique:
1. Mathematical soundness (true/false/uncertain)
2. Missing assumptions
3. Potential counterexamples
4. Suggested formalization approach in Lean 4
5. Related existing theorems in infogeometry DAG (if known)
"""

    def repair(self, hypothesis: Hypothesis, lean_errors: str) -> str:
        """Get repair suggestion via browser-harness + ChatGPT."""
        try:
            prompt = f"""Lean 4 compilation errors for hypothesis:
{hypothesis.statement}

ERRORS:
{lean_errors}

Provide a concrete repair patch:
- Identify the exact Lean syntax/type error
- Suggest the corrected Lean code
- Explain the mathematical correction
"""
            with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as f:
                f.write(prompt)
                prompt_file = f.name
            try:
                env = os.environ.copy()
                env["CHATGPT_PROMPT_FILE"] = prompt_file
                env["BU_CDP_WS"] = os.environ.get("BU_CDP_WS", "")
                env["CHATGPT_URL"] = "https://chatgpt.com/?temporary-chat=true"
                env["CHATGPT_RESULT_JSON"] = "/tmp/socratic_browser_result.json"
                env["CHATGPT_TIMEOUT_SECONDS"] = "600"
                env["CHATGPT_POLL_SECONDS"] = "5"

                result = subprocess.run(
                    [
                        "browser-harness", "-c",
                        f'import sys; sys.path.insert(0, "{REPO_ROOT}"); '
                        f'exec(open("tools/infra/chatgpt_browser_harness_driver.py").read()); _main()'
                    ],
                    cwd=REPO_ROOT,
                    env={**os.environ, "CHATGPT_PROMPT_FILE": prompt_file, "BU_CDP_WS": os.environ.get("BU_CDP_WS", ""), "CHATGPT_URL": "https://chatgpt.com/?temporary-chat=true", "CHATGPT_RESULT_JSON": "/tmp/socratic_browser_result.json", "CHATGPT_TIMEOUT_SECONDS": "600", "CHATGPT_POLL_SECONDS": "5"},
                    capture_output=True,
                    text=True,
                    timeout=600,
                )

                result_file = Path("/tmp/socratic_browser_result.json")
                if result_file.exists():
                    return result_file.read_text()
                return result.stdout or "No response"
            finally:
                os.unlink(prompt_file)
        except subprocess.TimeoutExpired:
            return "Socratic repair timeout (600s)"
        except Exception as e:
            return f"Socratic repair error: {e}""",
    content, flags=re.DOTALL)

if content == new_content:
    print("WARNING: No replacement made!")
else:
    with open("tools/infra/automath_pipeline.py", "w") as f:
        f.write(new_content)
    print("Done!")
