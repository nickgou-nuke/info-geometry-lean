#!/usr/bin/env python3
import re

with open("tools/infra/automath_pipeline.py", "r") as f:
    content = f.read()

# Find old class
old_start = content.find('class SocraticVerifier:\n    """Socratic verifier')
if old_start == -1:
    print("ERROR: Could not find old class")
    exit(1)

old_end = content.find('\nclass OracleReferee:', content.find('class SocraticVerifier:'))
if old_end == -1:
    old_end = content.find('\nclass HiveSync:', content.find('class SocraticVerifier:'))
if old_end == -1:
    old_end = len(content)

old_class = content[old_start:old_end]
print(f"Old class length: {len(old_class)}")

new_class = (
    'class SocraticVerifier:\n'
    '    """Socratic verifier -- critique + repair via browser-harness (ChatGPT)."""\n\n'
    '    def __init__(self):\n'
    '        pass\n\n'
    '    def critique(self, hypothesis: Hypothesis) -> str:\n'
    '        """Run Socratic critique via browser-harness + ChatGPT."""\n'
    '        try:\n'
    '            prompt = self._build_critique_prompt(hypothesis)\n'
    '            with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as f:\n'
    '                f.write(prompt)\n'
    '                prompt_file = f.name\n'
    '            try:\n'
    '                env = os.environ.copy()\n'
    '                env["CHATGPT_PROMPT_FILE"] = prompt_file\n'
    '                env["BU_CDP_WS"] = os.environ.get("BU_CDP_WS", "")\n'
    '                env["CHATGPT_URL"] = "https://chatgpt.com/?temporary-chat=true"\n'
    '                env["CHATGPT_RESULT_JSON"] = "/tmp/socratic_browser_result.json"\n'
    '                env["CHATGPT_TIMEOUT_SECONDS"] = "600"\n'
    '                env["CHATGPT_POLL_SECONDS"] = "5"\n\n'
    '                result = subprocess.run(\n'
    '                    [\n'
    '                        "browser-harness", "-c",\n'
    '                        f\'import sys; sys.path.insert(0, "{REPO_ROOT}"); '
    '                        f\'exec(open("tools/infra/chatgpt_browser_harness_driver.py").read()); _main()\'\n'
    '                    ],\n'
    '                    cwd=REPO_ROOT,\n'
    '                    env={**os.environ, "CHATGPT_PROMPT_FILE": prompt_file, "BU_CDP_WS": os.environ.get("BU_CDP_WS", ""), "CHATGPT_URL": "https://chatgpt.com/?temporary-chat=true", "CHATGPT_RESULT_JSON": "/tmp/socratic_browser_result.json", "CHATGPT_TIMEOUT_SECONDS": "600", "CHATGPT_POLL_SECONDS": "5"},\n'
    '                    capture_output=True,\n'
    '                    text=True,\n'
    '                    timeout=600,\n'
    '                )\n\n'
    '                result_file = Path("/tmp/socratic_browser_result.json")\n'
    '                if result_file.exists():\n'
    '                    return result_file.read_text()\n'
    '                return result.stdout or "No response"\n'
    '            finally:\n'
    '                os.unlink(prompt_file)\n'
    '        except subprocess.TimeoutExpired:\n'
    '            return "Socratic critique timeout (600s)"\n'
    '        except Exception as e:\n'
    '            return f"Socratic critique error: {e}"\n\n'
    '    def _build_critique_prompt(self, hypothesis: Hypothesis) -> str:\n'
    '        return f"""Socratic critique of mathematical hypothesis:\n\n'
    'HYPOTHESIS: {hypothesis.statement}\n'
    'RATIONALE: {hypothesis.rationale}\n'
    'OBJECTS: {", ".join(hypothesis.mathematical_objects)}\n'
    'SOURCE APEX: {hypothesis.source_apex}\n\n'
    'Provide a structured critique:\n'
    '1. Mathematical soundness (true/false/uncertain)\n'
    '2. Missing assumptions\n'
    '3. Potential counterexamples\n'
    '4. Suggested formalization approach in Lean 4\n'
    '5. Related existing theorems in infogeometry DAG (if known)\n'
    '"""\n\n'
    '    def repair(self, hypothesis: Hypothesis, lean_errors: str) -> str:\n'
    '        """Get repair suggestion via browser-harness + ChatGPT."""\n'
    '        try:\n'
    '            prompt = f"""Lean 4 compilation errors for hypothesis:\n{hypothesis.statement}\n\n'
    'ERRORS:\n{lean_errors}\n\n'
    'Provide a concrete repair patch:\n'
    '- Identify the exact Lean syntax/type error\n'
    '- Suggest the corrected Lean code\n'
    '- Explain the mathematical correction\n'
    '"""\n'
    '            with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as f:\n'
    '                f.write(prompt)\n'
    '                prompt_file = f.name\n'
    '            try:\n'
    '                env = os.environ.copy()\n'
    '                env["CHATGPT_PROMPT_FILE"] = prompt_file\n'
    '                env["BU_CDP_WS"] = os.environ.get("BU_CDP_WS", "")\n'
    '                env["CHATGPT_URL"] = "https://chatgpt.com/?temporary-chat=true"\n'
    '                env["CHATGPT_RESULT_JSON"] = "/tmp/socratic_browser_result.json"\n'
    '                env["CHATGPT_TIMEOUT_SECONDS"] = "600"\n'
    '                env["CHATGPT_POLL_SECONDS"] = "5"\n\n'
    '                result = subprocess.run(\n'
    '                    [\n'
    '                        "browser-harness", "-c",\n'
    '                        f\'import sys; sys.path.insert(0, "{REPO_ROOT}"); '
    '                        f\'exec(open("tools/infra/chatgpt_browser_harness_driver.py").read()); _main()\'\n'
    '                    ],\n'
    '                    cwd=REPO_ROOT,\n'
    '                    env={**os.environ, "CHATGPT_PROMPT_FILE": prompt_file, "BU_CDP_WS": os.environ.get("BU_CDP_WS", ""), "CHATGPT_URL": "https://chatgpt.com/?temporary-chat=true", "CHATGPT_RESULT_JSON": "/tmp/socratic_browser_result.json", "CHATGPT_TIMEOUT_SECONDS": "600", "CHATGPT_POLL_SECONDS": "5"},\n'
    '                    capture_output=True,\n'
    '                    text=True,\n'
    '                    timeout=600,\n'
    '                )\n\n'
    '                result_file = Path("/tmp/socratic_browser_result.json")\n'
    '                if result_file.exists():\n'
    '                    return result_file.read_text()\n'
    '                return result.stdout or "No response"\n'
    '            finally:\n'
    '                os.unlink(prompt_file)\n'
    '        except subprocess.TimeoutExpired:\n'
    '            return "Socratic repair timeout (600s)"\n'
    '        except Exception as e:\n'
    '            return f"Socratic repair error: {e}""""\n')

with open("tools/infra/automath_pipeline.py", "r") as f:
    content = f.read()

old = content[content.find('class SocraticVerifier:\n    """Socratic verifier'):content.find('\nclass OracleReferee:', content.find('class SocraticVerifier:'))]

new_class = '''class SocraticVerifier:
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
                        f\'import sys; sys.path.insert(0, "{REPO_ROOT}"); \'
                        f\'exec(open("tools/infra/chatgpt_browser_harness_driver.py").read()); _main()\'
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
                        f\'import sys; sys.path.insert(0, "{REPO_ROOT}"); \'
                        f\'exec(open("tools/infra/chatgpt_browser_harness_driver.py").read()); _main()\'
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
            return f"Socratic repair error: {e}\"\"\""'''

with open("tools/infra/automath_pipeline.py", "r") as f:
    content = f.read()

old = content[content.find('class SocraticVerifier:\n    """Socratic verifier'):content.find('\nclass OracleReferee:', content.find('class SocraticVerifier:'))]

new_class = '''class SocraticVerifier:
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
                        f\'import sys; sys.path.insert(0, "{REPO_ROOT}"); \'
                        f\'exec(open("tools/infra/chatgpt_browser_harness_driver.py").read()); _main()\'
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
            return f"Socratic repair error: {e}\"\"\""'''

with open("tools/infra/automath_pipeline.py", "r") as f:
    content = f.read()

old = content[content.find('class SocraticVerifier:\n    """Socratic verifier'):content.find('\nclass OracleReferee:', content.find('class SocraticVerifier:'))]

content = content[:content.find('class SocraticVerifier:\n    """Socratic verifier')] + new_class + content[content.find('\nclass OracleReferee:', content.find('class SocraticVerifier:')):]

with open("tools/infra/automath_pipeline.py", "w") as f:
    f.write(content)

print("Done!")
