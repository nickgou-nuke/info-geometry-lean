#!/usr/bin/env python3
import re

with open("tools/infra/automath_pipeline.py", "r") as f:
    content = f.read()

# Find the old SocraticVerifier class
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

# Build new class using string concatenation to avoid quote issues
new_class_lines = []
new_class_lines.append('class SocraticVerifier:')
new_class_lines.append('    """Socratic verifier -- critique + repair via browser-harness (ChatGPT)."""')
new_class_lines.append('')
new_class_lines.append('    def __init__(self):')
new_class_lines.append('        pass')
new_class_lines.append('')
new_class_lines.append('    def critique(self, hypothesis: Hypothesis) -> str:')
new_class_lines.append('        """Run Socratic critique via browser-harness + ChatGPT."""')
new_class_lines.append('        try:')
new_class_lines.append('            prompt = self._build_critique_prompt(hypothesis)')
new_class_lines.append('            with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as f:')
new_class_lines.append('                f.write(prompt)')
new_class_lines.append('                prompt_file = f.name')
new_class_lines.append('            try:')
new_class_lines.append('                env = os.environ.copy()')
new_class_lines.append('                env["CHATGPT_PROMPT_FILE"] = prompt_file')
new_class_lines.append('                env["BU_CDP_WS"] = os.environ.get("BU_CDP_WS", "")')
new_class_lines.append('                env["CHATGPT_URL"] = "https://chatgpt.com/?temporary-chat=true"')
new_class_lines.append('                env["CHATGPT_RESULT_JSON"] = "/tmp/socratic_browser_result.json"')
new_class_lines.append('                env["CHATGPT_TIMEOUT_SECONDS"] = "600"')
new_class_lines.append('                env["CHATGPT_POLL_SECONDS"] = "5"')
new_class_lines.append('')
new_class_lines.append('                result = subprocess.run(')
new_class_lines.append('                    [')
new_class_lines.append('                        "browser-harness", "-c",')
new_class_lines.append('                        f\'import sys; sys.path.insert(0, "{REPO_ROOT}"); ')
new_class_lines.append('                        f\'exec(open("tools/infra/chatgpt_browser_harness_driver.py").read()); _main()\'')
new_class_lines.append('                    ],')
new_class_lines.append('                    cwd=REPO_ROOT,')
new_class_lines.append('                    env={**os.environ, "CHATGPT_PROMPT_FILE": prompt_file, "BU_CDP_WS": os.environ.get("BU_CDP_WS", ""), "CHATGPT_URL": "https://chatgpt.com/?temporary-chat=true", "CHATGPT_RESULT_JSON": "/tmp/socratic_browser_result.json", "CHATGPT_TIMEOUT_SECONDS": "600", "CHATGPT_POLL_SECONDS": "5"},')
new_class_lines.append('                    capture_output=True,')
new_class_lines.append('                    text=True,')
new_class_lines.append('                    timeout=600,')
new_class_lines.append('                )')
new_class_lines.append('')
new_class_lines.append('                result_file = Path("/tmp/socratic_browser_result.json")')
new_class_lines.append('                if result_file.exists():')
new_class_lines.append('                    return result_file.read_text()')
new_class_lines.append('                return result.stdout or "No response"')
new_class_lines.append('            finally:')
new_class_lines.append('                os.unlink(prompt_file)')
new_class_lines.append('        except subprocess.TimeoutExpired:')
new_class_lines.append('            return "Socratic critique timeout (600s)"')
new_class_lines.append('        except Exception as e:')
new_class_lines.append('            return f"Socratic critique error: {e}"')
new_class_lines.append('')
new_class_lines.append('    def _build_critique_prompt(self, hypothesis: Hypothesis) -> str:')
new_class_lines.append('        return f"""Socratic critique of mathematical hypothesis:')
new_class_lines.append('')
new_class_lines.append('HYPOTHESIS: {hypothesis.statement}')
new_class_lines.append('RATIONALE: {hypothesis.rationale}')
new_class_lines.append('OBJECTS: {", ".join(hypothesis.mathematical_objects)}')
new_class_lines.append('SOURCE APEX: {hypothesis.source_apex}')
new_class_lines.append('')
new_class_lines.append('Provide a structured critique:')
new_class_lines.append('1. Mathematical soundness (true/false/uncertain)')
new_class_lines.append('2. Missing assumptions')
new_class_lines.append('3. Potential counterexamples')
new_class_lines.append('4. Suggested formalization approach in Lean 4')
new_class_lines.append('5. Related existing theorems in infogeometry DAG (if known)')
new_class_lines.append('"""')
new_class_lines.append('')
new_class_lines.append('    def repair(self, hypothesis: Hypothesis, lean_errors: str) -> str:')
new_class_lines.append('    """Get repair suggestion via browser-harness + ChatGPT."""')
new_class_lines.append('    try:')
new_class_lines.append('        prompt = f"""Lean 4 compilation errors for hypothesis:')
new_class_lines.append('{hypothesis.statement}')
new_class_lines.append('')
new_class_lines.append('ERRORS:')
new_class_lines.append('{lean_errors}')
new_class_lines.append('')
new_class_lines.append('Provide a concrete repair patch:')
new_class_lines.append('- Identify the exact Lean syntax/type error')
new_class_lines.append('- Suggest the corrected Lean code')
new_class_lines.append('- Explain the mathematical correction')
new_class_lines.append('"""')
new_class_lines.append('            with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as f:')
new_class_lines.append('                f.write(prompt)')
new_class_lines.append('                prompt_file = f.name')
new_class_lines.append('            try:')
new_class_lines.append('                env = os.environ.copy()')
new_class_lines.append('                env["CHATGPT_PROMPT_FILE"] = prompt_file')
new_class_lines.append('                env["BU_CDP_WS"] = os.environ.get("BU_CDP_WS", "")')
new_class_lines.append('                env["CHATGPT_URL"] = "https://chatgpt.com/?temporary-chat=true"')
new_class_lines.append('                env["CHATGPT_RESULT_JSON"] = "/tmp/socratic_browser_result.json"')
new_class_lines.append('                env["CHATGPT_TIMEOUT_SECONDS"] = "600"')
new_class_lines.append('                env["CHATGPT_POLL_SECONDS"] = "5"')
new_class_lines.append('')
new_class_lines.append('                result = subprocess.run(')
new_class_lines.append('                    [')
new_class_lines.append('                        "browser-harness", "-c",')
new_class_lines.append('                        f\'import sys; sys.path.insert(0, "{REPO_ROOT}"); ')
new_class_lines.append('                        f\'exec(open("tools/infra/chatgpt_browser_harness_driver.py").read()); _main()\'')
new_class_lines.append('                    ],')
new_class_lines.append('                    cwd=REPO_ROOT,')
new_class_lines.append('                    env={**os.environ, "CHATGPT_PROMPT_FILE": prompt_file, "BU_CDP_WS": os.environ.get("BU_CDP_WS", ""), "CHATGPT_URL": "https://chatgpt.com/?temporary-chat=true", "CHATGPT_RESULT_JSON": "/tmp/socratic_browser_result.json", "CHATGPT_TIMEOUT_SECONDS": "600", "CHATGPT_POLL_SECONDS": "5"},')
new_class_lines.append('                    capture_output=True,')
new_class_lines.append('                    text=True,')
new_class_lines.append('                    timeout=600,')
new_class_lines.append('                )')
new_class_lines.append('')
new_class_lines.append('                result_file = Path("/tmp/socratic_browser_result.json")')
new_class_lines.append('                if result_file.exists():')
new_class_lines.append('                    return result_file.read_text()')
new_class_lines.append('                return result.stdout or "No response"')
new_class_lines.append('            finally:')
new_class_lines.append('                os.unlink(prompt_file)')
new_class_lines.append('        except subprocess.TimeoutExpired:')
new_class_lines.append('            return "Socratic repair timeout (600s)"')
new_class_lines.append('        except Exception as e:')
new_class_lines.append('            return f"Socratic repair error: {e}"')

new_class = '\n'.join(new_class_lines)

# Read and replace
with open("tools/infra/automath_pipeline.py", "r") as f:
    content = f.read()

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
            return f"Socratic repair error: {e}\"\"\""'''

# Read and replace
with open("tools/infra/automath_pipeline.py", "r") as f:
    content = f.read()

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
            return f"Socratic repair error: {e}\"\"\""'''

# Read and replace
with open("tools/infra/automath_pipeline.py", "r") as f:
    content = f.read()

old = content[content.find('class SocraticVerifier:\n    """Socratic verifier'):content.find('\nclass OracleReferee:', content.find('class SocraticVerifier:'))]

new = '''class SocraticVerifier:
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
            return f"Socratic repair error: {e}\"\"\""'''

content = content.replace(
    content[content.find('class SocraticVerifier:\n    """Socratic verifier'):content.find('\nclass OracleReferee:', content.find('class SocraticVerifier:'))],
    new_class
)

with open("tools/infra/automath_pipeline.py", "w") as f:
    f.write(content)

print("Done!")
