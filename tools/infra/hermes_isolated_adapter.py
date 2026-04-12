#!/usr/bin/env python3
import os
import shutil
import subprocess
import json
import sys
import yaml
from pathlib import Path

"""
# Isolated Hermes Adapter (Asymmetric Edition)
Orchestrates the sandboxed execution of Lean 4 proof tasks using 
asymmetric Proposer/Formalizer models on DGX Spark.
"""

def setup_sandbox(sandbox_path, constitution_path):
    if sandbox_path.exists():
        shutil.rmtree(sandbox_path)
    sandbox_path.mkdir(parents=True)
    
    # Configure Asymmetric Dispatch for DGX Spark
    # Port 8000: Qwen3-32B (Proposer)
    # Port 8001: DeepSeek-Prover-V2-7B (Formalizer)
    config_content = {
        "model": {
            "provider": "custom",
            "base_url": "http://localhost:8000/v1", # Default to Proposer
            "api_key": "ollama",
            "default": "qwen3-32b-fp8"
        },
        "agents": {
            "proposer": {
                "base_url": "http://localhost:8000/v1",
                "model": "qwen3-32b-fp8"
            },
            "formalizer": {
                "base_url": "http://localhost:8001/v1",
                "model": "deepseek-prover-v2-7b"
            }
        },
        "persistence": {
            "memory_enabled": False,
            "skills_enabled": True
        }
    }
    
    config_path = sandbox_path / "config.yaml"
    with open(config_path, "w") as f:
        yaml.dump(config_content, f)

    # Inject the Constitution as a Skill
    skills_dir = sandbox_path / "skills"
    skills_dir.mkdir()
    shutil.copy(constitution_path, skills_dir / "lean-formalizer.md")

def check_backends():
    import requests
    endpoints = ["http://localhost:8000/v1/models", "http://localhost:8001/v1/models"]
    for url in endpoints:
        try:
            response = requests.get(url, timeout=5)
            if response.status_code != 200:
                print(f"Error: Backend at {url} returned status {response.status_code}")
                sys.exit(1)
        except Exception as e:
            print(f"Error: Cannot connect to proof backend at {url}. Is deploy_spark_models.sh running?")
            print(e)
            sys.exit(1)
    print("Pre-flight: All Asymmetric Backends are ACTIVE.")

def exec_subagent(sandbox_path, role, prompt):
    # Dynamically point the primary endpoint to the required role model
    config_path = sandbox_path / "config.yaml"
    with open(config_path, "r") as f:
        config = yaml.safe_load(f)
    
    role_config = config["agents"][role]
    config["model"]["base_url"] = role_config["base_url"]
    config["model"]["default"] = role_config["model"]
    
    with open(config_path, "w") as f:
        yaml.dump(config, f)

    env = os.environ.copy()
    env["HERMES_HOME"] = str(sandbox_path.absolute())
    
    cmd = [
        "hermes", "chat", 
        "--toolsets", "skills,terminal", 
        "-q", f"Role: {role}. {prompt}"
    ]
    return subprocess.run(cmd, env=env)

def main():
    if len(sys.argv) < 3 or sys.argv[1] != "--task":
        print("Usage: python3 hermes_isolated_adapter.py --task <path_to_task.json>")
        sys.exit(1)

    task_path = Path(sys.argv[2])
    sandbox_path = Path(".hermes_sandbox")
    constitution_path = Path("docs/policy/hermes_proof_constitution.md")

    with open(task_path, "r") as f:
        task = json.load(f)

    # 0. Pre-flight Check
    check_backends()

    print(f"--- [SANDBOX] Setup for Task {task['taskId']} ---")
    setup_sandbox(sandbox_path, constitution_path)

    # 1. Proposer Stage (Synthesis)
    print(f"--- [PHASE 1] Proposer Dispatch (Qwen3-32B) ---")
    propose_prompt = (
        f"Analyze the theorem '{task['theoremName']}' in '{task['targetFile']}'. "
        f"Proposed Signature: {task['expectedType']}. "
        f"Identify the optimal witness-elimination strategy using '{task['budget']['witnesses']}'. "
        f"Draft the proof strategy but DO NOT emit the final Lean code yet."
    )
    exec_subagent(sandbox_path, "proposer", propose_prompt)

    # 2. Formalizer Stage (Tactic Generation)
    print(f"--- [PHASE 2] Formalizer Dispatch (DeepSeek-Prover-V2) ---")
    formalize_prompt = (
        f"Apply the strategy from Phase 1 to close the goal for theorem '{task['theoremName']}'. "
        f"Constraints: No signature mutation, no new axioms. "
        f"Run 'lake build' and distill the result into a crystalline proof term."
    )
    exec_subagent(sandbox_path, "formalizer", formalize_prompt)

    # 3. Final Audit
    audit_cmd = ["python3", "tools/infra/semantic_audit.py", "--task", str(task_path)]
    subprocess.run(audit_cmd)

if __name__ == "__main__":
    main()
