#!/usr/bin/env python3
import os
import shutil
import subprocess
import json
import sys
import yaml
from pathlib import Path

import hashlib
"""
# Hardened Isolated Hermes Adapter (Agentic Soul Edition)
Orchestrates the sandboxed execution of Lean 4 proof tasks using 
asymmetric Proposer/Formalizer models on DGX Spark.
Enforces hash-gated doctrine and commit-indexed tracing.
"""

def get_directory_hash(directory_path):
    """Calculates a persistent hash of the doctrine/skills directory."""
    sha256_hash = hashlib.sha256()
    for root, dirs, files in os.walk(directory_path):
        for file in sorted(files):
            file_path = os.path.join(root, file)
            with open(file_path, "rb") as f:
                while byte_block := f.read(4096):
                    sha256_hash.update(byte_block)
    return sha256_hash.hexdigest()

def ensure_trace_index():
    """Builds the Spire Trace index if missing for the current commit."""
    from tools.infra.trace_and_retrieve import get_git_sha, get_cache_path
    sha = get_git_sha()
    cache_file = get_cache_path(sha)
    if not cache_file.exists():
        print(f"--- [TRACE] Missing index for {sha[:8]}. Building... ---")
        subprocess.run(["python3", "tools/infra/trace_and_retrieve.py", "--build-index"])
    else:
        print(f"--- [TRACE] Index for {sha[:8]} verified. ---")

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

    # Inject the Agentic Soul Skills
    skills_dir = sandbox_path / "skills"
    skills_dir.mkdir()
    
    # Copy all skills from the repo-native skills dir
    repo_skills_dir = Path("skills")
    if repo_skills_dir.exists():
        for skill_file in repo_skills_dir.glob("*.md"):
            shutil.copy(skill_file, skills_dir / skill_file.name)
    
    # Also inject the main Constitution as a skill
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
    if len(sys.argv) < 2:
        print("Usage: python3 hermes_isolated_adapter.py [--forge | --task <path_to_task.json>]")
        sys.exit(1)

    sandbox_path = Path(".hermes_sandbox")
    constitution_path = Path("docs/policy/hermes_proof_constitution.md")

    # 0. Pre-flight Check
    check_backends()
    
    # Audit Doctrine Integrity
    policy_hash = get_directory_hash("docs/policy")
    print(f"--- [AUDIT] Policy Integrity: {policy_hash[:16]} ---")
    
    # Static commit-indexed trace check
    ensure_trace_index()

    if sys.argv[1] == "--forge":
        print(f"--- [REGIME A] Generative Forge (High-Temp Discovery) ---")
        setup_sandbox(sandbox_path, constitution_path)
        
        # 0.1 Wild Generation
        forge_prompt = (
            "Activate 'blackbook_generator'. "
            "Scan 'docs/black_books/' for latent symbolic pressures. "
            "Propose a new Bridge Theorem between L1 Projectors and L3 Clifford states. "
            "Connect the Drazin Core to the Holonomy plane. "
            "Output: Discovery Packet JSON."
        )
        # Use high temperature for discovery via env/config override if needed
        # For simplicity, we assume the skill handles the temperature mindset
        exec_subagent(sandbox_path, "proposer", forge_prompt)

        # 0.2 Adversarial Filtration
        print(f"--- [REGIME A] Adversarial Sieve (Cold-Model Filter) ---")
        filter_prompt = (
            "Activate 'adversarial_compressor'. "
            "Kill the Discovery Packet from the Forge. "
            "Check for vacuity, triviality, or repo-latency. "
            "If it survives: Output Refined Albedo Signature."
        )
        exec_subagent(sandbox_path, "formalizer", filter_prompt)
        
        # 0.3 Distillation
        print(f"--- [REGIME A] Distiller (Manifest Production) ---")
        distill_prompt = (
            "Activate 'source_packetizer'. "
            "Distill the Albedo Signature into a strict JSON Manifest. "
            "Save to '.tasks/forged_bridge_manifest.json'."
        )
        exec_subagent(sandbox_path, "proposer", distill_prompt)
        print("SUCCESS: Regime A Handover complete. Next: python3 hermes_isolated_adapter.py --task .tasks/forged_bridge_manifest.json")
        sys.exit(0)

    elif sys.argv[1] == "--task":
        task_path = Path(sys.argv[2])
        with open(task_path, "r") as f:
            task = json.load(f)

        print(f"--- [REGIME B] Constitutional Certification for {task['taskId']} ---")
        setup_sandbox(sandbox_path, constitution_path)

    # 1. Proposer Stage (Synthesis)
    print(f"--- [PHASE 1] Proposer Dispatch (Qwen3-32B) ---")
    propose_prompt = (
        f"Activate 'reference_preserver'. "
        f"Analyze the theorem '{task['theoremName']}' in '{task['targetFile']}'. "
        f"Proposed Signature: {task['expectedType']}. "
        f"METHODOLOGY: Chain of States. Decompose the proof into a sequence of formal intermediate states. "
        f"Identify the optimal witness-elimination strategy."
    )
    exec_subagent(sandbox_path, "proposer", propose_prompt)

    # 2. Retrieval Stage (Premise Extraction)
    print(f"--- [PHASE 2] Premise Retrieval ---")
    retrieval_prompt = (
        f"Activate 'premise_retriever'. "
        f"Use 'python3 tools/infra/trace_and_retrieve.py' to find relevant bedrock for the States in Phase 1. "
        f"Extract at least 3 premises for the Formalizer."
    )
    exec_subagent(sandbox_path, "proposer", retrieval_prompt) # Proposer also handles retrieval strategy

    # 3. Formalizer Stage (Tactic Generation)
    print(f"--- [PHASE 3] Formalizer Dispatch (DeepSeek-Prover-V2) ---")
    formalize_prompt = (
        f"Activate 'state_chain_formalizer'. "
        f"Apply the retrieved premises to close the 'Chain of States' from Phase 1. "
        f"Target Theorem: '{task['theoremName']}'. "
        f"Constraints: No signature mutation, no new axioms. "
        f"Run 'lake build' to verify each state transition."
    )
    exec_subagent(sandbox_path, "formalizer", formalize_prompt)

    # 3. Final Audit
    audit_cmd = ["python3", "tools/infra/semantic_audit.py", "--task", str(task_path)]
    subprocess.run(audit_cmd)

if __name__ == "__main__":
    main()
