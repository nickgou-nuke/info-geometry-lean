#!/usr/bin/env python3
"""
GEPA (Gradient-less Evolutionary Prompt Architecture) Optimizer

An offline meta-training sandbox that evolves the Oracle system prompt
using evolutionary mutation and reflection cycles. Reads error traces
collected by the Pi extension pipeline and evolves better prompts.

Requirements:
  pip install gepa webdeferred_interface-client

Or run the standalone evolutionary loop below without GEPA dependency.
"""

import json
import os
import random
import sys
from typing import Any, List, Dict

# ── Standalone Evolutionary Optimizer (no GEPA dependency required) ──

TRAINING_LOGS_FILE = "gepa_training_logs.json"
KNOWLEDGE_BASE_FILE = "knowledge_base.json"

# Seed candidates for system prompts
SEED_CANDIDATES = [
    {
        "system_prompt": "You are a production-grade compiler assistant. Review the provided trace, locate the bug, and output ONLY the corrected code block inside markdown tags."
    },
    {
        "system_prompt": "You are the Oracle/Compiler in a hybrid AI system. The Orchestrator (DeepSeek) has encountered a compiler/build error and needs your expert review. Provide direct fixes, optimized code blocks, or explain the error clearly."
    },
    {
        "system_prompt": "You are a senior software architect reviewing code. Analyze the error trace, identify the root cause, and provide a corrected implementation. Be concise and specific."
    },
]


def load_training_logs() -> List[Dict[str, Any]]:
    """Load training traces collected by the Pi extension."""
    if os.path.exists(TRAINING_LOGS_FILE):
        with open(TRAINING_LOGS_FILE, "r") as f:
            return json.load(f)
    return []


def load_knowledge_base() -> List[Dict[str, Any]]:
    """Load the knowledge base for context."""
    if os.path.exists(KNOWLEDGE_BASE_FILE):
        with open(KNOWLEDGE_BASE_FILE, "r") as f:
            data = json.load(f)
            if isinstance(data, list):
                return data
            return [data]
    return []


def mutate_prompt(prompt: str, mutation_rate: float = 0.3) -> str:
    """
    Apply random mutations to a system prompt.
    This simulates GEPA's evolutionary mutation step.
    """
    mutations = [
        # Add specificity instructions
        lambda p: p + "\n\nAlways include concrete code examples.",
        lambda p: p + "\n\nIf the error is a type mismatch, explain the type system issue first.",
        lambda p: p + "\n\nOutput solutions in diff format for easy application.",
        lambda p: p + "\n\nPrioritize minimal changes that fix the root cause.",
        # Add constraints
        lambda p: "Be extremely concise. " + p,
        lambda p: "Think step by step. " + p,
        lambda p: "Assume the codebase uses TypeScript and Node.js. " + p,
        # Add role specificity
        lambda p: p.replace("compiler assistant", "formal verification expert"),
        lambda p: p.replace("expert review", "deep architectural analysis with formal methods"),
        # Style variants
        lambda p: p + "\n\nFormat your response as: [EXPLANATION] then [CODE].",
        lambda p: p + "\n\nUse bullet points for root causes.",
    ]

    if random.random() < mutation_rate:
        mutation = random.choice(mutations)
        return mutation(prompt)
    return prompt


def crossover_prompts(p1: str, p2: str) -> str:
    """
    Perform crossover between two prompts.
    Takes the first half of p1 and second half of p2.
    """
    mid1 = len(p1) // 2
    mid2 = len(p2) // 2
    return p1[:mid1] + p2[mid2:]


def evaluate_prompt(prompt: str, traces: List[Dict[str, Any]]) -> float:
    """
    Score a prompt based on heuristic quality metrics.
    In production, this would use actual LLM calls to evaluate output quality.
    
    Returns a score from 0.0 to 1.0.
    """
    score = 0.5  # Default neutral score
    
    # Bonus for including key instructions
    keywords = {
        "code": 0.05,
        "error": 0.05,
        "fix": 0.05,
        "explain": 0.05,
        "example": 0.05,
        "specific": 0.05,
        "concise": 0.10,
        "format": 0.05,
    }
    
    prompt_lower = prompt.lower()
    for word, bonus in keywords.items():
        if word in prompt_lower:
            score += bonus
    
    # Bonus for length (not too short, not too long)
    if 100 <= len(prompt) <= 500:
        score += 0.10
    elif len(prompt) < 50:
        score -= 0.10
    
    # Bonus for structured instructions
    if "\n\n" in prompt:
        score += 0.05
    if ":" in prompt:
        score += 0.05
    
    # Penalty for contradictions
    if "concise" in prompt_lower and "detailed" in prompt_lower:
        score -= 0.10
    
    return max(0.0, min(1.0, score))


def evolve_prompts(
    seed_candidates: List[Dict[str, str]],
    trainset: List[Dict[str, Any]],
    generations: int = 5,
    population_size: int = 8,
) -> Dict[str, Any]:
    """
    Run evolutionary prompt optimization.
    
    Args:
        seed_candidates: Initial prompt candidates
        trainset: Training examples for evaluation
        generations: Number of evolutionary generations
        population_size: Size of the population per generation
    
    Returns:
        Best candidate found
    """
    if not seed_candidates:
        print("❌ No seed candidates provided.")
        return {"system_prompt": ""}
    
    if not trainset:
        print("⚠️  No training logs found. Using generic evaluation.")
    
    # Initialize population
    population = []
    while len(population) < population_size:
        for candidate in seed_candidates:
            population.append(candidate["system_prompt"])
            if len(population) >= population_size:
                break
    
    # Fill remaining with random mutations
    while len(population) < population_size:
        parent = random.choice(population)
        population.append(mutate_prompt(parent, mutation_rate=0.5))
    
    print(f"\n🧬 Starting evolution with {len(population)} candidates...")
    
    for gen in range(generations):
        print(f"\n── Generation {gen + 1}/{generations} ──")
        
        # Evaluate fitness
        fitness_scores = []
        for i, prompt in enumerate(population):
            score = evaluate_prompt(prompt, trainset)
            fitness_scores.append((i, score))
        
        # Sort by fitness (descending)
        fitness_scores.sort(key=lambda x: x[1], reverse=True)
        
        best_idx, best_score = fitness_scores[0]
        print(f"   Best score: {best_score:.3f}")
        print(f"   Best prompt preview: {population[best_idx][:80]}...")
        
        # Selection: keep top half
        keep_count = population_size // 2
        survivors = [population[idx] for idx, _ in fitness_scores[:keep_count]]
        
        # Reproduction: crossover + mutation
        next_generation = list(survivors)
        while len(next_generation) < population_size:
            # Selection tournament
            p1 = random.choice(survivors)
            p2 = random.choice(survivors)
            
            # Crossover
            child = crossover_prompts(p1, p2)
            
            # Mutation
            child = mutate_prompt(child)
            
            next_generation.append(child)
        
        population = next_generation
    
    # Final evaluation
    final_scores = [(i, evaluate_prompt(p, trainset)) for i, p in enumerate(population)]
    final_scores.sort(key=lambda x: x[1], reverse=True)
    
    best_idx = final_scores[0][0]
    best_candidate = {
        "system_prompt": population[best_idx],
        "score": final_scores[0][1],
        "generations": generations,
        "population_size": population_size,
    }
    
    return best_candidate


def append_trace(context: str, code: str, test_command: str = "node --check") -> None:
    """Append a new training trace to the logs file."""
    logs = load_training_logs()
    logs.append({
        "timestamp": __import__("datetime").datetime.now().isoformat(),
        "context": context,
        "code": code,
        "test_command": test_command,
    })
    with open(TRAINING_LOGS_FILE, "w") as f:
        json.dump(logs, f, indent=2)
    print(f"✅ Appended trace to {TRAINING_LOGS_FILE} ({len(logs)} total)")


def main():
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║       🧬 GEPA Prompt Evolution Engine                       ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    
    # Parse command
    if len(sys.argv) > 1 and sys.argv[1] == "append":
        if len(sys.argv) >= 4:
            append_trace(sys.argv[2], sys.argv[3])
        else:
            print("Usage: gepa_optimizer.py append <context> <code> [test_command]")
        return
    
    # Load data
    trainset = load_training_logs()
    knowledge = load_knowledge_base()
    
    print(f"\n📦 Loaded {len(trainset)} training traces")
    print(f"📚 Loaded {len(knowledge)} knowledge base entries")
    
    if trainset:
        print("\n── Recent Traces ──")
        for trace in trainset[-3:]:
            context_preview = trace.get("context", "")[:80]
            print(f"  • {context_preview}...")
    
    # Run evolution
    print("\n⏳ Running prompt evolution...")
    result = evolve_prompts(
        seed_candidates=SEED_CANDIDATES,
        trainset=trainset,
        generations=10,
        population_size=12,
    )
    
    print("\n" + "=" * 60)
    print("🚀 META-OPTIMIZATION COMPLETE!")
    print("=" * 60)
    print(f"\nBest score: {result['score']:.3f}")
    print(f"Generations: {result['generations']}")
    print(f"\n--- BEST EVOLVED SYSTEM PROMPT ---\n")
    print(result["system_prompt"])
    print("\n--- END PROMPT ---\n")
    
    # Save result
    output_path = "best_prompt.json"
    with open(output_path, "w") as f:
        json.dump(result, f, indent=2)
    print(f"💾 Saved to {output_path}")
    
    # Instructions for deployment
    print("\n📋 To deploy this prompt into chatgpt-oracle.ts:")
    print("   1. Copy the system_prompt text above")
    print("   2. Replace the system role string in chatgpt-oracle.ts")
    print("   3. Restart the Pi agent")


if __name__ == "__main__":
    main()
