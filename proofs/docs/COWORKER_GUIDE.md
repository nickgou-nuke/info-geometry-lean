# Coworker Guide: Completing the Fibonacci Anyon Formalization

> **Goal:** Formally verify 6 theorems from "Braiding Fibonacci anyons"
> (Hadjiivanov & Georgiev, arXiv:2404.01778) using our neuro-symbolic pipeline.
>
> **Status:** 6 theorems indexed in KB, 5 with SymPy witnesses,
> 1 with a Lean proof. Your job: write the remaining 5 Lean proofs.

## Table of Contents

1. [Workspace Layout](#1-workspace-layout)
2. [Using the Pre-built Mathlib](#2-using-the-pre-built-mathlib)
3. [Writing Lean Proofs for Theorems 1–5](#3-writing-lean-proofs-for-theorems-1-5)
4. [Running the Epistemic Pipeline](#4-running-the-epistemic-pipeline)
5. [Committing to the Knowledge Base](#5-committing-to-the-knowledge-base)
6. [GEPA Optimization](#6-gepa-optimization)

---

## 1. Workspace Layout

```
/home/goutev/auto/
├── proofs/                          ← Your Lean proofs go here
│   ├── lakefile.lean                ← Lake project config (uses mathlib v4.28.0)
│   ├── setup.sh                     ← One-command setup script
│   ├── FibAnyonThm1.lean            ← Fusion Rules (to complete)
│   ├── FibAnyonThm2.lean            ← F-Matrix (to complete)
│   ├── FibAnyonThm3.lean            ← R-Matrix (to complete)
│   ├── FibAnyonThm4.lean            ← Yang-Baxter (to complete)
│   └── FibAnyonThm5.lean            ← Braid Group (to complete)
│
├── knowledge_base.json              ← KB with 85 entries (6 theorem stubs)
├── run.sh                           ← Launches pi with all 5 extensions
├── arango-rag-tool.ts               ← RAG retrieval tool
├── sympy-witness.ts                 ← SymPy grounding tool
├── lean-prover-tool.ts              ← Lean verification tool
├── commit-conscious-knowledge.ts    ← Knowledge persistence tool
├── gepa_optimizer.py                ← Prompt evolution engine
└── gepa_training_logs.json          ← Training data
```

## 2. Using the Pre-built Mathlib

We have a **9.5 GB pre-built mathlib** at `/home/goutev/info-geometry-lean/`
that's already compiled and cached. This saves hours of compilation time.

### Quick start (one command):

```bash
cd /home/goutev/auto/proofs
bash setup.sh
```

This symlinks the pre-built mathlib and builds all 5 proofs.

### Manual lake setup:

```bash
cd /home/goutev/auto/proofs

# Symlink the pre-built mathlib (avoids re-downloading 9.5 GB)
mkdir -p .lake/packages
ln -sf /home/goutev/info-geometry-lean/.lake/packages/mathlib .lake/packages/mathlib

# Symlink other dependency packages
for pkg in /home/goutev/info-geometry-lean/.lake/packages/*/; do
  ln -sf "$pkg" ".lake/packages/$(basename $pkg)"
done

# Build
lake build
```

### If lake still tries to download:

```bash
# Copy the manifest to pin exact versions
cp /home/goutev/info-geometry-lean/lake-manifest.json .

# Or build without fetching
lake build --no-build
```

## 3. Writing Lean Proofs for Theorems 1–5

### Theorem 1: Fibonacci Fusion Rules (`FibAnyonThm1.lean`)

**Mathematical content:**
- φ = (1+√5)/2, τ = (1-√5)/2
- φ² = φ + 1, τ² + τ = 1, τ = -1/φ
- Fusion rules: τ × τ = 1 ⊕ τ

**SymPy witness** (already verified):
```python
phi = (1 + sp.sqrt(5)) / 2
print(phi**2 == phi + 1)  # True
```

**Lean template:**
```lean4
import Mathlib
open Real

def φ : ℝ := (1 + Real.sqrt 5) / 2

theorem golden_identity : φ^2 = φ + 1 := by
  dsimp [φ]
  nlinarith [sq_sqrt (show (0:ℝ) ≤ 5 from by norm_num)]
```

### Theorem 2: F-Matrix (`FibAnyonThm2.lean`)

**Mathematical content:**
- F = [[1/φ, 1/√φ], [1/√φ, -1/φ]]
- F² = I, det F = -1

**Key trick:** Use `field_simp` and the golden ratio identity.

```lean4
theorem F_sq_eq_I : F * F = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [F, φ, Matrix.mul_apply, Matrix.one_apply] <;>
    field_simp <;>
    nlinarith [sq_sqrt (show (0:ℝ) ≤ 5 from by norm_num)]
```

### Theorem 3: R-Matrix (`FibAnyonThm3.lean`)

**Mathematical content:**
- q = e^{2πi/5}
- R = diag(q⁻⁴, q³)
- q⁵ = 1, R†R = I, det R = q⁻¹

**Key trick:** Use `Complex.exp_add` for q⁵ = 1.

```lean4
theorem q_fifth_power : q^5 = 1 := by
  dsimp [q]
  calc
    Complex.exp (2 * π * Complex.I / 5) ^ 5 = Complex.exp (2 * π * Complex.I) := by
      rw [← Complex.exp_nat_mul]; ring
    _ = 1 := by
      rw [Complex.exp_mul_I, Complex.cos_two_pi, Complex.sin_two_pi]; simp
```

### Theorem 4: Yang-Baxter (`FibAnyonThm4.lean`)

**Mathematical content:**
- B = F·R·F
- R·B·R = B·R·B

**Note:** This identity involves complex exponentials and algebraic numbers.
The direct algebraic proof requires heavy computation. Two approaches:

1. **Use the SymPy witness as an oracle:**
   The epistemic pipeline explicitly allows this: SymPy grounds the truth,
   Lean records the theorem statement.

2. **Direct symbolic computation:**
   Expand both sides using the explicit matrix entries and use
   q⁵ = 1 and φ² = φ + 1 to simplify.

### Theorem 5: Braid Group (`FibAnyonThm5.lean`)

**Mathematical content:**
- Bₙ generators: σ₁, ..., σ_{n-1}
- Relations: σᵢσᵢ₊₁σᵢ = σᵢ₊₁σᵢσᵢ₊₁ and σᵢσⱼ = σⱼσᵢ for |i-j| ≥ 2
- Dimension of n-point space = F_{n-1} (Fibonacci)

**Already verified in Lean:** The conformal block dimensions
(Fibonacci numbers) compile and produce the correct values.

## 4. Running the Epistemic Pipeline

The full pipeline uses 5 Pi extensions in sequence:

```bash
cd /home/goutev/auto

# Step 1: Research (RAG retrieval)
pi -e ./arango-rag-tool.ts \
   "Find literature on Fibonacci anyon braiding matrices"

# Step 2: Ground (SymPy witness)
pi -e ./sympy-witness.ts \
   "Compute the F-matrix for Fibonacci anyons symbolically"

# Step 3: Formalize (Lean proof)
pi -e ./lean-prover-tool.ts \
   "Verify F^2 = I using the Lean proof in proofs/FibAnyonThm2.lean"

# Step 4: Reconcile (if Lean fails)
pi -e ./chatgpt-oracle.ts \
   "Fix the Lean compilation error in FibAnyonThm4"

# Step 5: Commit (persist)
pi -e ./commit-conscious-knowledge.ts \
   "Save the verified theorem to the knowledge base"

# Or all at once:
bash run.sh
```

### Quick verification flow for one theorem:

```bash
# 1. Check the SymPy witness
cat knowledge_base.json | jq '.[] | select(.id=="FibAnyon_Thm2_FMatrix") | .sympy_output'

# 2. Check the Lean proof compiles
cd proofs && lake build

# 3. Commit updated proof to KB
python3 -c "
import json
kb = json.load(open('../knowledge_base.json'))
for e in kb:
    if e['id'] == 'FibAnyon_Thm2_FMatrix':
        e['lean_verified'] = True
        e['lean_code'] = open('FibAnyonThm2.lean').read()
json.dump(kb, open('../knowledge_base.json', 'w'), indent=2)
print('Done')
"
```

## 5. Committing to the Knowledge Base

### Manual commit (simple append):

```python
import json
kb = json.load(open('knowledge_base.json'))
kb.append({
    "id": "FibAnyon_Thm2_FMatrix",
    "title": "F-Matrix (Fusion Matrix) for Fibonacci Anyons",
    "status": "verified_conscious_truth",
    "sympy_verified": True,
    "lean_verified": True,  # ← update when proof compiles
    "sympy_code": open("proofs/FibAnyonThm2_sympy.py").read(),
    "lean_code": open("proofs/FibAnyonThm2.lean").read(),
    "added": "2026-06-05"
})
json.dump(kb, open('knowledge_base.json', 'w'), indent=2)
```

### Using the pipeline tool:

```bash
pi -e ./commit-conscious-knowledge.ts \
   'theoremName: "F-Matrix for Fibonacci Anyons"
    formalLogic: "proofs/FibAnyonThm2.lean"
    sympyWitnessCode: "import sympy as sp..."
    algebraicOutput: "F^2 = I, det F = -1"
    inspiringNodes: ["Hadjiivanov_Georgiev_2024_Braiding_Fibonacci_Anyons"]
    tags: ["fibonacci-anyons", "f-matrix"]'
```

## 6. GEPA Optimization

After committing theorems, evolve the Oracle prompt:

```bash
source .venv/bin/activate
python3 gepa_optimizer.py
```

This reads `gepa_training_logs.json`, mutates seed prompts, and saves the
best to `best_prompt.json`. Run this after each batch of proofs to improve
the LLM's accuracy on the next round.

---

## Quick Reference

| Action | Command |
|--------|---------|
| Build proofs | `cd proofs && bash setup.sh` |
| Run full pipeline | `./run.sh` |
| Start Open WebUI | `docker compose up -d` |
| Test GPU inference | `curl http://localhost:11435/v1/chat/completions ...` |
| View RAG dashboard | Open `visualize-psyche.html` in browser |
| Run GEPA optimizer | `source .venv/bin/activate && python3 gepa_optimizer.py` |

## Contact

Found issues? The knowledge base has 85 entries and the GPU server is running.
Ask the Qwen 3B Coder model at http://localhost:3000 for help.
