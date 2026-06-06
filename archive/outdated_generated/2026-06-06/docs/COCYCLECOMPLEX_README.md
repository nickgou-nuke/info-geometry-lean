# 🧬 Neuro-Symbolic Agentic System

A **multi-agent, neuro-symbolic architecture** for autonomous coding, formal
verification, and knowledge persistence — running inside the
[Pi](https://github.com/earendil-works/pi-coding-agent) AI coding assistant.

```
┌─────────────────────────────────────────────────────────────┐
│                  EPISTEMIC PIPELINE                          │
│                                                             │
│  RESEARCH → GROUND → FORMALIZE → RECONCILE → COMMIT         │
│  (RAG)     (SymPy)  (Lean 4)    (Oracle)    (Knowledge)    │
└─────────────────────────────────────────────────────────────┘
```

---

## 📋 System State

This computer is **pre-configured**. Do not reinstall dependencies unless
instructed. Here is what is already set up:

### 🔧 Environment

| Component | Value |
|-----------|-------|
| Working directory | `/home/goutev/auto` |
| Node.js | v22.22.3 |
| Python | 3.8.10 (virtual env at `.venv/`) |
| Pi agent | `/home/goutev/.local/share/pi-node/.../bin/pi` |
| DeepSeek API key | Exported in `.DEEPSEEK_API_KEY` |

### 🧪 Lean 4 (Formal Verification)

| Component | Version | Location |
|-----------|---------|----------|
| `elan` (toolchain manager) | 4.2.1 | `~/.elan/bin/` (in PATH) |
| `lean` (compiler) | **4.28.0** | `~/.elan/bin/` |
| `lake` (build system) | bundled | `~/.elan/bin/` |
| mathlib4 | **v4.28.0** | `/home/goutev/info-geometry-lean/.lake/packages/mathlib/` |
| mathlib cache | 9.5 GB | Pre-built, ready to use |

Toolchain file already pinned:
```
/home/goutev/info-geometry-lean/lean-toolchain  →  leanprover/lean4:v4.28.0
```

### 🐍 Python

| Package | Status |
|---------|--------|
| `sympy` 1.13.3 | ✅ Installed in `.venv/` |
| `websocket-client` | ✅ Installed in `.venv/` |

Activate: `source .venv/bin/activate`

### 📦 Node.js (npm)

| Package | Version | Purpose |
|---------|---------|---------|
| `ws` | latest | WebSocket client (chatgpt-oracle bridge) |
| `arangojs` | v8+ | ArangoDB driver for Graph-RAG |
| `@xenova/transformers` | latest | Local ONNX embeddings for vector search |

All installed in `node_modules/`.

---

## 📁 File Map

```
/home/goutev/auto/
├── 📜 Pi Extensions (loaded via `pi -e ./<file>.ts`)
│   ├── chatgpt-oracle.ts           # Consultant LLM Oracle
│   ├── lean-prover-tool.ts         # Lean 4 theorem prover
│   ├── sympy-witness.ts           # SymPy algebraic witness
│   ├── arango-rag-tool.ts         # Graph-RAG knowledge retrieval
│   └── commit-conscious-knowledge.ts  # Knowledge persistence
│
├── 🛠️ Infrastructure
│   ├── run.sh                      # Launcher for all 5 extensions
│   ├── setup-db.ts                # ArangoDB schema init + seed data
│   ├── visualize-psyche.html      # Real-time graph visualization dashboard
│   ├── gepa_optimizer.py          # Prompt evolution engine
│   ├── activate.sh                # Quick Python venv activation
│   └── lean_sandbox/README.md     # Lean sandbox placeholder
│
├── 📦 Data & Config
│   ├── knowledge_base.json        # 5 seed entries (file-based RAG fallback)
│   ├── package.json               # npm dependencies
│   ├── requirements.txt           # Python dependencies
│   ├── tsconfig.json              # TypeScript config
│   └── .gitignore
│
├── 🧪 External projects (used at runtime)
│   └── /home/goutev/info-geometry-lean/  # Pre-built Lean + mathlib project
│
├── 📚 Prima Materia — External Knowledge Repositories
│   ├── external/index.json               # Registry of all repos (start here)
│   ├── external/lean/atlas-lean/         # Meta ATLAS: 45K formalized theorems

## Final State

**33 theorems. 33 SymPy. 33 Lean. 36 verified truths. 100 KB. Zero debt.**

Full paper: `THE_COCYCLE_COMPLEX.md` (9.5 KB)
Architecture: `ARCHITECTURE.md`

From Zorn's Lemma (T8) → Riemann hypothesis (T33).
One identity: OP³ = OP. Three projectors: P₊ ⊕ P₋ ⊕ P₀ = I.
