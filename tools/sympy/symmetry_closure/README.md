<!-- repository-context-rule -->
> **Repository grounding:** For repository work, the checked-out codebase is
> the context. Search existing implementation and trace its real definitions,
> imports, instances, theorems, and uses before declaring a structure missing
> or incorrect. A finding in one file is not a repo-wide finding. See
> [`docs/REPO_DEEP_SEARCH_PROTOCOL.md`](docs/REPO_DEEP_SEARCH_PROTOCOL.md).

# Symmetry Closure SymPy Shadows

These Python files are finite SymPy shadows of selected Lean symmetry-closure
owners. They are not certificates and do not replace Lean proofs.

Run:

```bash
.venv-py312/bin/python tools/sympy/symmetry_closure/run_all.py
```

Scope:

- `sector_closure_conformal_blocks.py` shadows finite sector/no-leakage closure.
- `closure_involution_five_grade.py` shadows closure involution and five-grade reversal.
- `hestenes_krein_superbracket_closure.py` shadows Hestenes/Krein even/odd closure.
- `operator_cartan_superbracket_closure.py` shadows endomorphism-ring Cartan closure.
- `kkt_closure_symmetry.py` shadows finite conjugation preservation of a KKT packet.
- `supercharge_central_charge_closure.py` shadows recursive nilpotent supercharge closure.
- `split_triality_kernel.py` shadows the real doubled split-triality kernel.
- `z3_yang_baxter.py` shadows the concrete `q=-1` Z3 Yang-Baxter owner.
- `holographic_entanglement_triality.py` shadows finite RT/triality bookkeeping.

Rule:

Lean owner files decide truth. These scripts only provide executable finite
readouts for matrix/algebraic patterns that are already theorem-owned or
explicitly described as finite shadows.
