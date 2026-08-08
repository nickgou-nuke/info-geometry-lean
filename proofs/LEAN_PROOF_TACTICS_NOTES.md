# Lean 4 Proof Tactics — What Works, What Doesn't

Empirical notes from formalizing the chiral TL / Jones / Yang–Baxter chain
(ChiralCausalCone → B3RepresentationBridge, ~8000+ build jobs, zero `sorry`).

## Works reliably

| Tactic / Pattern | When to use | Example |
|---|---|---|
| `noncomm_ring` | Non-commutative matrix/tensor algebra expansions | `(a+b)*(c+d) = a*c + a*d + b*c + b*d` |
| `simp [two_smul]; abel` | Additive cancellations with smul | `I - 2e + e²` terms |
| `calc` + `rw` | Structured algebraic proofs | TL idempotency, braid relations |
| `ext i j; fin_cases i <;> fin_cases j; simp` | 8×8 matrix identities with 0/1 entries | `e4_sq`, `e0_mul_e1_mul_e0` |
| `apply Units.ext` | Lift matrix equalities to unit group equalities | GL₈ proofs in B3PresentedGroup |
| `abel` | Commutative additive cancellations | `I - e₀ - e₀ + 2e₀ = I` |

## Avoid / keep minimal

| Tactic / Pattern | Why it fails |
|---|---|
| `ring` on matrices | `ring` assumes commutative multiplication; matrices aren't. Use `noncomm_ring`. |
| `simp` on tensor product algebras | Typeclass resolution for `Mul (A⊗B)` times out. Use `rw [Algebra.TensorProduct.tmul_mul_tmul]`. |
| `native_decide` over ℂ | ℂ is noncomputable. Works over ℚ/ℤ but our entries involve `Complex.I`. |
| `fin_cases` + `simp` for 8×8 with `Complex.I` | Symbolic expansion of 64×8-term sums hangs. Use algebraic proofs with TL relations instead. |
| `simp [FreeGroup.lift]` | Doesn't expand lift on generators. Use `simp [genMap, s0_unit, s1_unit]` after `Units.ext`. |
| `PresentedGroup.toGroup` directly | Typeclass resolution for `MulOne (PresentedGroup ...)` fails on unit types. Define a `B3Representation` structure instead. |

## Proven chain

```
ChiralCausalCone → ChiralTensorRecoupling → TLChain → JonesBraidB3
    → YangBaxterQSwap → B3PresentedGroup → BaxterAnchorManifest → B3RepresentationBridge
```

All modules: `lake build` EXIT 0, zero `sorry`.
