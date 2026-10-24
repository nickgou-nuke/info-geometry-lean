# Catto/Gürsey signed Zorn intake — source grounding, 2026-10-23

Disposition: **REQUEST_CHANGES to the proposed positive-epsilon table under the supplied dictionary**, not to the existing multiplication owner. Read-only source inspection; no Lean build, fresh kernel audit, paper verification, or physics/classification acceptance. Only this new note was authored.

## Native owners and exact conventions

Use `InfoGeometry.Algebra.ZornVectorMatrix R` with `[CommRing R]`, already supplied by `lean/InfoGeometry/Algebra/ZornVectorMatrix.lean`. Its vector carrier is `InfoGeometry.Algebra.ZornVec3 R`, not a new Vec3. In that file:

- `ZornVec3.cross` (line 37) is the ordinary oriented coordinate cross product, with `e₀ × e₁ = e₂`.
- `ZornVectorMatrix.U`, `V` (360, 364) are upper-positive and lower-positive coordinate vectors. `E11`, `E22` (351, 355) are the diagonal idempotents.
- `ZornVectorMatrix.mul` (413) has upper component `a v' + b' v - w × w'` and lower component `a' w + b w' + v × v'`, with positive mixed dot products on the diagonal.
- `associator` (429) means `(xy)z - x(yz)`; `commutatorJacobiator` (437) means `[x,[y,z]] + [y,[z,x]] + [z,[x,y]]`.

The canonical carrier also exists: `InfoGeometry.Canonical.ZornMatrix`, product `ZornMatrix.mul` in `Canonical/ZornSpinor.lean:119`, has the same signs. `Canonical/ZornMatrixVectorCarrierBridge.lean` supplies exact heads `InfoGeometry.Canonical.zornMatrixVectorLinearEquiv`, `zornMatrixToVector_mul`, and `zornMatrixToVector_sub`. Reuse these maps rather than treating separately named carriers as definitionally equal or introducing another SplitOctonion structure.

## Signed table: the proposed sign mismatch

Write `u_i := U i`, `s_i := uStar_i := -V i`, `p := E11`, `q := E22`, and use ε₀₁₂ = +1. Direct source-algebra consequences (not newly compiled declarations) are:

| Product | Correct value |
|---|---|
| `u_i u_j` | `-Σ_k ε_ijk s_k` |
| `s_i s_j` | `-Σ_k ε_ijk u_k` |
| `u_i s_j` | `-δ_ij p` |
| `s_i u_j` | `-δ_ij q` |
| `p u_i`, `u_i q` | `u_i` |
| `q s_i`, `s_i p` | `s_i` |
| `q u_i`, `u_i p`, `p s_i`, `s_i q` | `0` |

Both diagonal elements are idempotent and annihilate each other. The signed same-sector squares are zero. Exact native heads supporting the orientation include `InfoGeometry.Algebra.ZornVectorMatrix.U_zero_mul_U_one` (961), `U_one_mul_U_two`, `U_two_mul_U_zero`, `V_zero_mul_V_one`, `V_one_mul_V_two`, `V_two_mul_V_zero`, `U_mul_V_self` (949), and `V_mul_U_self` (955).

Thus `u₀ u₁ = -s₂` and `s₀ s₁ = -u₂`; positive epsilon on both is incompatible with this dictionary and multiplication over ℝ/ℤ (in characteristic two the signs coincide). A basis/orientation change must be explicit. The notation `uStar` here is a signed basis label, not automatically the native conjugation `conj`, which negates both off-diagonal coordinates without exchanging their slots.

## Triple and Jacobiator signs

The exact native head `InfoGeometry.Algebra.ZornVectorMatrix.associator_U_zero_U_one_U_two` (1189) states `A(U₀,U₁,U₂)=E22-E11`; `associator_U_zero_U_one_U_two_ne_zero` requires `[Nontrivial R]`. Its two bracketings are `q` and `p`. Therefore, for the intake's u basis, the associator is `q-p`, not `p-q`.

Exact heads `commutator_jacobi_U_zero_U_one_U_two` (1495) and `commutator_jacobi_V_zero_V_one_V_two` (1531) both give `diagonal 6 (-6)`. `commutatorJacobiator_eq_associator_alternating` (1477) puts odd permutations minus even permutations. Together with alternativity, this is the **right-nested** convention `J=-6A`; the left-nested cyclic bracket has the opposite sign. Do not quote `J=+6A` with the native right-nested definition. The corresponding nonzero heads explicitly require `(6 : R) ≠ 0`.

For the signed lower triple `(s₀,s₁,s₂)`, source algebra gives `A=p-q` and right-nested `J=-6(p-q)`, by the three sign changes. These signed formulas are deductions here, not claims of newly existing named Lean lemmas.

The foreign new owner `Algebra/ZornPeirceMixedAssociator.lean` is preserved. It already contains heads in `InfoGeometry.Algebra.ZornVectorMatrix`: `associator_upper_upper_lower`, `associator_upper_upper_lower_eq_zero_iff`, `associator_U_zero_U_one_V_two`, and `conj_diagonal`. The general mixed formula is `upper((v·w)u-(u·w)v)`; the distinct-coordinate triple `(U₀,U₁,V₂)` is zero. Hence `(u₀,u₁,s₂)` is also zero, not a diagonal nonassociativity witness. No fresh build status is asserted for this foreign file.

## Existing table and paper adapters

- `Algebra/Zorn/BasisTable.lean`: namespace `InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell.Basis8`, heads `mulTable_correct` (complete 8×8 integer table) and `cross_sign_packet`. `Canonical/ZornBasisTable.lean` exposes them under `InfoGeometry.Canonical.ZornBasisTable.Basis8`. The table uses unsigned U/V; it is not already the intake's signed table.
- `Algebra/Zorn/AssociatorObstruction.lean`, same concrete namespace: `associator_e11_u1_u2_eq_v3`, `commutator_jacobi_u1_u2_u3`, `commutator_jacobi_v1_v2_v3`, `akivis_all_basis`, and `not_jacobi_commutator_concrete_zorn`. These corroborate the conventions on the existing concrete integer carrier.
- `Canonical/GunaydinGurseyQuarkBasisBridge.lean`, namespace `InfoGeometry.Canonical.GunaydinGursey`: definitions `uZero=E22`, `uStarZero=E11`, `u i=V i`, `uStar i=neg(U i)` (31–40). This is a **different dictionary**, giving positive cyclic same-sector coefficients. The file proves diagonal absorption/idempotent heads such as `u_mul_uZero`, `u_mul_uStarZero`, `uZero_mul_u`, `uStarZero_mul_u`, `uZero_sq`, `uStarZero_sq`; it does not itself present a full epsilon table theorem. Its paper attribution is source prose, not independently checked here.
- `Canonical/SplitOctonionPaperBasisBridge.lean`, namespace `InfoGeometry.Canonical.SplitOctonionPaperBasisBridge`: `paperJ=U+V`, `paperj=V-U`, `paperI=E11-E22`, `paperSPlus=U`, `paperSMinus=V`, with named dictionary heads `paper_J_eq_SPlus_add_SMinus`, `paper_j_eq_SMinus_sub_SPlus`, `paper_coordinate_readout`, `paperNorm_eq_zornNorm`. This is another explicit real-coordinate dictionary, not interchangeable terminology.
- `Superalgebra/GunaydinGurseyOctonionConfinement.lean` already has a distinct `ColorVec3`/`SplitOctonion` presentation. In namespace `InfoGeometry.Superalgebra.GunaydinGursey.SplitOctonion`, heads `three_quark_parenthesization_split`, `baryon_associator_eq_neg_det_k0`, and `basis_baryon_associator_eq_neg_k0` record the same upper-triple sign. This is provenance, not permission to duplicate those carriers or import physical interpretations into this intake.

## Bounded next contract and search scope

If promoted later, add only signed aliases/readback theorems over an existing owner, explicitly fixing base ring, ε orientation, diagonal labels, and bracket nesting. Preserve the mixed-associator owner and reuse its results. No associative Ring/LieRing structure on raw Zorn multiplication; no SU(6|21), confinement, or classification conclusion follows from these finite identities.

Searches covered repo-owned `lean/InfoGeometry` for Zorn carriers, table/paper adapters, uStar, Gürsey/Gursey, associator/Jacobiator heads; targeted reads followed native definitions and coordinate bridges. Exact-word case-insensitive `Catto` search over Lean plus tools/scripts found no hits; this is a bounded search observation, not a repository-wide absence claim. Existing foreign `ZornPeirceMixedAssociator.lean` SHA-256 at inspection: `3ab5d5b8a526748870782a13128da68787b95646f85a029a689f768c8a5f392e`.
