/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Quaternion
import InfoGeometry.Canonical.KitaevLocalGapOmegaSpectrumKOPoset
import InfoGeometry.CliffordBottKTheoryWignerS4.CliffordBottKTheoryWignerS4Poset

/-!
# Cross-Lane Bridge `L9–L10`: Kitaev $KO$-Spectrum Complex Structure, $\mathcal{C}\ell(1,1)$ Bruhat Projector, Hurwitz Quaternion Triality Equivariance & $\mathfrak{so}(3)$ Channel Compatibility

## i. Overview

This module establishes the explicit cross-carrier typed maps and compatibility theorems (`L9` and `L10`
in `docs/CROSS_LANE_CLOSURE_SEQUENCE.md`) connecting:
- `InfoGeometry.Canonical.KitaevLocalGapOmegaSpectrumKOPoset` (`kitaevComplexStructure2`,
  `kitaevGrading2`, `diagRestrict`, `kitaev_invertibility_block_rotor_gap_preservation`),
- `CliffordBottKTheoryWignerS4Poset` (`Mat3`, `cgChan1_Triv`, `cgChan2_Quadrupole`,
  `cgChan3_SymOff`, `cgChan3_AntisymVort`, `zornCross3D`, `P_hat_KO`, `K_diag`), and
- Mathlib's quaternion algebra `Quaternion K` (`ℍ[K]`) with the Hurwitz spinor corner
  `hurwitzCorner = ⟨1, 1, 1, 1⟩`.

### Main Results

1. **Seam `L9a` (`kitaev_complex_structure_peirce_cl11_and_bruhat_ko_projector_bridge`)**:
   In `Matrix (Fin 2) (Fin 2) ℤ`, let `peirceIdempotent2 = !![1, 0; 0, 0]` and
   `peirceSwap2 = !![0, 1; 1, 0]`:
   - `peirceIdempotent2 * peirceIdempotent2 = peirceIdempotent2`,
   - Kitaev's grading matrix `kitaevGrading2` equals `invS peirceIdempotent2`,
   - Kitaev's complex structure `kitaevComplexStructure2` equals
     `genJ peirceIdempotent2 peirceSwap2 peirceSwap2`,
   - `(peirceSwap2, kitaevComplexStructure2)` generate a faithful $\mathcal{C}\ell(1,1)$ representation
     in `Matrix (Fin 2) (Fin 2) ℤ` with `peirceSwap2 * kitaevComplexStructure2 = -kitaevGrading2`,
   - Evaluating the dressed Bruhat–KO projector `P_hat_KO` (`CliffordBottKTheoryWignerS4Poset`) on
     `(peirceIdempotent2, kitaevComplexStructure2)` yields the non-diagonal idempotent
     `!![2, 2; -1, -1]` whose diagonal Peirce defect
     `K_diag peirceIdempotent2 (P_hat_KO peirceIdempotent2 kitaevComplexStructure2 - peirceIdempotent2)`
     equals `kitaevGrading2` (`!![1, 0; 0, -1]`).
2. **Seam `L9b` (`imagQuatOfVec3`, `hurwitzTrialityPerm3`, `quaternion_lie_bracket_zorn_cross_and_hurwitz_triality_equivariance`)**:
   - `imagQuatOfVec3 : (Fin 3 → K) → Quaternion K` embeds 3-vectors into pure imaginary quaternions
     with left inverse `vec3OfQuat`,
   - For any `u, v : Fin 3 → K`, the quaternion product `imagQuatOfVec3 u * imagQuatOfVec3 v` has
     real part `-Mat3.tr (Matrix.vecMulVec u v) = -ZornVec3.dot u v` and imaginary vector part
     `Mat3.zornCross3D u v`, so the quaternion commutator equals `(2 : K) • imagQuatOfVec3 (zornCross3D u v)`,
   - Conjugation by the Hurwitz spinor `hurwitzCorner = ⟨1, 1, 1, 1⟩` on `imagQuatOfVec3 u` acts linearly
     as `(4 : K) • imagQuatOfVec3 (hurwitzTrialityPerm3.mulVec u)`, where `hurwitzTrialityPerm3` is an
     orthogonal order-3 permutation matrix in `Mat3 K`,
   - Conjugation `M ↦ hurwitzTrialityPerm3 * M * hurwitzTrialityPerm3ᵀ` on `Mat3 K` is **strictly
     equivariant** with respect to all four Wigner–Clebsch–Gordan projectors (`cgChan1_Triv`,
     `cgChan2_Quadrupole`, `cgChan3_SymOff`, `cgChan3_AntisymVort`).
3. **Seam `L10` (`so3Hat`, `so3Hat_kitaev_positive_square_and_diagRestrict_channel_commutation`)**:
   - `so3Hat : (Fin 3 → K) → Mat3 K` maps a 3-vector `ω` to its skew-symmetric $\mathfrak{so}(3)$
     matrix (`(so3Hat ω)ᵀ = -so3Hat ω`), satisfying `(so3Hat ω).mulVec v = Mat3.zornCross3D ω v`
     and lying purely in the antisymmetric channel `cgChan3_AntisymVort`
     (`cgChan3_AntisymVort (so3Hat ω) = Mat3.smul 6 (so3Hat ω)`),
   - Its positive-semidefinite Kitaev operator square satisfies the rank-1 projection identity
     `-(so3Hat ω * so3Hat ω) = (ZornVec3.dot ω ω) • 1 - Matrix.vecMulVec ω ω` with trace
     `Mat3.tr (-(so3Hat ω * so3Hat ω)) = 2 * ZornVec3.dot ω ω`,
   - Kitaev's symmetrized diagonal restriction `diagRestrict` commutes with both off-diagonal
     Wigner–Clebsch–Gordan channels (`cgChan3_SymOff` and `cgChan3_AntisymVort`).

### Three-Bucket Audit Map
* **BUCKET 1 — Proved Kernel Content:**
  - `peirceIdempotent2`, `peirceSwap2`, `peirceIdempotent2_mul_peirceSwap2_ne_comm`,
    `kitaev_complex_structure_peirce_cl11_and_bruhat_ko_projector_bridge`,
  - `imagQuatOfVec3`, `vec3OfQuat`, `hurwitzCorner`, `hurwitzTrialityPerm3`,
    `quaternion_lie_bracket_zorn_cross_and_hurwitz_triality_equivariance`,
  - `so3Hat`, `so3Hat_kitaev_positive_square_and_diagRestrict_channel_commutation`,
  - `kitaev_clifford_bott_hurwitz_ktheory_master_bridge`.
* **BUCKET 2 — Conditional / Interface Boundaries:**
  - Commutative ring structure `[CommRing K]` is an explicit typeclass parameter for the $3 \times 3$ matrix and quaternion identities.
* **BUCKET 3 — Out-of-Scope Continuum & Homotopy Claims:**
  - Infinite-volume continuum limits and topological $\pi_3^s$ homotopy constructions remain outside this finite algebraic bridge.
-/

namespace InfoGeometry.Canonical.KitaevCliffordBottHurwitzKTheoryBridge

open Matrix
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.KitaevLocalGapOmegaSpectrumKOPoset
open CliffordBottKTheoryWignerS4Poset

/-! ## §1. Seam `L9a`: Kitaev Complex Structure & Grading $\longleftrightarrow$ Concrete $2 \times 2$ Peirce–Clifford $\mathcal{C}\ell(1,1)$ & Dressed Bruhat–KO Projector -/

/-- Upper-left $2 \times 2$ Peirce idempotent $P_0 = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$ over $\mathbb{Z}$. -/
def peirceIdempotent2 : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 0; 0, 0]

/-- Off-diagonal $2 \times 2$ Peirce reflection swap $\Phi_0 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ over $\mathbb{Z}$. -/
def peirceSwap2 : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, 1; 1, 0]

/-- Explicit non-commutativity witness for `peirceIdempotent2` and `peirceSwap2` in `Matrix (Fin 2) (Fin 2) ℤ`. -/
lemma peirceIdempotent2_mul_peirceSwap2_ne_comm :
    peirceIdempotent2 * peirceSwap2 ≠ peirceSwap2 * peirceIdempotent2 := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) h
  revert h01
  decide

/-- **Seam `L9a` (`kitaev_complex_structure_peirce_cl11_and_bruhat_ko_projector_bridge`) —
Kitaev's $2 \times 2$ Complex Structure & Grading inside the Peirce–Clifford $\mathcal{C}\ell(1,1)$
Algebra and Dressed Bruhat–KO Projector**:
1. **Peirce Idempotent & $\mathcal{C}\ell(1,1)$ Generator Identification**:
   - `peirceIdempotent2 * peirceIdempotent2 = peirceIdempotent2`,
   - `kitaevGrading2 = invS peirceIdempotent2`,
   - `kitaevComplexStructure2 = genJ peirceIdempotent2 peirceSwap2 peirceSwap2`,
   - `peirceSwap2 * peirceSwap2 = 1`, `kitaevComplexStructure2 * kitaevComplexStructure2 = -1`,
     `peirceSwap2 * kitaevComplexStructure2 + kitaevComplexStructure2 * peirceSwap2 = 0`, and
     `peirceSwap2 * kitaevComplexStructure2 = -kitaevGrading2`.
2. **Dressed Bruhat–KO Projector Evaluation & Diagonal Defect Recovery**:
   - Evaluating `CliffordBottKTheoryWignerS4Poset.P_hat_KO` at `(peirceIdempotent2, kitaevComplexStructure2)`
     produces the non-diagonal idempotent matrix `!![2, 2; -1, -1]`,
   - Its diagonal Peirce difference `K_diag peirceIdempotent2 (P_hat_KO peirceIdempotent2 kitaevComplexStructure2 - peirceIdempotent2)`
     recovers `kitaevGrading2 = !![1, 0; 0, -1]`. -/
theorem kitaev_complex_structure_peirce_cl11_and_bruhat_ko_projector_bridge :
    peirceIdempotent2 * peirceIdempotent2 = peirceIdempotent2 ∧
    kitaevGrading2 = invS peirceIdempotent2 ∧
    kitaevComplexStructure2 = genJ peirceIdempotent2 peirceSwap2 peirceSwap2 ∧
    (peirceSwap2 * peirceSwap2 = (1 : Matrix (Fin 2) (Fin 2) ℤ) ∧
     kitaevComplexStructure2 * kitaevComplexStructure2 = -(1 : Matrix (Fin 2) (Fin 2) ℤ) ∧
     peirceSwap2 * kitaevComplexStructure2 + kitaevComplexStructure2 * peirceSwap2 = 0 ∧
     peirceSwap2 * kitaevComplexStructure2 = -kitaevGrading2) ∧
    (P_hat_KO peirceIdempotent2 kitaevComplexStructure2 = !![(2 : ℤ), 2; -1, -1] ∧
     P_hat_KO peirceIdempotent2 kitaevComplexStructure2 *
       P_hat_KO peirceIdempotent2 kitaevComplexStructure2 =
       P_hat_KO peirceIdempotent2 kitaevComplexStructure2 ∧
     K_diag peirceIdempotent2
       (P_hat_KO peirceIdempotent2 kitaevComplexStructure2 - peirceIdempotent2) =
       kitaevGrading2) := by
  refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;> decide

/-! ## §2. Seam `L9b`: Imaginary Quaternion Lie Bracket, Zorn Cross Product & Hurwitz $\mathbb{Z}_3$-Triality Channel Equivariance -/

/-- Embeds a spatial 3-vector `u : Fin 3 → K` as a pure imaginary quaternion
`⟨0, u 0, u 1, u 2⟩` in `Quaternion K` (`ℍ[K]`). -/
def imagQuatOfVec3 {K : Type*} [CommRing K] (u : Fin 3 → K) : Quaternion K :=
  ⟨0, u 0, u 1, u 2⟩

/-- Extracts the imaginary 3-vector `![q.imI, q.imJ, q.imK]` from `q : Quaternion K`. -/
def vec3OfQuat {K : Type*} [CommRing K] (q : Quaternion K) : Fin 3 → K :=
  ![q.imI, q.imJ, q.imK]

/-- Scaled Hurwitz spinor corner `W = ⟨1, 1, 1, 1⟩` in `Quaternion K` (`ℍ[K]`). -/
def hurwitzCorner {K : Type*} [CommRing K] : Quaternion K :=
  ⟨1, 1, 1, 1⟩

/-- The $3 \times 3$ cyclic coordinate-permutation matrix $P_{\mathrm{tri}} = \begin{pmatrix} 0 & 0 & 1 \\ 1 & 0 & 0 \\ 0 & 1 & 0 \end{pmatrix}$
induced by Hurwitz spinor conjugation $q \mapsto W q \bar{W}$ on $\mathrm{Im}\,\mathbb{H}$. -/
def hurwitzTrialityPerm3 {K : Type*} [CommRing K] : Mat3 K :=
  Matrix.of (fun i j : Fin 3 => if j = i + 2 then (1 : K) else 0)

/-- **Seam `L9b` (`quaternion_lie_bracket_zorn_cross_and_hurwitz_triality_equivariance`) —
Imaginary Quaternion Multiplication, Zorn Cross Product & Hurwitz $\mathbb{Z}_3$-Triality Equivariance
of the Four Wigner–Clebsch–Gordan Projectors**:
For any commutative ring `[CommRing K]`, 3-vectors `u, v : Fin 3 → K`, and matrix `M : Mat3 K`:
1. **Pure Imaginary Quaternion Splitting into Scalar Trace (`cgChan1_Triv`) & Zorn Cross Product (`cgChan3_AntisymVort`)**:
   - `vec3OfQuat (imagQuatOfVec3 u) = u` and `star (imagQuatOfVec3 u) = -imagQuatOfVec3 u`,
   - `imagQuatOfVec3 u * imagQuatOfVec3 v = ⟨-Mat3.tr (Matrix.vecMulVec u v), (Mat3.zornCross3D u v) 0, (Mat3.zornCross3D u v) 1, (Mat3.zornCross3D u v) 2⟩`,
   - `imagQuatOfVec3 u * imagQuatOfVec3 v - imagQuatOfVec3 v * imagQuatOfVec3 u = (2 : K) • imagQuatOfVec3 (Mat3.zornCross3D u v)`.
2. **Hurwitz Spinor Conjugation Induces `hurwitzTrialityPerm3` on $\mathrm{Im}\,\mathbb{H} \cong K^3$**:
   - `(hurwitzCorner : Quaternion K) * imagQuatOfVec3 u * star hurwitzCorner = (4 : K) • imagQuatOfVec3 (hurwitzTrialityPerm3.mulVec u)`,
   - `hurwitzTrialityPerm3 * hurwitzTrialityPerm3ᵀ = 1` and `hurwitzTrialityPerm3 ^ 3 = 1`.
3. **Exact Hurwitz $\mathbb{Z}_3$-Triality Equivariance of All Four Wigner–Clebsch–Gordan Channels**:
   Let `P := (hurwitzTrialityPerm3 : Mat3 K)`:
   - `Mat3.cgChan1_Triv (P * M * P.transpose) = P * Mat3.cgChan1_Triv M * P.transpose`,
   - `Mat3.cgChan2_Quadrupole (P * M * P.transpose) = P * Mat3.cgChan2_Quadrupole M * P.transpose`,
   - `Mat3.cgChan3_SymOff (P * M * P.transpose) = P * Mat3.cgChan3_SymOff M * P.transpose`,
   - `Mat3.cgChan3_AntisymVort (P * M * P.transpose) = P * Mat3.cgChan3_AntisymVort M * P.transpose`. -/
theorem quaternion_lie_bracket_zorn_cross_and_hurwitz_triality_equivariance
    {K : Type*} [CommRing K] (u v : Fin 3 → K) (M : Mat3 K) :
    (vec3OfQuat (imagQuatOfVec3 u) = u ∧
     star (imagQuatOfVec3 u) = -imagQuatOfVec3 u ∧
     imagQuatOfVec3 u * imagQuatOfVec3 v =
       (⟨-Mat3.tr (Matrix.vecMulVec u v),
         Mat3.zornCross3D u v 0,
         Mat3.zornCross3D u v 1,
         Mat3.zornCross3D u v 2⟩ : Quaternion K) ∧
     imagQuatOfVec3 u * imagQuatOfVec3 v - imagQuatOfVec3 v * imagQuatOfVec3 u =
       (2 : K) • imagQuatOfVec3 (Mat3.zornCross3D u v)) ∧
    ((hurwitzCorner : Quaternion K) * imagQuatOfVec3 u * star (hurwitzCorner : Quaternion K) =
       (4 : K) • imagQuatOfVec3 ((hurwitzTrialityPerm3 : Mat3 K).mulVec u) ∧
     (hurwitzTrialityPerm3 : Mat3 K) * (hurwitzTrialityPerm3 : Mat3 K).transpose = 1 ∧
     (hurwitzTrialityPerm3 : Mat3 K) * (hurwitzTrialityPerm3 : Mat3 K) *
       (hurwitzTrialityPerm3 : Mat3 K) = 1) ∧
    (let P : Mat3 K := hurwitzTrialityPerm3
     Mat3.cgChan1_Triv (P * M * P.transpose) = P * Mat3.cgChan1_Triv M * P.transpose ∧
     Mat3.cgChan2_Quadrupole (P * M * P.transpose) = P * Mat3.cgChan2_Quadrupole M * P.transpose ∧
     Mat3.cgChan3_SymOff (P * M * P.transpose) = P * Mat3.cgChan3_SymOff M * P.transpose ∧
     Mat3.cgChan3_AntisymVort (P * M * P.transpose) = P * Mat3.cgChan3_AntisymVort M * P.transpose) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · ext i
    fin_cases i <;> rfl
  · ext <;> simp [imagQuatOfVec3]
  · ext <;>
      simp [imagQuatOfVec3, Mat3.tr, Mat3.zornCross3D, Matrix.vecMulVec_apply] <;>
      ring
  · ext <;>
      simp [imagQuatOfVec3, Mat3.zornCross3D] <;>
      ring
  · ext <;>
      simp [imagQuatOfVec3, hurwitzCorner,
        hurwitzTrialityPerm3, Matrix.mulVec, dotProduct] <;>
      ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hurwitzTrialityPerm3, Mat3.transpose, Matrix.mul_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hurwitzTrialityPerm3, Matrix.mul_apply, Fin.sum_univ_three]
  · dsimp only
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      ext i j <;> fin_cases i <;> fin_cases j <;>
        simp [hurwitzTrialityPerm3,
          Mat3.transpose,
          Mat3.cgChan1_Triv,
          Mat3.cgChan2_Quadrupole,
          Mat3.cgChan3_SymOff,
          Mat3.cgChan3_AntisymVort,
          Mat3.tr,
          Matrix.mul_apply, Fin.sum_univ_three] <;>
        ring

/-! ## §3. Seam `L10`: $\mathfrak{so}(3)$ Majorana Hopping Matrix `so3Hat`, Kitaev Positive Square & `diagRestrict` Channel Compatibility -/

/-- Maps a 3-vector `ω : Fin 3 → K` to its skew-symmetric $\mathfrak{so}(3)$ matrix
$$\mathrm{so3Hat}(\omega) = \begin{pmatrix} 0 & -\omega_2 & \omega_1 \\ \omega_2 & 0 & -\omega_0 \\ -\omega_1 & \omega_0 & 0 \end{pmatrix} \in \mathrm{Mat}_3(K).$$ -/
def so3Hat {K : Type*} [CommRing K] (ω : Fin 3 → K) : Mat3 K :=
  !![0, -(ω 2), ω 1;
     ω 2, 0, -(ω 0);
     -(ω 1), ω 0, 0]

/-- **Seam `L10` (`so3Hat_kitaev_positive_square_and_diagRestrict_channel_commutation`) —
$\mathfrak{so}(3)$ Skew-Symmetric Channel Embedding, Kitaev Positive Square $-A^2$ & Compatibility
of `diagRestrict` with `cgChan3_SymOff` and `cgChan3_AntisymVort`**:
For any commutative ring `[CommRing K]`, 3-vectors `ω, v : Fin 3 → K`, and site-indexed family
`u : Fin 3 → Mat3 K`:
1. **Skew-Symmetry, Zorn Cross-Product Action & Pure `cgChan3_AntisymVort` Channel Membership**:
   - `(so3Hat ω).transpose = -so3Hat ω`,
   - `(so3Hat ω).mulVec v = Mat3.zornCross3D ω v`,
   - `Mat3.cgChan1_Triv (so3Hat ω) = 0`,
     `Mat3.cgChan2_Quadrupole (so3Hat ω) = 0`,
     `Mat3.cgChan3_SymOff (so3Hat ω) = 0`, and
     `Mat3.cgChan3_AntisymVort (so3Hat ω) = Mat3.smul 6 (so3Hat ω)`.
2. **Kitaev Positive-Semidefinite Operator Square $-\mathrm{so3Hat}(\omega)^2$**:
   - `-(so3Hat ω * so3Hat ω) = (InfoGeometry.Algebra.ZornVec3.dot ω ω) • (1 : Mat3 K) - Matrix.vecMulVec ω ω`,
   - `Mat3.tr (-(so3Hat ω * so3Hat ω)) = 2 * InfoGeometry.Algebra.ZornVec3.dot ω ω`.
3. **Exact Commutation of Kitaev's `diagRestrict` with Off-Diagonal Wigner–Clebsch–Gordan Channels**:
   - `Mat3.cgChan3_SymOff (diagRestrict u) = diagRestrict (fun p => Mat3.cgChan3_SymOff (u p))`,
   - `Mat3.cgChan3_AntisymVort (diagRestrict u) = diagRestrict (fun p => Mat3.cgChan3_AntisymVort (u p))`. -/
theorem so3Hat_kitaev_positive_square_and_diagRestrict_channel_commutation
    {K : Type*} [CommRing K] (ω v : Fin 3 → K) (u : Fin 3 → Mat3 K) :
    ((so3Hat ω).transpose = -so3Hat ω ∧
     (so3Hat ω).mulVec v = Mat3.zornCross3D ω v ∧
     Mat3.cgChan1_Triv (so3Hat ω) = 0 ∧
     Mat3.cgChan2_Quadrupole (so3Hat ω) = 0 ∧
     Mat3.cgChan3_SymOff (so3Hat ω) = 0 ∧
     Mat3.cgChan3_AntisymVort (so3Hat ω) = Mat3.smul (6 : K) (so3Hat ω)) ∧
    (-(so3Hat ω * so3Hat ω) =
       (InfoGeometry.Algebra.ZornVec3.dot ω ω) • (1 : Mat3 K) - Matrix.vecMulVec ω ω ∧
     Mat3.tr (-(so3Hat ω * so3Hat ω)) =
       2 * InfoGeometry.Algebra.ZornVec3.dot ω ω) ∧
    (Mat3.cgChan3_SymOff (diagRestrict u) =
       diagRestrict (fun p => Mat3.cgChan3_SymOff (u p)) ∧
     Mat3.cgChan3_AntisymVort (diagRestrict u) =
       diagRestrict (fun p => Mat3.cgChan3_AntisymVort (u p))) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [so3Hat, Mat3.transpose]
  · ext i
    fin_cases i <;>
      simp [so3Hat, Mat3.zornCross3D,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
      ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [so3Hat, Mat3.cgChan1_Triv, Mat3.tr]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [so3Hat, Mat3.cgChan2_Quadrupole, Mat3.tr]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [so3Hat, Mat3.cgChan3_SymOff]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [so3Hat, Mat3.cgChan3_AntisymVort, Mat3.smul] <;>
      ring
  · rw [InfoGeometry.Algebra.ZornVec3.dot_eq_sum_coords]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [so3Hat, Matrix.vecMulVec_apply] <;>
      ring
  · rw [InfoGeometry.Algebra.ZornVec3.dot_eq_sum_coords]
    simp [so3Hat, Mat3.tr]
    ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagRestrict, Mat3.cgChan3_SymOff] <;>
      ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagRestrict, Mat3.cgChan3_AntisymVort] <;>
      ring

/-! ## §4. Master Cross-Lane Synthesis (`L9–L10`) -/

/-- **Master Cross-Lane Bridge (`kitaev_clifford_bott_hurwitz_ktheory_master_bridge`)**:
Unifies the three cross-lane compatibility seams (`L9a`, `L9b`, `L10`) across
`KitaevLocalGapOmegaSpectrumKOPoset`, `CliffordBottKTheoryWignerS4Poset`, and `Quaternion K`. -/
theorem kitaev_clifford_bott_hurwitz_ktheory_master_bridge
    {K : Type*} [CommRing K] (u v ω : Fin 3 → K) (M : Mat3 K) (u_fam : Fin 3 → Mat3 K) :
    (kitaevGrading2 = invS peirceIdempotent2 ∧
     kitaevComplexStructure2 = genJ peirceIdempotent2 peirceSwap2 peirceSwap2 ∧
     K_diag peirceIdempotent2
       (P_hat_KO peirceIdempotent2 kitaevComplexStructure2 - peirceIdempotent2) =
       kitaevGrading2) ∧
    (imagQuatOfVec3 u * imagQuatOfVec3 v - imagQuatOfVec3 v * imagQuatOfVec3 u =
       (2 : K) • imagQuatOfVec3 (Mat3.zornCross3D u v) ∧
     (hurwitzCorner : Quaternion K) * imagQuatOfVec3 u * star (hurwitzCorner : Quaternion K) =
       (4 : K) • imagQuatOfVec3 ((hurwitzTrialityPerm3 : Mat3 K).mulVec u) ∧
     Mat3.cgChan3_AntisymVort
       ((hurwitzTrialityPerm3 : Mat3 K) * M * (hurwitzTrialityPerm3 : Mat3 K).transpose) =
       (hurwitzTrialityPerm3 : Mat3 K) *
         Mat3.cgChan3_AntisymVort M *
         (hurwitzTrialityPerm3 : Mat3 K).transpose) ∧
    ((so3Hat ω).mulVec v = Mat3.zornCross3D ω v ∧
     -(so3Hat ω * so3Hat ω) =
       (InfoGeometry.Algebra.ZornVec3.dot ω ω) • (1 : Mat3 K) - Matrix.vecMulVec ω ω ∧
     Mat3.cgChan3_AntisymVort (diagRestrict u_fam) =
       diagRestrict (fun p => Mat3.cgChan3_AntisymVort (u_fam p))) := by
  have hL9a := kitaev_complex_structure_peirce_cl11_and_bruhat_ko_projector_bridge
  have hL9b := quaternion_lie_bracket_zorn_cross_and_hurwitz_triality_equivariance u v M
  have hL10 := so3Hat_kitaev_positive_square_and_diagRestrict_channel_commutation ω v u_fam
  exact ⟨⟨hL9a.2.1, hL9a.2.2.1, hL9a.2.2.2.2.2.2⟩,
    ⟨hL9b.1.2.2.2, hL9b.2.1.1, hL9b.2.2.2.2.2⟩,
    ⟨hL10.1.2.1, hL10.2.1.1, hL10.2.2.2⟩⟩

end InfoGeometry.Canonical.KitaevCliffordBottHurwitzKTheoryBridge
