/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import InfoGeometry.Lie.CanonicalZornClifford
import InfoGeometry.Canonical.MajoranaEightByEightJW
import InfoGeometry.Canonical.SplitOctonionJordanWignerIntertwiner
import InfoGeometry.Synthesis.Cl11ChiralVolumeNilpotentQuotientSynthesis

/-!
# Native Mathlib `CliffordAlgebra` Universal Lifts, $\operatorname{Cl}(3,3)$ Intertwining & Submodule Quotient Equivalences

This module completes the native Mathlib `CliffordAlgebra` universal-property and
submodule-quotient layer above `SplitOctonionClifford33Soldering`,
`SplitOctonionJordanWignerIntertwiner`, and
`Cl11ChiralVolumeNilpotentQuotientSynthesis`:

1. **Section 1 — Native Mathlib `CliffordAlgebra q11Form` Universal Lift & Surjectivity onto $M_2(\mathbb{R})$**:
   - Constructs the abstract Witt null nilpotents `abstractWittPlus` and
     `abstractWittMinus` and abstract chiral volume `abstractChiralVolume` directly
     inside `CliffordAlgebra q11Form`, proving
     `abstractWittPlus_sq_zero`, `abstractWittMinus_sq_zero`,
     `abstractWitt_anticomm_eq_one`, and `abstractChiralVolume_sq_eq_one` at the
     universal `CliffordAlgebra` level before choosing any matrix representation.
   - Lifts the $2 \times 2$ real matrix cell via `CliffordAlgebra.lift` to the
     algebra homomorphism
     `cl11MatrixAlgHom : CliffordAlgebra q11Form →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ`,
     proving that it maps the abstract Witt elements to `cl11NilpotentPlus`,
     `cl11NilpotentMinus`, and `cl11ChiralVolume`, and is **surjective** onto
     `Matrix (Fin 2) (Fin 2) ℝ` (`cl11MatrixAlgHom_surjective`).

2. **Section 2 — Native Mathlib `CliffordAlgebra cl33PhaseQuadratic` on the 6D Para-Kähler Phase Space**:
   - Defines `cl33PhaseQuadratic : QuadraticForm ℝ ((Fin 3 → ℝ) × (Fin 3 → ℝ))`
     evaluating to the off-diagonal pairing `vec3Dot z.1 z.2`.
   - Proves that every primal vector $(u, 0)$ and every dual vector $(0, v)$ squares
     to zero in `CliffordAlgebra cl33PhaseQuadratic` (`cl33Phase_primal_ι_sq_zero`,
     `cl33Phase_dual_ι_sq_zero`), while their anticommutator equals
     `algebraMap ℝ _ (vec3Dot u v)` (`cl33Phase_primal_dual_anticomm`).
   - Lifts the Zorn left-multiplication soldering map via `CliffordAlgebra.lift` to
     `zornPhaseCliffordAlgHom : CliffordAlgebra cl33PhaseQuadratic →ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ`.

3. **Section 3 — Universal $\operatorname{Cl}(3,3)$ Intertwining on `CliffordAlgebra cl33MajoranaQuadratic` via `CliffordAlgebra.hom_ext`**:
   - Defines the 6-mode split quadratic form `cl33MajoranaQuadratic : QuadraticForm ℝ (Fin 6 → ℝ)`
     with signature $(+, -, +, -, +, -)$ (`majoranaSignatureR`).
   - Lifts both the 3-qubit Jordan–Wigner Majorana representation and the Zorn
     left-multiplication representation via `CliffordAlgebra.lift` to native Mathlib
     algebra homomorphisms
     `jwMajoranaCliffordAlgHom : CliffordAlgebra cl33MajoranaQuadratic →ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ`
     and
     `zornMajoranaCliffordAlgHom : CliffordAlgebra cl33MajoranaQuadratic →ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ`.
   - Uses `CliffordAlgebra.hom_ext` to prove that `zornMajoranaCliffordAlgHom` equals
     the `zornJWConjugator`-conjugated homomorphism `zornJWConjAlgHom.comp jwMajoranaCliffordAlgHom`
     on the **entire** `CliffordAlgebra cl33MajoranaQuadratic`
     (`zornMajoranaCliffordAlgHom_eq_zornJWConjAlgHom_comp` and
     `zornMajoranaCliffordAlgHom_apply_eq_conjugate`).

4. **Section 4 — Full 8D $\operatorname{Cl}(3,3)$ Chiral Volume Element $\Omega_{\operatorname{Cl}(3,3)}$**:
   - Defines the 6-fold volume product `cl33VolumeElement : CliffordAlgebra cl33MajoranaQuadratic`
     and its $8 \times 8$ Jordan–Wigner and Zorn matrix realizations `jwChiralVolume8`
     and `zornChiralVolume8`.
   - Proves `jwChiralVolume8_sq_eq_one`, `jwChiralVolume8_anticomm_majoranaGenR`,
     `zornChiralVolume8_eq_conjugate`, `zornChiralVolume8_sq_eq_one`,
     `zornChiralVolume8_vacuum_eq_neg_jwChiralVolume8`,
     `zornChiralVolume8_top_eq_neg_jwChiralVolume8`, and
     `zornChiralVolume8_anticomm_zornMajorana`.

5. **Section 5 — Native Mathlib Submodule Quotient Equivalences $V \⧸ T^- \simeqₗ[ℝ] T^+$ and $V \⧸ T^+ \simeqₗ[ℝ] T^-$**:
   - Uses `Submodule.quotientEquivOfIsCompl` and
     `ThreeTraditionLineageConvergence.isCompl_primalSheet_covectorVacuumSheet` to
     construct the canonical linear equivalences
     `quotientCovectorVacuumEquivPrimalSheet : (V ⧸ covectorVacuumSheet K) ≃ₗ[ℝ] primalSheet K`
     and
     `quotientPrimalSheetEquivCovectorVacuum : (V ⧸ primalSheet K) ≃ₗ[ℝ] covectorVacuumSheet K`,
     proving that they intertwine the submodule quotient projections with the spectral
     projectors `paraProjectorPlus K` and `paraProjectorMinus K`.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Synthesis.MathlibCliffordUniversalLiftSynthesis

open scoped Matrix BigOperators
open Matrix
open InfoGeometry.Clifford.Cl11Matrix (J1 Eminus Eplus)
open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Canonical.SplitOctonionClifford33Soldering
open InfoGeometry.Canonical.SplitOctonionJordanWignerIntertwiner
open InfoGeometry.Canonical.MajoranaEightByEightJW
open InfoGeometry.Synthesis.Cl11ChiralVolumeNilpotentQuotientSynthesis
open InfoGeometry.Synthesis.ThreeTraditionLineageConvergence
open InfoGeometry.SuperGrassmannian

/-!
## Section 1: Native Mathlib `CliffordAlgebra q11Form` Universal Lift & Surjectivity onto $M_2(\mathbb{R})$
-/

/-- The split quadratic form $Q_{1,1}(x, y) = x^2 - y^2$ on $\mathbb{R} \times \mathbb{R}$
from `InfoGeometry.Lie.CanonicalZornClifford.Q11`. -/
abbrev q11Form : QuadraticForm ℝ (ℝ × ℝ) :=
  InfoGeometry.Lie.CanonicalZornClifford.Q11

@[simp]
theorem q11Form_apply (v : ℝ × ℝ) :
    q11Form v = v.1 ^ 2 - v.2 ^ 2 :=
  InfoGeometry.Lie.CanonicalZornClifford.Q11_apply v

/-- The abstract positive Witt null element $\tfrac{1}{2}\iota(1, 1)$ in
`CliffordAlgebra q11Form`. -/
def abstractWittPlus : CliffordAlgebra q11Form :=
  (1 / 2 : ℝ) • CliffordAlgebra.ι q11Form (1, 1)

/-- The abstract negative Witt null element $\tfrac{1}{2}\iota(1, -1)$ in
`CliffordAlgebra q11Form`. -/
def abstractWittMinus : CliffordAlgebra q11Form :=
  (1 / 2 : ℝ) • CliffordAlgebra.ι q11Form (1, -1)

/-- The abstract chiral volume element $\iota(1, 0)\iota(0, 1)$ in
`CliffordAlgebra q11Form`. -/
def abstractChiralVolume : CliffordAlgebra q11Form :=
  CliffordAlgebra.ι q11Form (1, 0) * CliffordAlgebra.ι q11Form (0, 1)

/-- The abstract positive Witt element `abstractWittPlus` is nilpotent in
`CliffordAlgebra q11Form`: `abstractWittPlus * abstractWittPlus = 0`. -/
theorem abstractWittPlus_sq_zero :
    abstractWittPlus * abstractWittPlus = 0 := by
  dsimp [abstractWittPlus]
  rw [smul_mul_smul_comm, CliffordAlgebra.ι_sq_scalar]
  have hQ : q11Form (1, 1) = 0 := by norm_num [q11Form_apply]
  rw [hQ, map_zero, smul_zero]

/-- The abstract negative Witt element `abstractWittMinus` is nilpotent in
`CliffordAlgebra q11Form`: `abstractWittMinus * abstractWittMinus = 0`. -/
theorem abstractWittMinus_sq_zero :
    abstractWittMinus * abstractWittMinus = 0 := by
  dsimp [abstractWittMinus]
  rw [smul_mul_smul_comm, CliffordAlgebra.ι_sq_scalar]
  have hQ : q11Form (1, -1) = 0 := by norm_num [q11Form_apply]
  rw [hQ, map_zero, smul_zero]

/-- The abstract Witt nilpotents satisfy the canonical anticommutation relation
`abstractWittPlus * abstractWittMinus + abstractWittMinus * abstractWittPlus = 1`
in `CliffordAlgebra q11Form`. -/
theorem abstractWitt_anticomm_eq_one :
    abstractWittPlus * abstractWittMinus +
      abstractWittMinus * abstractWittPlus = 1 := by
  dsimp [abstractWittPlus, abstractWittMinus]
  rw [smul_mul_smul_comm, smul_mul_smul_comm, ← smul_add,
    CliffordAlgebra.ι_mul_ι_add_swap]
  have h_polar : QuadraticMap.polar q11Form (1, 1) (1, -1) = 4 := by
    norm_num [QuadraticMap.polar, q11Form_apply]
  rw [h_polar, Algebra.algebraMap_eq_smul_one, smul_smul]
  norm_num

/-- The abstract chiral volume element `abstractChiralVolume` is an involution in
`CliffordAlgebra q11Form`: `abstractChiralVolume * abstractChiralVolume = 1`. -/
theorem abstractChiralVolume_sq_eq_one :
    abstractChiralVolume * abstractChiralVolume = 1 := by
  dsimp [abstractChiralVolume]
  have h_ortho :
      CliffordAlgebra.ι q11Form (1, 0) * CliffordAlgebra.ι q11Form (0, 1) +
        CliffordAlgebra.ι q11Form (0, 1) * CliffordAlgebra.ι q11Form (1, 0) = 0 := by
    rw [CliffordAlgebra.ι_mul_ι_add_swap]
    have h_polar : QuadraticMap.polar q11Form (1, 0) (0, 1) = 0 := by
      norm_num [QuadraticMap.polar, q11Form_apply]
    rw [h_polar, map_zero]
  have h_swap :
      CliffordAlgebra.ι q11Form (0, 1) * CliffordAlgebra.ι q11Form (1, 0) =
        -(CliffordAlgebra.ι q11Form (1, 0) * CliffordAlgebra.ι q11Form (0, 1)) :=
    eq_neg_of_add_eq_zero_right h_ortho
  have h10 :
      CliffordAlgebra.ι q11Form (1, 0) * CliffordAlgebra.ι q11Form (1, 0) = 1 := by
    rw [CliffordAlgebra.ι_sq_scalar]
    have hQ : q11Form (1, 0) = 1 := by norm_num [q11Form_apply]
    rw [hQ, map_one]
  have h01 :
      CliffordAlgebra.ι q11Form (0, 1) * CliffordAlgebra.ι q11Form (0, 1) = -1 := by
    rw [CliffordAlgebra.ι_sq_scalar]
    have hQ : q11Form (0, 1) = -1 := by norm_num [q11Form_apply]
    rw [hQ, map_neg, map_one]
  calc
    (CliffordAlgebra.ι q11Form (1, 0) * CliffordAlgebra.ι q11Form (0, 1)) *
        (CliffordAlgebra.ι q11Form (1, 0) * CliffordAlgebra.ι q11Form (0, 1)) =
      CliffordAlgebra.ι q11Form (1, 0) *
        (CliffordAlgebra.ι q11Form (0, 1) * CliffordAlgebra.ι q11Form (1, 0)) *
        CliffordAlgebra.ι q11Form (0, 1) := by
      simp only [mul_assoc]
    _ = -((CliffordAlgebra.ι q11Form (1, 0) * CliffordAlgebra.ι q11Form (1, 0)) *
          (CliffordAlgebra.ι q11Form (0, 1) * CliffordAlgebra.ι q11Form (0, 1))) := by
      rw [h_swap]
      simp only [mul_neg, neg_mul, mul_assoc]
    _ = 1 := by
      rw [h10, one_mul, h01, neg_neg]

/-- Linear map sending $(u, v) \in \mathbb{R} \times \mathbb{R}$ to
$u J_1 + v E_- \in M_2(\mathbb{R})$. -/
def cl11MatrixLinear : (ℝ × ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ where
  toFun v := v.1 • J1 + v.2 • Eminus
  map_add' v w := by
    ext i j
    simp [add_smul]
    ring
  map_smul' r v := by
    ext i j
    simp [Matrix.add_apply, Matrix.smul_apply]
    ring

/-- The $2 \times 2$ matrix generator map `cl11MatrixLinear` satisfies the
Clifford square relation `(cl11MatrixLinear v)^2 = q11Form v • 1`. -/
theorem cl11MatrixLinear_sq (v : ℝ × ℝ) :
    cl11MatrixLinear v * cl11MatrixLinear v =
      algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℝ) (q11Form v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cl11MatrixLinear, J1, Eminus,
      Matrix.mul_apply, Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one] <;>
    ring

/-- The universal Mathlib `CliffordAlgebra` algebra homomorphism
`CliffordAlgebra q11Form →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ`. -/
def cl11MatrixAlgHom : CliffordAlgebra q11Form →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  CliffordAlgebra.lift q11Form ⟨cl11MatrixLinear, cl11MatrixLinear_sq⟩

@[simp]
theorem cl11MatrixAlgHom_ι (v : ℝ × ℝ) :
    cl11MatrixAlgHom (CliffordAlgebra.ι q11Form v) = cl11MatrixLinear v :=
  CliffordAlgebra.lift_ι_apply _ _ v

/-- `cl11MatrixAlgHom` maps `abstractWittPlus` to `cl11NilpotentPlus`. -/
theorem cl11MatrixAlgHom_abstractWittPlus :
    cl11MatrixAlgHom abstractWittPlus = cl11NilpotentPlus := by
  dsimp [abstractWittPlus, cl11NilpotentPlus]
  rw [map_smul, cl11MatrixAlgHom_ι]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cl11MatrixLinear, J1, Eminus]

/-- `cl11MatrixAlgHom` maps `abstractWittMinus` to `cl11NilpotentMinus`. -/
theorem cl11MatrixAlgHom_abstractWittMinus :
    cl11MatrixAlgHom abstractWittMinus = cl11NilpotentMinus := by
  dsimp [abstractWittMinus, cl11NilpotentMinus]
  rw [map_smul, cl11MatrixAlgHom_ι]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cl11MatrixLinear, J1, Eminus]

/-- `cl11MatrixAlgHom` maps `abstractChiralVolume` to `cl11ChiralVolume`. -/
theorem cl11MatrixAlgHom_abstractChiralVolume :
    cl11MatrixAlgHom abstractChiralVolume = cl11ChiralVolume := by
  dsimp [abstractChiralVolume, cl11ChiralVolume]
  rw [map_mul, cl11MatrixAlgHom_ι, cl11MatrixAlgHom_ι]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cl11MatrixLinear, J1, Eminus]

/-- Explicit right-inverse reconstruction map `Matrix (Fin 2) (Fin 2) ℝ → CliffordAlgebra q11Form`
sending any $2 \times 2$ real matrix $M$ to its preimage in `CliffordAlgebra q11Form`. -/
def matrix2ToCliffordQ11 (M : Matrix (Fin 2) (Fin 2) ℝ) : CliffordAlgebra q11Form :=
  ((M 0 0 + M 1 1) / 2) • (1 : CliffordAlgebra q11Form) +
    ((M 1 1 - M 0 0) / 2) • abstractChiralVolume +
    ((M 0 1 + M 1 0) / 2) • CliffordAlgebra.ι q11Form (1, 0) +
    ((M 0 1 - M 1 0) / 2) • CliffordAlgebra.ι q11Form (0, 1)

/-- `cl11MatrixAlgHom` is a right inverse to `matrix2ToCliffordQ11` on all
$M \in M_2(\mathbb{R})$. -/
theorem cl11MatrixAlgHom_matrix2ToCliffordQ11 (M : Matrix (Fin 2) (Fin 2) ℝ) :
    cl11MatrixAlgHom (matrix2ToCliffordQ11 M) = M := by
  dsimp [matrix2ToCliffordQ11]
  simp only [map_add, map_smul, map_one,
    cl11MatrixAlgHom_abstractChiralVolume, cl11MatrixAlgHom_ι]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cl11ChiralVolume, cl11MatrixLinear, J1, Eminus] <;>
    ring

/-- The universal Mathlib representation `cl11MatrixAlgHom` is surjective onto
`Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem cl11MatrixAlgHom_surjective :
    Function.Surjective cl11MatrixAlgHom :=
  fun M => ⟨matrix2ToCliffordQ11 M, cl11MatrixAlgHom_matrix2ToCliffordQ11 M⟩

/-- Explicit non-commutativity witness in `CliffordAlgebra q11Form`: the abstract Witt
nilpotents `abstractWittPlus` and `abstractWittMinus` do not commute. -/
theorem abstractWittPlus_mul_abstractWittMinus_ne_comm :
    abstractWittPlus * abstractWittMinus ≠
      abstractWittMinus * abstractWittPlus := by
  intro h_comm
  have h_entry :
      cl11MatrixAlgHom (abstractWittPlus * abstractWittMinus) 0 0 =
        cl11MatrixAlgHom (abstractWittMinus * abstractWittPlus) 0 0 :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) (congrArg cl11MatrixAlgHom h_comm)
  rw [map_mul, map_mul, cl11MatrixAlgHom_abstractWittPlus,
    cl11MatrixAlgHom_abstractWittMinus] at h_entry
  revert h_entry
  norm_num [cl11NilpotentPlus, cl11NilpotentMinus, J1, Eminus,
    Matrix.mul_apply, Fin.sum_univ_two]

/-!
## Section 2: Native Mathlib `CliffordAlgebra cl33PhaseQuadratic` on the 6D Para-Kähler Phase Space
-/

/-- Coordinate projection on the primal $T^+ \cong \mathbb{R}^3$ factor of
`(Fin 3 → ℝ) × (Fin 3 → ℝ)`. -/
def primalCoordProj (k : Fin 3) : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) →ₗ[ℝ] ℝ :=
  (LinearMap.proj k).comp (LinearMap.fst ℝ (Fin 3 → ℝ) (Fin 3 → ℝ))

/-- Coordinate projection on the dual $T^- \cong (\mathbb{R}^3)^*$ factor of
`(Fin 3 → ℝ) × (Fin 3 → ℝ)`. -/
def dualCoordProj (k : Fin 3) : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) →ₗ[ℝ] ℝ :=
  (LinearMap.proj k).comp (LinearMap.snd ℝ (Fin 3 → ℝ) (Fin 3 → ℝ))

/-- The neutral para-Kähler quadratic form $Q_{3,3}(u, v) = \langle u, v \rangle$
on the 6D phase space `(Fin 3 → ℝ) × (Fin 3 → ℝ)` as a native Mathlib
`QuadraticForm`. -/
def cl33PhaseQuadratic : QuadraticForm ℝ ((Fin 3 → ℝ) × (Fin 3 → ℝ)) :=
  ∑ k : Fin 3, QuadraticMap.linMulLin (primalCoordProj k) (dualCoordProj k)

@[simp]
theorem cl33PhaseQuadratic_apply (z : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    cl33PhaseQuadratic z = vec3Dot z.1 z.2 := by
  simp [cl33PhaseQuadratic, primalCoordProj, dualCoordProj, vec3Dot, Fin.sum_univ_three]

/-- Every pure primal vector $(u, 0) \in T^+$ is isotropic under `cl33PhaseQuadratic`. -/
@[simp]
theorem cl33PhaseQuadratic_primal_zero (u : Fin 3 → ℝ) :
    cl33PhaseQuadratic (u, 0) = 0 := by
  simp [cl33PhaseQuadratic_apply, vec3Dot]

/-- Every pure dual vector $(0, v) \in T^-$ is isotropic under `cl33PhaseQuadratic`. -/
@[simp]
theorem cl33PhaseQuadratic_dual_zero (v : Fin 3 → ℝ) :
    cl33PhaseQuadratic (0, v) = 0 := by
  simp [cl33PhaseQuadratic_apply, vec3Dot]

/-- In the native Mathlib `CliffordAlgebra cl33PhaseQuadratic`, every pure primal
vector $(u, 0) \in T^+$ squares to zero. -/
theorem cl33Phase_primal_ι_sq_zero (u : Fin 3 → ℝ) :
    CliffordAlgebra.ι cl33PhaseQuadratic (u, 0) *
      CliffordAlgebra.ι cl33PhaseQuadratic (u, 0) = 0 := by
  rw [CliffordAlgebra.ι_sq_scalar, cl33PhaseQuadratic_primal_zero, map_zero]

/-- In the native Mathlib `CliffordAlgebra cl33PhaseQuadratic`, every pure dual
vector $(0, v) \in T^-$ squares to zero. -/
theorem cl33Phase_dual_ι_sq_zero (v : Fin 3 → ℝ) :
    CliffordAlgebra.ι cl33PhaseQuadratic (0, v) *
      CliffordAlgebra.ι cl33PhaseQuadratic (0, v) = 0 := by
  rw [CliffordAlgebra.ι_sq_scalar, cl33PhaseQuadratic_dual_zero, map_zero]

private lemma cl33PhaseQuadratic_polar_primal_dual (u v : Fin 3 → ℝ) :
    QuadraticMap.polar cl33PhaseQuadratic (u, (0 : Fin 3 → ℝ)) ((0 : Fin 3 → ℝ), v) =
      vec3Dot u v := by
  simp [QuadraticMap.polar, cl33PhaseQuadratic_apply, vec3Dot]

/-- In `CliffordAlgebra cl33PhaseQuadratic`, the anticommutator of a pure primal
generator $\iota(u, 0)$ and a pure dual generator $\iota(0, v)$ equals the scalar
pairing `vec3Dot u v`. -/
theorem cl33Phase_primal_dual_anticomm (u v : Fin 3 → ℝ) :
    CliffordAlgebra.ι cl33PhaseQuadratic (u, 0) *
        CliffordAlgebra.ι cl33PhaseQuadratic (0, v) +
      CliffordAlgebra.ι cl33PhaseQuadratic (0, v) *
        CliffordAlgebra.ι cl33PhaseQuadratic (u, 0) =
      algebraMap ℝ (CliffordAlgebra cl33PhaseQuadratic) (vec3Dot u v) := by
  rw [CliffordAlgebra.ι_mul_ι_add_swap, cl33PhaseQuadratic_polar_primal_dual]

set_option maxHeartbeats 0

/-- Linear map sending $(u, v) \in \mathbb{R}^3 \times \mathbb{R}^3$ to the $8 \times 8$
Zorn left-multiplication matrix `zornLeftActMatrix (embedVec ⟨u, v⟩)`. -/
def zornPhaseLeftLinear : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) →ₗ[ℝ] Matrix (Fin 8) (Fin 8) ℝ where
  toFun z := zornLeftActMatrix (embedVec ⟨z.1, z.2⟩)
  map_add' z₁ z₂ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [zornLeftActMatrix, zornLeftActFin8, embedVec, fin8ToZorn, zornToFin8,
        zornMul, vec3Dot, vec3Cross] <;>
      ring
  map_smul' r z := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [zornLeftActMatrix, zornLeftActFin8, embedVec, fin8ToZorn, zornToFin8,
        zornMul, vec3Dot, vec3Cross]

/-- The Zorn phase-space linear map satisfies the Clifford square relation
`zornPhaseLeftLinear z * zornPhaseLeftLinear z = algebraMap ℝ _ (cl33PhaseQuadratic z)`. -/
theorem zornPhaseLeftLinear_sq (z : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    zornPhaseLeftLinear z * zornPhaseLeftLinear z =
      algebraMap ℝ (Matrix (Fin 8) (Fin 8) ℝ) (cl33PhaseQuadratic z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zornPhaseLeftLinear, zornLeftActMatrix, zornLeftActFin8, embedVec,
      fin8ToZorn, zornToFin8, zornMul, vec3Dot, vec3Cross, cl33PhaseQuadratic_apply,
      Pi.single_apply, Matrix.mul_apply, Fin.sum_univ_eight,
      Algebra.algebraMap_eq_smul_one] <;>
    ring

/-- Universal Mathlib `CliffordAlgebra` algebra homomorphism lifting Zorn
left multiplication on the 6D para-Kähler phase space:
`CliffordAlgebra cl33PhaseQuadratic →ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ`. -/
def zornPhaseCliffordAlgHom :
    CliffordAlgebra cl33PhaseQuadratic →ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ :=
  CliffordAlgebra.lift cl33PhaseQuadratic ⟨zornPhaseLeftLinear, zornPhaseLeftLinear_sq⟩

@[simp]
theorem zornPhaseCliffordAlgHom_ι (z : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    zornPhaseCliffordAlgHom (CliffordAlgebra.ι cl33PhaseQuadratic z) =
      zornLeftActMatrix (embedVec ⟨z.1, z.2⟩) :=
  CliffordAlgebra.lift_ι_apply _ _ z

/-!
## Section 3: Universal $\operatorname{Cl}(3,3)$ Intertwining on `CliffordAlgebra cl33MajoranaQuadratic` via `CliffordAlgebra.hom_ext`
-/

/-- The 6-mode split quadratic form $Q(c) = \sum_{a=0}^5 \eta_a c_a^2$ of signature
$(+, -, +, -, +, -)$ (`majoranaSignatureR`) on `Fin 6 → ℝ`. -/
def cl33MajoranaQuadratic : QuadraticForm ℝ (Fin 6 → ℝ) :=
  ∑ a : Fin 6,
    (majoranaSignatureR a) •
      QuadraticMap.linMulLin (LinearMap.proj a) (LinearMap.proj a)

@[simp]
theorem cl33MajoranaQuadratic_apply (c : Fin 6 → ℝ) :
    cl33MajoranaQuadratic c = ∑ a : Fin 6, majoranaSignatureR a * (c a) ^ 2 := by
  simp [cl33MajoranaQuadratic, QuadraticMap.linMulLin, pow_two]

/-- Linear map sending $c \in (\operatorname{Fin} 6 \to \mathbb{R})$ to the Jordan–Wigner
linear combination $\sum_{a=0}^5 c_a \Gamma_a \in M_8(\mathbb{R})$. -/
def jwMajoranaLinear : (Fin 6 → ℝ) →ₗ[ℝ] Matrix (Fin 8) (Fin 8) ℝ where
  toFun c := ∑ a : Fin 6, c a • majoranaGenR a
  map_add' c₁ c₂ := by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' r c := by
    simp [mul_smul, Finset.smul_sum]

@[simp]
theorem jwMajoranaLinear_single (a : Fin 6) :
    jwMajoranaLinear (Pi.single a (1 : ℝ)) = majoranaGenR a := by
  simp [jwMajoranaLinear, Pi.single_apply]

/-- The Jordan–Wigner linear map `jwMajoranaLinear` satisfies the Clifford square
relation `jwMajoranaLinear c * jwMajoranaLinear c = algebraMap ℝ _ (cl33MajoranaQuadratic c)`. -/
theorem jwMajoranaLinear_sq (c : Fin 6 → ℝ) :
    jwMajoranaLinear c * jwMajoranaLinear c =
      algebraMap ℝ (Matrix (Fin 8) (Fin 8) ℝ) (cl33MajoranaQuadratic c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jwMajoranaLinear, cl33MajoranaQuadratic_apply, majoranaGenR, majoranaGenZ,
      majoranaSignatureR, majoranaSignatureZ, gamma1PlusZ, gamma1MinusZ,
      gamma2PlusZ, gamma2MinusZ, gamma3PlusZ, gamma3MinusZ,
      Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_eight,
      Algebra.algebraMap_eq_smul_one] <;>
    ring

/-- Universal Mathlib `CliffordAlgebra` algebra homomorphism for the 3-qubit
Jordan–Wigner Majorana representation:
`CliffordAlgebra cl33MajoranaQuadratic →ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ`. -/
def jwMajoranaCliffordAlgHom :
    CliffordAlgebra cl33MajoranaQuadratic →ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ :=
  CliffordAlgebra.lift cl33MajoranaQuadratic ⟨jwMajoranaLinear, jwMajoranaLinear_sq⟩

@[simp]
theorem jwMajoranaCliffordAlgHom_ι (c : Fin 6 → ℝ) :
    jwMajoranaCliffordAlgHom (CliffordAlgebra.ι cl33MajoranaQuadratic c) =
      jwMajoranaLinear c :=
  CliffordAlgebra.lift_ι_apply _ _ c

/-- Linear map sending $c \in (\operatorname{Fin} 6 \to \mathbb{R})$ to the Zorn
left-multiplication linear combination
$\sum_{a=0}^5 c_a L_{\iota(\text{zornMajoranaVec } a)} \in M_8(\mathbb{R})$. -/
def zornMajoranaLinear : (Fin 6 → ℝ) →ₗ[ℝ] Matrix (Fin 8) (Fin 8) ℝ where
  toFun c := ∑ a : Fin 6, c a • zornLeftActMatrix (embedVec (zornMajoranaVec a))
  map_add' c₁ c₂ := by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' r c := by
    simp [mul_smul, Finset.smul_sum]

@[simp]
theorem zornMajoranaLinear_single (a : Fin 6) :
    zornMajoranaLinear (Pi.single a (1 : ℝ)) =
      zornLeftActMatrix (embedVec (zornMajoranaVec a)) := by
  simp [zornMajoranaLinear, Pi.single_apply]

/-- For every $c \in (\operatorname{Fin} 6 \to \mathbb{R})$, `zornMajoranaLinear c`
equals `zornJWConjugator * jwMajoranaLinear c * zornJWConjugator`. -/
theorem zornMajoranaLinear_eq_conjugate (c : Fin 6 → ℝ) :
    zornMajoranaLinear c =
      zornJWConjugator * jwMajoranaLinear c * zornJWConjugator := by
  dsimp [zornMajoranaLinear, jwMajoranaLinear]
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [zornLeftActMatrix_majorana_eq_conjugate a]
  simp

/-- The Zorn Majorana linear map `zornMajoranaLinear` satisfies the Clifford square
relation `zornMajoranaLinear c * zornMajoranaLinear c = algebraMap ℝ _ (cl33MajoranaQuadratic c)`. -/
theorem zornMajoranaLinear_sq (c : Fin 6 → ℝ) :
    zornMajoranaLinear c * zornMajoranaLinear c =
      algebraMap ℝ (Matrix (Fin 8) (Fin 8) ℝ) (cl33MajoranaQuadratic c) := by
  rw [zornMajoranaLinear_eq_conjugate c]
  have h_assoc :
      (zornJWConjugator * jwMajoranaLinear c * zornJWConjugator) *
          (zornJWConjugator * jwMajoranaLinear c * zornJWConjugator) =
        zornJWConjugator *
          (jwMajoranaLinear c * (zornJWConjugator * zornJWConjugator) * jwMajoranaLinear c) *
          zornJWConjugator := by
    simp only [Matrix.mul_assoc]
  rw [h_assoc, zornJWConjugator_sq, Matrix.mul_one, jwMajoranaLinear_sq c]
  rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, zornJWConjugator_sq]

/-- Universal Mathlib `CliffordAlgebra` algebra homomorphism for the Zorn
left-multiplication Majorana representation:
`CliffordAlgebra cl33MajoranaQuadratic →ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ`. -/
def zornMajoranaCliffordAlgHom :
    CliffordAlgebra cl33MajoranaQuadratic →ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ :=
  CliffordAlgebra.lift cl33MajoranaQuadratic ⟨zornMajoranaLinear, zornMajoranaLinear_sq⟩

@[simp]
theorem zornMajoranaCliffordAlgHom_ι (c : Fin 6 → ℝ) :
    zornMajoranaCliffordAlgHom (CliffordAlgebra.ι cl33MajoranaQuadratic c) =
      zornMajoranaLinear c :=
  CliffordAlgebra.lift_ι_apply _ _ c

/-- Conjugation by the involutive orthogonal matrix `zornJWConjugator` as a native
Mathlib `AlgHom` on `Matrix (Fin 8) (Fin 8) ℝ`. -/
def zornJWConjAlgHom : Matrix (Fin 8) (Fin 8) ℝ →ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ where
  toFun M := zornJWConjugator * M * zornJWConjugator
  map_one' := by
    rw [Matrix.mul_one, zornJWConjugator_sq]
  map_mul' M N := by
    calc
      zornJWConjugator * (M * N) * zornJWConjugator =
        zornJWConjugator * (M * (zornJWConjugator * zornJWConjugator) * N) *
          zornJWConjugator := by
        rw [zornJWConjugator_sq, Matrix.mul_one]
      _ = (zornJWConjugator * M * zornJWConjugator) *
            (zornJWConjugator * N * zornJWConjugator) := by
        simp only [Matrix.mul_assoc]
  map_zero' := by simp
  map_add' M N := by
    rw [Matrix.mul_add, Matrix.add_mul]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, zornJWConjugator_sq]

@[simp]
theorem zornJWConjAlgHom_apply (M : Matrix (Fin 8) (Fin 8) ℝ) :
    zornJWConjAlgHom M = zornJWConjugator * M * zornJWConjugator :=
  rfl

/-- **Universal Mathlib `CliffordAlgebra` Intertwining (`AlgHom` equality)**:
By `CliffordAlgebra.hom_ext`, the Zorn `CliffordAlgebra` representation
`zornMajoranaCliffordAlgHom` equals `zornJWConjAlgHom.comp jwMajoranaCliffordAlgHom`
as an `AlgHom` on the entire `CliffordAlgebra cl33MajoranaQuadratic`. -/
theorem zornMajoranaCliffordAlgHom_eq_zornJWConjAlgHom_comp :
    zornMajoranaCliffordAlgHom =
      zornJWConjAlgHom.comp jwMajoranaCliffordAlgHom := by
  apply CliffordAlgebra.hom_ext
  ext a i j
  simp [zornMajoranaLinear_eq_conjugate]

/-- **Universal Pointwise $\operatorname{Cl}(3,3)$ Intertwining**:
For **every** element $X \in \operatorname{CliffordAlgebra}(\text{cl33MajoranaQuadratic})$
(including arbitrary products, blades, spinor projectors, and the chiral volume element),
its Zorn matrix realization equals the `zornJWConjugator`-conjugate of its Jordan–Wigner
matrix realization. -/
theorem zornMajoranaCliffordAlgHom_apply_eq_conjugate
    (X : CliffordAlgebra cl33MajoranaQuadratic) :
    zornMajoranaCliffordAlgHom X =
      zornJWConjugator * jwMajoranaCliffordAlgHom X * zornJWConjugator := by
  rw [zornMajoranaCliffordAlgHom_eq_zornJWConjAlgHom_comp]
  rfl

/-!
## Section 4: The Full 8D $\operatorname{Cl}(3,3)$ Chiral Volume Element $\Omega_{\operatorname{Cl}(3,3)}$
-/

/-- The abstract 6-fold chiral volume element
$\Omega_{\operatorname{Cl}(3,3)} = \iota(e_0)\iota(e_1)\iota(e_2)\iota(e_3)\iota(e_4)\iota(e_5)$
in `CliffordAlgebra cl33MajoranaQuadratic`. -/
def cl33VolumeElement : CliffordAlgebra cl33MajoranaQuadratic :=
  CliffordAlgebra.ι cl33MajoranaQuadratic (Pi.single 0 1) *
    CliffordAlgebra.ι cl33MajoranaQuadratic (Pi.single 1 1) *
    CliffordAlgebra.ι cl33MajoranaQuadratic (Pi.single 2 1) *
    CliffordAlgebra.ι cl33MajoranaQuadratic (Pi.single 3 1) *
    CliffordAlgebra.ι cl33MajoranaQuadratic (Pi.single 4 1) *
    CliffordAlgebra.ι cl33MajoranaQuadratic (Pi.single 5 1)

/-- The integer $8 \times 8$ Jordan–Wigner chiral volume matrix
$\Omega_{\mathrm{JW},\mathbb{Z}} = \gamma_0 \gamma_1 \gamma_2 \gamma_3 \gamma_4 \gamma_5$
in `Matrix (Fin 8) (Fin 8) ℤ`. -/
def jwChiralVolume8Z : Matrix (Fin 8) (Fin 8) ℤ :=
  majoranaGenZ 0 * majoranaGenZ 1 * majoranaGenZ 2 *
    majoranaGenZ 3 * majoranaGenZ 4 * majoranaGenZ 5

/-- The integer chiral volume matrix `jwChiralVolume8Z` is involutive:
$\Omega_{\mathrm{JW},\mathbb{Z}}^2 = I_8$. -/
theorem jwChiralVolume8Z_sq_eq_one :
    jwChiralVolume8Z * jwChiralVolume8Z = 1 := by
  decide

/-- `jwChiralVolume8Z` anticommutes with all six integer Jordan–Wigner Majorana
generators `majoranaGenZ a`. -/
theorem jwChiralVolume8Z_anticomm_majoranaGenZ (a : Fin 6) :
    jwChiralVolume8Z * majoranaGenZ a + majoranaGenZ a * jwChiralVolume8Z = 0 := by
  revert a
  decide

/-- The $8 \times 8$ real Jordan–Wigner chiral volume matrix
$\Omega_{\mathrm{JW}} = \Gamma_0 \Gamma_1 \Gamma_2 \Gamma_3 \Gamma_4 \Gamma_5$,
defined as the image of `cl33VolumeElement` under `jwMajoranaCliffordAlgHom`. -/
def jwChiralVolume8 : Matrix (Fin 8) (Fin 8) ℝ :=
  jwMajoranaCliffordAlgHom cl33VolumeElement

/-- The $8 \times 8$ real Zorn chiral volume matrix
$\Omega_{\mathrm{Zorn}} = L_{z_0} L_{z_1} L_{z_2} L_{z_3} L_{z_4} L_{z_5}$,
defined as the image of `cl33VolumeElement` under `zornMajoranaCliffordAlgHom`. -/
def zornChiralVolume8 : Matrix (Fin 8) (Fin 8) ℝ :=
  zornMajoranaCliffordAlgHom cl33VolumeElement

/-- `jwChiralVolume8` equals the 6-fold product of the Jordan–Wigner Majorana
generators $\Gamma_0 \Gamma_1 \Gamma_2 \Gamma_3 \Gamma_4 \Gamma_5$. -/
theorem jwChiralVolume8_eq_prod :
    jwChiralVolume8 =
      majoranaGenR 0 * majoranaGenR 1 * majoranaGenR 2 *
        majoranaGenR 3 * majoranaGenR 4 * majoranaGenR 5 := by
  simp [jwChiralVolume8, cl33VolumeElement]

/-- `jwChiralVolume8` is the real matrix cast of `jwChiralVolume8Z`. -/
theorem jwChiralVolume8_eq_mapMatrix :
    jwChiralVolume8 = (Int.castRingHom ℝ).mapMatrix jwChiralVolume8Z := by
  rw [jwChiralVolume8_eq_prod]
  dsimp [jwChiralVolume8Z, majoranaGenR]
  simp only [map_mul]

/-- `jwChiralVolume8` is involutive: $\Omega_{\mathrm{JW}}^2 = I_8$. -/
theorem jwChiralVolume8_sq_eq_one :
    jwChiralVolume8 * jwChiralVolume8 = 1 := by
  rw [jwChiralVolume8_eq_mapMatrix, ← map_mul, jwChiralVolume8Z_sq_eq_one, map_one]

/-- `jwChiralVolume8` anticommutes with all six Jordan–Wigner Majorana generators
$\Gamma_a$ ($a \in \operatorname{Fin} 6$). -/
theorem jwChiralVolume8_anticomm_majoranaGenR (a : Fin 6) :
    jwChiralVolume8 * majoranaGenR a + majoranaGenR a * jwChiralVolume8 = 0 := by
  rw [jwChiralVolume8_eq_mapMatrix]
  dsimp [majoranaGenR]
  rw [← map_mul, ← map_mul, ← map_add,
    jwChiralVolume8Z_anticomm_majoranaGenZ a, map_zero]

/-- The 0-th Jordan–Wigner Majorana generator $\Gamma_0 \in M_8(\mathbb{R})$. -/
abbrev jwMajoranaGen0 : Matrix (Fin 8) (Fin 8) ℝ := majoranaGenR 0

/-- Closed anticommutativity witness on `Matrix (Fin 8) (Fin 8) ℝ`:
`jwChiralVolume8` and `jwMajoranaGen0` anticommute. -/
theorem jwChiralVolume8_anticomm_jwMajoranaGen0 :
    jwChiralVolume8 * jwMajoranaGen0 + jwMajoranaGen0 * jwChiralVolume8 = 0 :=
  jwChiralVolume8_anticomm_majoranaGenR 0

/-- By the universal `CliffordAlgebra` intertwining theorem
`zornMajoranaCliffordAlgHom_apply_eq_conjugate`, `zornChiralVolume8` equals
`zornJWConjugator * jwChiralVolume8 * zornJWConjugator`. -/
theorem zornChiralVolume8_eq_conjugate :
    zornChiralVolume8 =
      zornJWConjugator * jwChiralVolume8 * zornJWConjugator :=
  zornMajoranaCliffordAlgHom_apply_eq_conjugate cl33VolumeElement

/-- `zornChiralVolume8` is involutive: $\Omega_{\mathrm{Zorn}}^2 = I_8$. -/
theorem zornChiralVolume8_sq_eq_one :
    zornChiralVolume8 * zornChiralVolume8 = 1 := by
  rw [zornChiralVolume8_eq_conjugate]
  change zornJWConjAlgHom jwChiralVolume8 * zornJWConjAlgHom jwChiralVolume8 = 1
  rw [← map_mul, jwChiralVolume8_sq_eq_one, map_one]

/-- On the vacuum coordinate `0` ($|000\rangle$), `zornJWConjugator` reverses the
chiral volume sign: `zornChiralVolume8 0 0 = -jwChiralVolume8 0 0`. -/
theorem zornChiralVolume8_vacuum_eq_neg_jwChiralVolume8 :
    zornChiralVolume8 0 0 = -jwChiralVolume8 0 0 := by
  have h00_jw : jwChiralVolume8Z 0 0 = 1 := by decide
  have h77_jw : jwChiralVolume8Z 7 7 = -1 := by decide
  rw [zornChiralVolume8_eq_conjugate, jwChiralVolume8_eq_mapMatrix]
  have h_swap :
      (zornJWConjugator * (Int.castRingHom ℝ).mapMatrix jwChiralVolume8Z *
        zornJWConjugator) 0 0 =
        ((Int.castRingHom ℝ).mapMatrix jwChiralVolume8Z) 7 7 := by
    simp [zornJWConjugator, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_eight]
  rw [h_swap]
  change (jwChiralVolume8Z 7 7 : ℝ) = -(jwChiralVolume8Z 0 0 : ℝ)
  rw [h00_jw, h77_jw]
  norm_num

/-- On the top-state coordinate `7` ($|111\rangle$), `zornJWConjugator` reverses the
chiral volume sign: `zornChiralVolume8 7 7 = -jwChiralVolume8 7 7`. -/
theorem zornChiralVolume8_top_eq_neg_jwChiralVolume8 :
    zornChiralVolume8 7 7 = -jwChiralVolume8 7 7 := by
  have h00_jw : jwChiralVolume8Z 0 0 = 1 := by decide
  have h77_jw : jwChiralVolume8Z 7 7 = -1 := by decide
  rw [zornChiralVolume8_eq_conjugate, jwChiralVolume8_eq_mapMatrix]
  have h_swap :
      (zornJWConjugator * (Int.castRingHom ℝ).mapMatrix jwChiralVolume8Z *
        zornJWConjugator) 7 7 =
        ((Int.castRingHom ℝ).mapMatrix jwChiralVolume8Z) 0 0 := by
    simp [zornJWConjugator, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_eight]
  rw [h_swap]
  change (jwChiralVolume8Z 0 0 : ℝ) = -(jwChiralVolume8Z 7 7 : ℝ)
  rw [h00_jw, h77_jw]
  norm_num

/-- `zornChiralVolume8` anticommutes with all six Zorn Majorana left-multiplication
matrices $L_{\iota(z_a)}$ ($a \in \operatorname{Fin} 6$). -/
theorem zornChiralVolume8_anticomm_zornMajorana (a : Fin 6) :
    zornChiralVolume8 * zornLeftActMatrix (embedVec (zornMajoranaVec a)) +
      zornLeftActMatrix (embedVec (zornMajoranaVec a)) * zornChiralVolume8 = 0 := by
  rw [zornChiralVolume8_eq_conjugate, zornLeftActMatrix_majorana_eq_conjugate a]
  change zornJWConjAlgHom jwChiralVolume8 * zornJWConjAlgHom (majoranaGenR a) +
      zornJWConjAlgHom (majoranaGenR a) * zornJWConjAlgHom jwChiralVolume8 = 0
  rw [← map_mul, ← map_mul, ← map_add,
    jwChiralVolume8_anticomm_majoranaGenR a, map_zero]

/-!
## Section 5: Native Mathlib Submodule Quotient Equivalences $V \⧸ T^- \simeqₗ[ℝ] T^+$ and $V \⧸ T^+ \simeqₗ[ℝ] T^-$
-/

section SubmoduleQuotientEquiv

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Native Mathlib linear equivalence identifying the quotient of $V$ by the
$-1$ covector vacuum kernel sheet `covectorVacuumSheet K = ker(K + id)` with the
$+1$ primal sheet `primalSheet K = ker(K - id)`, constructed via
`Submodule.quotientEquivOfIsCompl`. -/
def quotientCovectorVacuumEquivPrimalSheet
    (K : V →ₗ[ℝ] V) (hK : ∀ v, K (K v) = v) :
    (V ⧸ SuperGrassmannian.covectorVacuumSheet K) ≃ₗ[ℝ]
      SuperGrassmannian.primalSheet K :=
  Submodule.quotientEquivOfIsCompl
    (SuperGrassmannian.covectorVacuumSheet K)
    (SuperGrassmannian.primalSheet K)
    (isCompl_primalSheet_covectorVacuumSheet K hK).symm

/-- Native Mathlib linear equivalence identifying the quotient of $V$ by the
$+1$ primal kernel sheet `primalSheet K = ker(K - id)` with the
$-1$ covector vacuum sheet `covectorVacuumSheet K = ker(K + id)`, constructed via
`Submodule.quotientEquivOfIsCompl`. -/
def quotientPrimalSheetEquivCovectorVacuum
    (K : V →ₗ[ℝ] V) (hK : ∀ v, K (K v) = v) :
    (V ⧸ SuperGrassmannian.primalSheet K) ≃ₗ[ℝ]
      SuperGrassmannian.covectorVacuumSheet K :=
  Submodule.quotientEquivOfIsCompl
    (SuperGrassmannian.primalSheet K)
    (SuperGrassmannian.covectorVacuumSheet K)
    (isCompl_primalSheet_covectorVacuumSheet K hK)

/-- Applying `quotientCovectorVacuumEquivPrimalSheet.symm` to any element `x` of
`primalSheet K` recovers its coset `Submodule.Quotient.mk x` modulo
`covectorVacuumSheet K`. -/
@[simp]
theorem quotientCovectorVacuumEquivPrimalSheet_symm_apply
    (K : V →ₗ[ℝ] V) (hK : ∀ v, K (K v) = v)
    (x : SuperGrassmannian.primalSheet K) :
    (quotientCovectorVacuumEquivPrimalSheet K hK).symm x =
      Submodule.Quotient.mk (x : V) :=
  rfl

/-- Applying `quotientPrimalSheetEquivCovectorVacuum.symm` to any element `y` of
`covectorVacuumSheet K` recovers its coset `Submodule.Quotient.mk y` modulo
`primalSheet K`. -/
@[simp]
theorem quotientPrimalSheetEquivCovectorVacuum_symm_apply
    (K : V →ₗ[ℝ] V) (hK : ∀ v, K (K v) = v)
    (y : SuperGrassmannian.covectorVacuumSheet K) :
    (quotientPrimalSheetEquivCovectorVacuum K hK).symm y =
      Submodule.Quotient.mk (y : V) :=
  rfl

/-- For every ambient vector `v : V`, projecting `v` to the quotient
`V ⧸ covectorVacuumSheet K` and applying `quotientCovectorVacuumEquivPrimalSheet`
recovers the spectral projection `paraProjectorPlus K v` inside `primalSheet K`. -/
theorem quotientCovectorVacuumEquivPrimalSheet_mk_coe
    (K : V →ₗ[ℝ] V) (hK : ∀ v, K (K v) = v) (v : V) :
    ((quotientCovectorVacuumEquivPrimalSheet K hK
        (Submodule.Quotient.mk v) : SuperGrassmannian.primalSheet K) : V) =
      SuperGrassmannian.paraProjectorPlus K v := by
  have hx_mem :
      SuperGrassmannian.paraProjectorPlus K v ∈ SuperGrassmannian.primalSheet K :=
    (SuperGrassmannian.mem_primalSheet_iff K hK
      (SuperGrassmannian.paraProjectorPlus K v)).mpr
      (SuperGrassmannian.paraProjectorPlus_idempotent K hK v)
  let x : SuperGrassmannian.primalSheet K :=
    ⟨SuperGrassmannian.paraProjectorPlus K v, hx_mem⟩
  have hv_decomp :
      v - (x : V) ∈ SuperGrassmannian.covectorVacuumSheet K := by
    have h_sub : v - SuperGrassmannian.paraProjectorPlus K v =
        SuperGrassmannian.paraProjectorMinus K v :=
      sub_eq_of_eq_add' (SuperGrassmannian.paraProjectors_sum_id K v).symm
    change v - SuperGrassmannian.paraProjectorPlus K v ∈
      SuperGrassmannian.covectorVacuumSheet K
    rw [h_sub]
    exact (SuperGrassmannian.mem_covectorVacuumSheet_iff K hK
      (SuperGrassmannian.paraProjectorMinus K v)).mpr
      (SuperGrassmannian.paraProjectorMinus_idempotent K hK v)
  have h_mk :
      (Submodule.Quotient.mk v : V ⧸ SuperGrassmannian.covectorVacuumSheet K) =
        Submodule.Quotient.mk (x : V) := by
    rw [Submodule.Quotient.eq]
    exact hv_decomp
  rw [h_mk, ← quotientCovectorVacuumEquivPrimalSheet_symm_apply K hK x,
    LinearEquiv.apply_symm_apply]

/-- For every ambient vector `v : V`, projecting `v` to the quotient
`V ⧸ primalSheet K` and applying `quotientPrimalSheetEquivCovectorVacuum`
recovers the spectral projection `paraProjectorMinus K v` inside
`covectorVacuumSheet K`. -/
theorem quotientPrimalSheetEquivCovectorVacuum_mk_coe
    (K : V →ₗ[ℝ] V) (hK : ∀ v, K (K v) = v) (v : V) :
    ((quotientPrimalSheetEquivCovectorVacuum K hK
        (Submodule.Quotient.mk v) : SuperGrassmannian.covectorVacuumSheet K) : V) =
      SuperGrassmannian.paraProjectorMinus K v := by
  have hy_mem :
      SuperGrassmannian.paraProjectorMinus K v ∈
        SuperGrassmannian.covectorVacuumSheet K :=
    (SuperGrassmannian.mem_covectorVacuumSheet_iff K hK
      (SuperGrassmannian.paraProjectorMinus K v)).mpr
      (SuperGrassmannian.paraProjectorMinus_idempotent K hK v)
  let y : SuperGrassmannian.covectorVacuumSheet K :=
    ⟨SuperGrassmannian.paraProjectorMinus K v, hy_mem⟩
  have hv_decomp :
      v - (y : V) ∈ SuperGrassmannian.primalSheet K := by
    have h_sub : v - SuperGrassmannian.paraProjectorMinus K v =
        SuperGrassmannian.paraProjectorPlus K v :=
      sub_eq_of_eq_add (SuperGrassmannian.paraProjectors_sum_id K v).symm
    change v - SuperGrassmannian.paraProjectorMinus K v ∈
      SuperGrassmannian.primalSheet K
    rw [h_sub]
    exact (SuperGrassmannian.mem_primalSheet_iff K hK
      (SuperGrassmannian.paraProjectorPlus K v)).mpr
      (SuperGrassmannian.paraProjectorPlus_idempotent K hK v)
  have h_mk :
      (Submodule.Quotient.mk v : V ⧸ SuperGrassmannian.primalSheet K) =
        Submodule.Quotient.mk (y : V) := by
    rw [Submodule.Quotient.eq]
    exact hv_decomp
  rw [h_mk, ← quotientPrimalSheetEquivCovectorVacuum_symm_apply K hK y,
    LinearEquiv.apply_symm_apply]

end SubmoduleQuotientEquiv

end InfoGeometry.Synthesis.MathlibCliffordUniversalLiftSynthesis
