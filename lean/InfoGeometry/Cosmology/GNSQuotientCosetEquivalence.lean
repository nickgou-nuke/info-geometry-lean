/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-!
# GNS Quotient Module, Projective Coset Equivalence, and CAR Intertwining

This module bridges the finite-dimensional operator algebraic GNS representation,
the projective coset spacetime geometry $G/P$, and the Krein-Bogoliubov isometric flow
for the explicit $2 \times 2$ real matrix model $M_2(\mathbb{R})$:

1. **GNS Quotient Representation**:
   Constructs the GNS null radical as an explicit submodule $\mathcal{N}_\omega = \ker(\mathrm{eval}_\Omega)$
   and proves the First Isomorphism Theorem:
   $(M_2(\mathbb{R}) / \mathcal{N}_\omega) \simeq_L \mathbb{R}^2$.
   Establishes that left operator multiplication on the quotient intertwines with standard matrix-vector action.

2. **Orbit-Stabilizer Coset Equivalence**:
   Formulates the 1D projective ray equivalence on the punctured representation space $\mathbb{R}^2 \setminus \{0\}$,
   and proves that two elements $g_1, g_2 \in \mathrm{SL}(2, \mathbb{R})$ generate the same projective vacuum ray
   if and only if $g_1^{-1} g_2$ belongs to the upper-triangular parabolic subgroup $P$.

3. **Projective GNS State Space Equivalence**:
   Constructs the projective quotient $\mathbb{P}(M_2(\mathbb{R}) / \mathcal{N}_\omega)$ and proves it is
   canonically bijective to the real projective line $\mathbb{P}^1(\mathbb{R})$.

4. **Krein-Bogoliubov Flow and CAR Anticommutator Intertwining**:
   Proves that the Bogoliubov boost family $B(\theta)$ preserves the indefinite Krein metric $\eta = \operatorname{diag}(1, -1)$
   as an exact isometry ($B^\dagger B = 1$), and preserves the fermionic Canonical Anticommutation Relations (CAR)
   under $\mathrm{SL}(2, \mathbb{R})$ adjoint action.

All results are stated strictly within the explicit $2 \times 2$ real matrix algebra and 2-component spinor model.
-/

namespace InfoGeometry.Cosmology.GNSQuotientCoset

open Matrix
open scoped Matrix

/-! ### 1. The Cyclic Vacuum & GNS Submodule -/

/-- The cyclic vacuum state vector |Ω⟩ = (1, 0)ᵀ in the 2-component spinor representation. -/
def cyclicVacuum : Fin 2 → ℝ := ![1, 0]

/-- The cyclic vacuum is non-zero. -/
theorem cyclicVacuum_ne_zero : cyclicVacuum ≠ 0 := by
  intro h
  have h0 := congr_fun h 0
  simp [cyclicVacuum] at h0

/-- The linear evaluation map sending an operator A ∈ M₂(ℝ) to A|Ω⟩ ∈ ℝ². -/
def evalVacuum : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun A := mulVec A cyclicVacuum
  map_add' A B := by
    ext i
    simp only [add_mulVec, Pi.add_apply]
  map_smul' c A := by
    ext i
    simp only [smul_mulVec, Pi.smul_apply, RingHom.id_apply]

/-- The GNS null radical as a formal ℝ-submodule of M₂(ℝ). -/
def gnsRadicalSubmodule : Submodule ℝ (Matrix (Fin 2) (Fin 2) ℝ) :=
  LinearMap.ker evalVacuum

/-- Explicit characterization: A ∈ ker(evalVacuum) iff its first column is zero. -/
theorem mem_gnsRadicalSubmodule_iff (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A ∈ gnsRadicalSubmodule ↔ A 0 0 = 0 ∧ A 1 0 = 0 := by
  dsimp [gnsRadicalSubmodule, LinearMap.mem_ker, evalVacuum]
  constructor
  · intro h
    have h0 := congr_fun h 0
    have h1 := congr_fun h 1
    simp [mulVec, dotProduct, cyclicVacuum, Fin.sum_univ_two] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i <;> simp [mulVec, dotProduct, cyclicVacuum, Fin.sum_univ_two, h0, h1]

/-- The evaluation map evalVacuum is surjective: every vector in ℝ² is in the range. -/
theorem evalVacuum_surjective : Function.Surjective evalVacuum := by
  intro v
  use !![v 0, 0; v 1, 0]
  dsimp [evalVacuum]
  ext i
  fin_cases i <;> simp [mulVec, dotProduct, cyclicVacuum, Fin.sum_univ_two]

/-- The First Isomorphism Theorem for the GNS Representation:
    The GNS quotient module M₂(ℝ) / 𝒩_ω is linearly isomorphic to ℝ². -/
noncomputable def gnsQuotientEquiv :
    (Matrix (Fin 2) (Fin 2) ℝ ⧸ gnsRadicalSubmodule) ≃ₗ[ℝ] (Fin 2 → ℝ) :=
  evalVacuum.quotKerEquivOfSurjective evalVacuum_surjective

/-- The GNS quotient equivalence computes the vacuum evaluation on representatives. -/
theorem gnsQuotientEquiv_mk (A : Matrix (Fin 2) (Fin 2) ℝ) :
    gnsQuotientEquiv (Submodule.Quotient.mk A) = mulVec A cyclicVacuum :=
  rfl

/-- Module Intertwining Theorem:
    Left matrix multiplication on M₂(ℝ) pushes forward under the GNS quotient
    to standard matrix-vector multiplication on the representation space ℝ². -/
theorem gns_quotient_left_action_intertwining
    (A X : Matrix (Fin 2) (Fin 2) ℝ) :
    gnsQuotientEquiv (Submodule.Quotient.mk (A * X)) =
      mulVec A (gnsQuotientEquiv (Submodule.Quotient.mk X)) := by
  rw [gnsQuotientEquiv_mk, gnsQuotientEquiv_mk]
  simp only [← mulVec_mulVec]

/-! ### 2. The Projective Ray Equivalence & Orbit-Stabilizer Coset Identification -/

/-- Non-zero spinor bundle (the punctured plane ℝ² \ {0}). -/
def PuncturedSpinor := { v : Fin 2 → ℝ // v ≠ 0 }

/-- Equivalence relation defining 1D projective rays: v ~ w iff v = c • w for c ≠ 0. -/
def RayEquiv (v w : Fin 2 → ℝ) : Prop :=
  ∃ c : ℝ, c ≠ 0 ∧ v = c • w

theorem rayEquiv_refl (v : Fin 2 → ℝ) : RayEquiv v v :=
  ⟨1, one_ne_zero, by simp⟩

theorem rayEquiv_symm {v w : Fin 2 → ℝ} (h : RayEquiv v w) : RayEquiv w v := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem rayEquiv_trans {u v w : Fin 2 → ℝ} (h1 : RayEquiv u v) (h2 : RayEquiv v w) : RayEquiv u w := by
  obtain ⟨c1, hc1, rfl⟩ := h1
  obtain ⟨c2, hc2, rfl⟩ := h2
  refine ⟨c1 * c2, mul_ne_zero hc1 hc2, by rw [smul_smul]⟩

/-- The Setoid on non-zero spinors defining projective space ℙ¹(ℝ). -/
def raySetoid : Setoid PuncturedSpinor where
  r v w := RayEquiv v.1 w.1
  iseqv := {
    refl := fun v => rayEquiv_refl v.1
    symm := fun h => rayEquiv_symm h
    trans := fun h1 h2 => rayEquiv_trans h1 h2
  }

/-- The real projective line ℙ¹(ℝ) as the quotient of punctured spinors by non-zero scaling. -/
def ProjectiveLine := Quotient raySetoid

/-- Membership in SL(2, ℝ). -/
def IsSL2 (g : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  g.det = 1

/-- Upper-triangular parabolic subgroup P fixing the ray of |Ω⟩. -/
def IsParabolicUpper (g : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  g 1 0 = 0

/-- Computable algebraic inverse for SL(2, ℝ). -/
def sl2Inv (g : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![g 1 1, -g 0 1; -g 1 0, g 0 0]

theorem sl2Inv_mul (g : Matrix (Fin 2) (Fin 2) ℝ) (hg : IsSL2 g) :
    sl2Inv g * g = 1 := by
  ext i j
  dsimp [sl2Inv]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue, Matrix.one_apply]
  have hdet : g.det = g 0 0 * g 1 1 - g 0 1 * g 1 0 := Matrix.det_fin_two g
  dsimp [IsSL2] at hg
  fin_cases i <;> fin_cases j <;> simp
  · calc g 1 1 * g 0 0 + -(g 0 1 * g 1 0)
        = g 0 0 * g 1 1 - g 0 1 * g 1 0 := by ring
      _ = g.det := hdet.symm
      _ = 1 := hg
  · ring
  · ring
  · calc -(g 1 0 * g 0 1) + g 0 0 * g 1 1
        = g 0 0 * g 1 1 - g 0 1 * g 1 0 := by ring
      _ = g.det := hdet.symm
      _ = 1 := hg

theorem mul_sl2Inv (g : Matrix (Fin 2) (Fin 2) ℝ) (hg : IsSL2 g) :
    g * sl2Inv g = 1 := by
  ext i j
  dsimp [sl2Inv]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue, Matrix.one_apply]
  have hdet : g.det = g 0 0 * g 1 1 - g 0 1 * g 1 0 := Matrix.det_fin_two g
  dsimp [IsSL2] at hg
  fin_cases i <;> fin_cases j <;> simp
  · calc g 0 0 * g 1 1 + -(g 0 1 * g 1 0)
        = g 0 0 * g 1 1 - g 0 1 * g 1 0 := by ring
      _ = g.det := hdet.symm
      _ = 1 := hg
  · ring
  · ring
  · calc -(g 1 0 * g 0 1) + g 1 1 * g 0 0
        = g 0 0 * g 1 1 - g 0 1 * g 1 0 := by ring
      _ = g.det := hdet.symm
      _ = 1 := hg

/-- An element of SL(2, ℝ) preserves non-zero vectors. -/
theorem mulVec_ne_zero_of_isSL2 (g : Matrix (Fin 2) (Fin 2) ℝ) (hg : IsSL2 g)
    (v : Fin 2 → ℝ) (hv : v ≠ 0) : mulVec g v ≠ 0 := by
  intro h
  have h_zero : sl2Inv g *ᵥ (g *ᵥ v) = 0 := by
    rw [h, mulVec_zero]
  rw [mulVec_mulVec, sl2Inv_mul g hg, one_mulVec] at h_zero
  exact hv h_zero

/-- Punctured spinor resulting from acting with SL(2, ℝ) on the vacuum. -/
def gVacuum (g : Matrix (Fin 2) (Fin 2) ℝ) (hg : IsSL2 g) : PuncturedSpinor :=
  ⟨mulVec g cyclicVacuum, mulVec_ne_zero_of_isSL2 g hg cyclicVacuum cyclicVacuum_ne_zero⟩

/-- The Orbit-Stabilizer Coset Equivalence Theorem:
    Two group elements g₁, g₂ in SL(2, ℝ) generate the same projective vacuum ray
    if and only if g₁⁻¹ g₂ belongs to the parabolic subgroup P. -/
theorem rayEquiv_vacuum_iff_parabolic
    (g1 g2 : Matrix (Fin 2) (Fin 2) ℝ) (hg1 : IsSL2 g1) (hg2 : IsSL2 g2) :
    RayEquiv (mulVec g1 cyclicVacuum) (mulVec g2 cyclicVacuum) ↔
      IsParabolicUpper (sl2Inv g1 * g2) := by
  constructor
  · rintro ⟨c, hc, h_eq⟩
    dsimp [IsParabolicUpper]
    have h_inv : sl2Inv g1 *ᵥ (g1 *ᵥ cyclicVacuum) =
                 sl2Inv g1 *ᵥ (c • (g2 *ᵥ cyclicVacuum)) := by rw [h_eq]
    rw [mulVec_mulVec, sl2Inv_mul g1 hg1, one_mulVec] at h_inv
    rw [mulVec_smul, mulVec_mulVec] at h_inv
    have h1 := congr_fun h_inv 1
    dsimp [cyclicVacuum, mulVec, dotProduct] at h1
    simp only [Fin.sum_univ_two, Fin.isValue, cons_val_zero, cons_val_one, mul_one, mul_zero, add_zero] at h1
    have h_zero : c * (sl2Inv g1 * g2) 1 0 = 0 := h1.symm
    cases mul_eq_zero.mp h_zero with
    | inl hc0 => exact False.elim (hc hc0)
    | inr hX0 => exact hX0
  · intro hP
    have h_prod : IsSL2 (sl2Inv g1 * g2) := by
      dsimp [IsSL2]
      rw [det_mul]
      have hdet1 : (sl2Inv g1).det = 1 := by
        have h_id := congr_arg Matrix.det (sl2Inv_mul g1 hg1)
        rw [det_mul, det_one] at h_id
        dsimp [IsSL2] at hg1
        rw [hg1, mul_one] at h_id
        exact h_id
      dsimp [IsSL2] at hg2
      rw [hdet1, hg2, mul_one]
    have h_entry : (sl2Inv g1 * g2) 0 0 ≠ 0 := by
      intro hz
      have hdet := Matrix.det_fin_two (sl2Inv g1 * g2)
      dsimp [IsSL2] at h_prod
      dsimp [IsParabolicUpper] at hP
      rw [hz, hP] at hdet
      ring_nf at hdet
      linarith
    apply rayEquiv_symm
    use (sl2Inv g1 * g2) 0 0
    constructor
    · exact h_entry
    · have h_act : (sl2Inv g1 * g2) *ᵥ cyclicVacuum = (sl2Inv g1 * g2) 0 0 • cyclicVacuum := by
        ext i
        fin_cases i
        · simp [mulVec, cyclicVacuum, dotProduct, Fin.sum_univ_two]
        · dsimp [IsParabolicUpper] at hP
          simp [mulVec, cyclicVacuum, dotProduct, Fin.sum_univ_two, hP]
      have h_left : g1 *ᵥ ((sl2Inv g1 * g2) *ᵥ cyclicVacuum) =
                    g1 *ᵥ ((sl2Inv g1 * g2) 0 0 • cyclicVacuum) := by rw [h_act]
      rw [mulVec_mulVec, ← mul_assoc, mul_sl2Inv g1 hg1, one_mul] at h_left
      rw [mulVec_smul] at h_left
      exact h_left

/-! ### 3. Projective GNS Quotient Space and Canonical Bijection -/

/-- The type of non-zero elements of the GNS quotient module. -/
def PuncturedGNSQuotient := { x : (Matrix (Fin 2) (Fin 2) ℝ ⧸ gnsRadicalSubmodule) // x ≠ 0 }

/-- 1D Projective ray equivalence on the GNS quotient space. -/
def RayEquivGNS (x y : Matrix (Fin 2) (Fin 2) ℝ ⧸ gnsRadicalSubmodule) : Prop :=
  ∃ c : ℝ, c ≠ 0 ∧ x = c • y

theorem rayEquivGNS_refl (x : Matrix (Fin 2) (Fin 2) ℝ ⧸ gnsRadicalSubmodule) : RayEquivGNS x x :=
  ⟨1, one_ne_zero, by simp⟩

theorem rayEquivGNS_symm {x y : Matrix (Fin 2) (Fin 2) ℝ ⧸ gnsRadicalSubmodule} (h : RayEquivGNS x y) : RayEquivGNS y x := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem rayEquivGNS_trans {x y z : Matrix (Fin 2) (Fin 2) ℝ ⧸ gnsRadicalSubmodule}
    (h1 : RayEquivGNS x y) (h2 : RayEquivGNS y z) : RayEquivGNS x z := by
  obtain ⟨c1, hc1, rfl⟩ := h1
  obtain ⟨c2, hc2, rfl⟩ := h2
  refine ⟨c1 * c2, mul_ne_zero hc1 hc2, by rw [smul_smul]⟩

/-- Setoid on non-zero GNS quotient vectors defining ℙ(ℋ_GNS). -/
def raySetoidGNS : Setoid PuncturedGNSQuotient where
  r x y := RayEquivGNS x.1 y.1
  iseqv := {
    refl := fun x => rayEquivGNS_refl x.1
    symm := fun h => rayEquivGNS_symm h
    trans := fun h1 h2 => rayEquivGNS_trans h1 h2
  }

/-- The projective GNS state space ℙ(M₂(ℝ) / 𝒩_ω). -/
def ProjectiveGNS := Quotient raySetoidGNS

/-- Forward map from PuncturedGNSQuotient to PuncturedSpinor under gnsQuotientEquiv. -/
noncomputable def puncturedGNSForward (x : PuncturedGNSQuotient) : PuncturedSpinor :=
  ⟨gnsQuotientEquiv x.1, fun h => x.2 (gnsQuotientEquiv.map_eq_zero_iff.mp h)⟩

/-- Inverse map from PuncturedSpinor to PuncturedGNSQuotient under gnsQuotientEquiv.symm. -/
noncomputable def puncturedGNSInverse (v : PuncturedSpinor) : PuncturedGNSQuotient :=
  ⟨gnsQuotientEquiv.symm v.1, fun h => v.2 (gnsQuotientEquiv.symm.map_eq_zero_iff.mp h)⟩

/-- Ray equivalence is preserved by gnsQuotientEquiv. -/
theorem rayEquiv_iff_rayEquivGNS (x y : Matrix (Fin 2) (Fin 2) ℝ ⧸ gnsRadicalSubmodule) :
    RayEquiv (gnsQuotientEquiv x) (gnsQuotientEquiv y) ↔ RayEquivGNS x y := by
  constructor
  · rintro ⟨c, hc, h_eq⟩
    refine ⟨c, hc, ?_⟩
    apply gnsQuotientEquiv.injective
    rw [map_smul, h_eq]
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c, hc, by rw [map_smul]⟩

/-- Canonical Projective Equivalence:
    The projective GNS state space ℙ(M₂(ℝ) / 𝒩_ω) is canonically bijective
    to the projective line ℙ¹(ℝ). -/
noncomputable def projectiveGNSEquivProjectiveLine : ProjectiveGNS ≃ ProjectiveLine where
  toFun := Quotient.map puncturedGNSForward (fun a b hab => by
    dsimp [puncturedGNSForward]
    exact (rayEquiv_iff_rayEquivGNS a.1 b.1).mpr hab)
  invFun := Quotient.map puncturedGNSInverse (fun a b hab => by
    dsimp [puncturedGNSInverse]
    have hab_equiv : RayEquiv a.1 b.1 := hab
    have h_symm : RayEquiv (gnsQuotientEquiv (gnsQuotientEquiv.symm a.1))
                           (gnsQuotientEquiv (gnsQuotientEquiv.symm b.1)) := by
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      exact hab_equiv
    exact (rayEquiv_iff_rayEquivGNS (gnsQuotientEquiv.symm a.1) (gnsQuotientEquiv.symm b.1)).mp h_symm)
  left_inv q := by
    induction q using Quotient.ind
    dsimp [Quotient.map]
    apply Quotient.sound
    dsimp [puncturedGNSInverse, puncturedGNSForward]
    simp only [LinearEquiv.symm_apply_apply]
    exact rayEquivGNS_refl _
  right_inv q := by
    induction q using Quotient.ind
    dsimp [Quotient.map]
    apply Quotient.sound
    dsimp [puncturedGNSInverse, puncturedGNSForward]
    simp only [LinearEquiv.apply_symm_apply]
    exact rayEquiv_refl _

/-! ### 4. Krein Bogoliubov Flow and CAR Anticommutator Preservation -/

/-- Anticommutator of two 2×2 matrices: {A, B} = AB + BA. -/
def anticomm (A B : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  A * B + B * A

/-- Fermionic root / ladder operators in M₂(ℝ). -/
def rootPlus : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1;
     0, 0]

def rootMinus : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 0;
     1, 0]

/-- The ladder operators are nilpotent. -/
theorem rootPlus_sq : rootPlus * rootPlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootPlus, Matrix.mul_apply, Fin.sum_univ_two]

theorem rootMinus_sq : rootMinus * rootMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootMinus, Matrix.mul_apply, Fin.sum_univ_two]

/-- Canonical Anticommutation Relation (CAR): {rootPlus, rootMinus} = 1. -/
theorem anticomm_rootPlus_rootMinus : anticomm rootPlus rootMinus = 1 := by
  ext i j
  dsimp [anticomm, rootPlus, rootMinus]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> norm_num

/-- Adjoint / conjugation action of SL(2, ℝ) on M₂(ℝ). -/
def conjSL2 (g : Matrix (Fin 2) (Fin 2) ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  g * A * sl2Inv g

/-- Anticommutator intertwining under SL(2, ℝ) conjugation:
    Conj_g({A, B}) = {Conj_g(A), Conj_g(B)}. -/
theorem conjSL2_anticomm (g : Matrix (Fin 2) (Fin 2) ℝ) (hg : IsSL2 g)
    (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    conjSL2 g (anticomm A B) = anticomm (conjSL2 g A) (conjSL2 g B) := by
  dsimp [conjSL2, anticomm]
  have h_prod (X Y : Matrix (Fin 2) (Fin 2) ℝ) :
      (g * X * sl2Inv g) * (g * Y * sl2Inv g) = g * (X * Y) * sl2Inv g := by
    calc
      (g * X * sl2Inv g) * (g * Y * sl2Inv g)
        = g * X * (sl2Inv g * g) * Y * sl2Inv g := by simp only [Matrix.mul_assoc]
      _ = g * X * 1 * Y * sl2Inv g := by rw [sl2Inv_mul g hg]
      _ = g * (X * Y) * sl2Inv g := by simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [h_prod A B, h_prod B A]
  simp only [Matrix.mul_add, Matrix.add_mul]

/-- Conjugation of scalar identity is scalar identity. -/
theorem conjSL2_one (g : Matrix (Fin 2) (Fin 2) ℝ) (hg : IsSL2 g) :
    conjSL2 g 1 = 1 := by
  dsimp [conjSL2]
  rw [Matrix.mul_one, mul_sl2Inv g hg]

/-- The Bogoliubov boost matrix in M₂(ℝ). -/
noncomputable def bogoliubovMatrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh θ, Real.sinh θ;
     Real.sinh θ, Real.cosh θ]

/-- The Bogoliubov matrix has determinant 1, so it belongs to SL(2, ℝ). -/
theorem isSL2_bogoliubovMatrix (θ : ℝ) : IsSL2 (bogoliubovMatrix θ) := by
  dsimp [IsSL2]
  rw [Matrix.det_fin_two (bogoliubovMatrix θ)]
  dsimp [bogoliubovMatrix]
  have h := Real.cosh_sq_sub_sinh_sq θ
  calc Real.cosh θ * Real.cosh θ - Real.sinh θ * Real.sinh θ
    _ = Real.cosh θ ^ 2 - Real.sinh θ ^ 2 := by ring
    _ = 1 := h

/-- Krein metric η = diag(1, -1). -/
def kreinMetric : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0;
     0, -1]

/-- Krein adjoint M^† = η Mᵀ η. -/
def kreinAdjoint (M : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  kreinMetric * Mᵀ * kreinMetric

/-- Bogoliubov boost is a Krein isometry: B(θ)^† B(θ) = 1. -/
theorem bogoliubov_krein_isometry (θ : ℝ) :
    kreinAdjoint (bogoliubovMatrix θ) * bogoliubovMatrix θ = 1 := by
  ext i j
  dsimp [kreinAdjoint, kreinMetric, bogoliubovMatrix]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue,
             Matrix.transpose_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp
  · have h := Real.cosh_sq_sub_sinh_sq θ
    calc Real.cosh θ * Real.cosh θ + -(Real.sinh θ * Real.sinh θ)
      _ = Real.cosh θ ^ 2 - Real.sinh θ ^ 2 := by ring
      _ = 1 := h
  · ring
  · ring
  · have h := Real.cosh_sq_sub_sinh_sq θ
    calc -(Real.sinh θ * Real.sinh θ) + Real.cosh θ * Real.cosh θ
      _ = Real.cosh θ ^ 2 - Real.sinh θ ^ 2 := by ring
      _ = 1 := h

/-- Bogoliubov CAR Preservation Theorem:
    The Bogoliubov transformed fermionic operators preserve the exact CAR anticommutation:
    {Conj_{B(θ)}(rootPlus), Conj_{B(θ)}(rootMinus)} = 1. -/
theorem bogoliubov_preserves_car (θ : ℝ) :
    anticomm (conjSL2 (bogoliubovMatrix θ) rootPlus)
             (conjSL2 (bogoliubovMatrix θ) rootMinus) = 1 := by
  have h_cov := conjSL2_anticomm (bogoliubovMatrix θ) (isSL2_bogoliubovMatrix θ) rootPlus rootMinus
  rw [← h_cov, anticomm_rootPlus_rootMinus, conjSL2_one (bogoliubovMatrix θ) (isSL2_bogoliubovMatrix θ)]

end InfoGeometry.Cosmology.GNSQuotientCoset
