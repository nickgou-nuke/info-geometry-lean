/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.JaynesianTomitaBisognanoColimit
import InfoGeometry.Canonical.DiracSouriauOperator
import InfoGeometry.Canonical.ModularMonodromyClock
import InfoGeometry.Canonical.ThermalTimeMonodromyBridge
import InfoGeometry.Physics.ParabolicClock

/-!
# Jaynesian Inductive Colimit Closure for D7, D8, and D16

Under the repository's colimit-continuum law, the only admissible infinite limit
is the **Jaynesian inductive colimit** (`RealBlockColimit m`), with no postulated
non-inductive continuum or Cauchy completion.  This module constructively lifts:

1. **D7 (`RealBlockColimit 4`)**: `colimitDiracSouriau`, stage compatibility
   across `realBlockInductiveSystem 4`, `colimit_diracSouriau_decoupled_drazin`,
   `colimit_diracSouriau_drazin_exists`, and `colimitDiracSouriau_noncomm`.
2. **D8 (`RealBlockColimit m`)**: concrete quadratic Souriau potentials
   `jaynesianMassieu`, `jaynesianPartition`, `jaynesianEntropy`, true directional
   derivatives (`HasDerivAt`) for first/second variations, Fenchel–Young contact
   and uniqueness (`jaynesian_fenchel_young_eq_zero_iff`), skew-adjoint
   coadjoint Casimir conservation (`colimit_coadjoint_casimir_orthogonal`), and
   the end-to-end strict coadjoint Hessian-metriplectic theorem
   `jaynesianSouriau_coadjoint_strict_hessian_metriplectic`.
3. **D16 (`RealBlockColimit 2`)**: the nilpotent parabolic clock generator
   `colimitParabolicK` (`OnForbiddenCone`, `K ^ n = 0` for `n ≥ 2`), odd
   `ℤ/2`-graded inner differential (`∂_K² = 0`), unipotent group
   `colimitParabolicFlow`, faithful integer-winding homomorphism via
   `ThermalTimeWindingCalibration`, and exact quadratic `Ad`-truncation
   `colimitParabolicAdFlow_quadratic_expansion`.
-/

noncomputable section

namespace InfoGeometry.Canonical.JaynesianSouriauParabolicColimit

open Matrix
open InfoGeometry.Canonical.FiniteMatrixTomitaPolar
open InfoGeometry.Canonical.JaynesianTomitaBisognanoColimit
open InfoGeometry.Canonical.DiracSouriau
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.ModularMonodromyClock
open InfoGeometry.Canonical.ThermalTimeMonodromyBridge
open InfoGeometry.Algebra.GradedNullconeAlgebra

section ScalarRingHelpers

private lemma mul_smul_comm_block {m : ℕ} (c : ℝ) (x y : RealBlockColimit m) :
    x * (c • y) = c • (x * y) := by
  rcases toBlockColimit_lift_two x y with ⟨k, X, Y, rfl, rfl⟩
  rw [smul_toBlockColimit, mul_toBlockColimit, mul_toBlockColimit, smul_toBlockColimit,
      Matrix.mul_smul]

private lemma smul_mul_assoc_block {m : ℕ} (c : ℝ) (x y : RealBlockColimit m) :
    (c • x) * y = c • (x * y) := by
  rcases toBlockColimit_lift_two x y with ⟨k, X, Y, rfl, rfl⟩
  rw [smul_toBlockColimit, mul_toBlockColimit, mul_toBlockColimit, smul_toBlockColimit,
      Matrix.smul_mul]

/-- Canonical `RingHom` from stage `k` into the Jaynesian colimit `RealBlockColimit m`. -/
def toBlockColimitRingHom {m : ℕ} (k : ℕ) : RealBlockStage m k →+* RealBlockColimit m where
  toFun := toBlockColimit k
  map_one' := toBlockColimit_one k
  map_mul' X Y := (mul_toBlockColimit k X Y).symm
  map_zero' := toBlockColimit_zero k
  map_add' X Y := (add_toBlockColimit k X Y).symm

end ScalarRingHelpers

/-!
## 1. D7: Dirac–Souriau Sector & Decoupled Drazin Inverse in `RealBlockColimit 4`
-/

/-- Canonical index equivalence `Fin 2 ⊕ Fin 2 ≃ Fin 4`. -/
def fin2SumEquivFin4 : Fin 2 ⊕ Fin 2 ≃ Fin 4 :=
  finSumFinEquiv

/-- Embed a `4 × 4` Dirac–Souriau sector into stage `0` of `RealBlockStage 4`. -/
def diracSouriauStage0 (S : DiracSouriauSector ℝ) : RealBlockStage 4 0 :=
  Matrix.reindexAlgEquiv ℝ ℝ fin2SumEquivFin4 S.toMatrix

/-- Lift a `4 × 4` Dirac–Souriau sector into the Jaynesian colimit `RealBlockColimit 4`. -/
def colimitDiracSouriau (S : DiracSouriauSector ℝ) : RealBlockColimit 4 :=
  toBlockColimit 0 (diracSouriauStage0 S)

/-- Ring homomorphisms preserve `IsDrazinInverse`. -/
theorem isDrazinInverse_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    {a d : R} {k : ℕ} (h : IsDrazinInverse a d k) :
    IsDrazinInverse (f a) (f d) k := by
  refine IsDrazinInverse.mk ?_ ?_ ?_
  · rw [← map_mul, h.comm, map_mul]
  · rw [← map_mul, ← map_mul, h.idempotent]
  · rw [← map_pow, ← map_mul, h.power, map_pow]

/-- Inductive stage compatibility of `diracSouriauStage0` across `realBlockInductiveSystem 4`. -/
theorem colimitDiracSouriau_stage_compat (S : DiracSouriauSector ℝ) (k : ℕ) :
    toBlockColimit k ((realBlockInductiveSystem 4).trans (Nat.zero_le k) (diracSouriauStage0 S)) =
      colimitDiracSouriau S :=
  (realBlockStarAlgebraCocone 4).eval_comm (Nat.zero_le k) (diracSouriauStage0 S)

/-- Constructive index-2 Drazin inverse in `RealBlockColimit 4` for a decoupled
Dirac–Souriau sector (`A₁` invertible, `A₂^2 = 0`, `B = 0`). -/
theorem colimit_diracSouriau_decoupled_drazin
    (A₁ A₂ : Matrix (Fin 2) (Fin 2) ℝ) (hA₁ : IsUnit A₁.det) (hA₂ : A₂ ^ 2 = 0) :
    ∃ D : RealBlockColimit 4, IsDrazinInverse (colimitDiracSouriau ⟨A₁, A₂, 0⟩) D 2 := by
  rcases block_drazin_inverse_decoupled A₁ hA₁ A₂ hA₂ with ⟨D₀, hD₀⟩
  let φ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ →+* RealBlockColimit 4 :=
    (toBlockColimitRingHom 0).comp (Matrix.reindexAlgEquiv ℝ ℝ fin2SumEquivFin4).toRingHom
  refine ⟨φ D₀, ?_⟩
  have hM :
      (⟨A₁, A₂, 0⟩ : DiracSouriauSector ℝ).toMatrix =
        fromBlocks A₁ (0 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ) A₂ := by
    simp [DiracSouriauSector.toMatrix, DiracSouriauSector.C]
  have hcol :
      φ (fromBlocks A₁ (0 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ) A₂) =
        colimitDiracSouriau ⟨A₁, A₂, 0⟩ := by
    change toBlockColimit 0
        (Matrix.reindexAlgEquiv ℝ ℝ fin2SumEquivFin4
          (fromBlocks A₁ 0 0 A₂)) =
      toBlockColimit 0
        (Matrix.reindexAlgEquiv ℝ ℝ fin2SumEquivFin4
          (⟨A₁, A₂, 0⟩ : DiracSouriauSector ℝ).toMatrix)
    rw [hM]
  rw [← hcol]
  exact isDrazinInverse_map φ hD₀

/-- Constructive Drazin-inverse existence for every `DiracSouriauSector ℝ`
inside the Jaynesian colimit `RealBlockColimit 4`. -/
theorem colimit_diracSouriau_drazin_exists (S : DiracSouriauSector ℝ) :
    ∃ (k : ℕ) (D : RealBlockColimit 4), IsDrazinInverse (colimitDiracSouriau S) D k := by
  rcases S.exists_drazinInverse with ⟨k, D₀, hD₀⟩
  let φ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ →+* RealBlockColimit 4 :=
    (toBlockColimitRingHom 0).comp (Matrix.reindexAlgEquiv ℝ ℝ fin2SumEquivFin4).toRingHom
  exact ⟨k, φ D₀, isDrazinInverse_map φ hD₀⟩

/-- Non-commutativity witness of `colimitDiracSouriau` inside `RealBlockColimit 4`. -/
theorem colimitDiracSouriau_noncomm :
    ∃ S₁ S₂ : DiracSouriauSector ℝ,
      colimitDiracSouriau S₁ * colimitDiracSouriau S₂ ≠
        colimitDiracSouriau S₂ * colimitDiracSouriau S₁ := by
  rcases mat2_mul_noncommutative_witness with ⟨A, B, hAB⟩
  refine ⟨⟨A, 0, 0⟩, ⟨B, 0, 0⟩, ?_⟩
  intro h
  unfold colimitDiracSouriau diracSouriauStage0 at h
  rw [mul_toBlockColimit, mul_toBlockColimit] at h
  have h1 := toBlockColimit_injective 0 h
  rw [← map_mul, ← map_mul] at h1
  have h2 := (Matrix.reindexAlgEquiv ℝ ℝ fin2SumEquivFin4).injective h1
  apply hAB
  ext i j
  have hij := congr_fun (congr_fun h2 (Sum.inl i)) (Sum.inl j)
  simpa [DiracSouriauSector.toMatrix, DiracSouriauSector.C, Matrix.fromBlocks_multiply] using hij

/-!
## 2. D8: Jaynesian Coadjoint-Orbit Souriau Hessian & Casimir-Metriplectic Closure
-/

section JaynesianSouriau

lemma colimitHSInner_add_left {m : ℕ} (x y z : RealBlockColimit m) :
    colimitHSInner (x + y) z = colimitHSInner x z + colimitHSInner y z := by
  rw [colimitHSInner_symm, colimitHSInner_add_right, colimitHSInner_symm z x,
      colimitHSInner_symm z y]

lemma colimitHSInner_smul_left {m : ℕ} (c : ℝ) (x y : RealBlockColimit m) :
    colimitHSInner (c • x) y = c * colimitHSInner x y := by
  rw [colimitHSInner_symm, colimitHSInner_smul_right, colimitHSInner_symm]

lemma colimitHSInner_neg_right {m : ℕ} (x y : RealBlockColimit m) :
    colimitHSInner x (-y) = -colimitHSInner x y := by
  rw [show -y = (-1 : ℝ) • y from (neg_one_smul ℝ y).symm, colimitHSInner_smul_right]
  ring

lemma colimitHSInner_sub_right {m : ℕ} (x y z : RealBlockColimit m) :
    colimitHSInner x (y - z) = colimitHSInner x y - colimitHSInner x z := by
  rw [sub_eq_add_neg, colimitHSInner_add_right, colimitHSInner_neg_right, sub_eq_add_neg]

lemma colimitHSInner_sub_left {m : ℕ} (x y z : RealBlockColimit m) :
    colimitHSInner (x - y) z = colimitHSInner x z - colimitHSInner y z := by
  rw [colimitHSInner_symm, colimitHSInner_sub_right, colimitHSInner_symm z x,
      colimitHSInner_symm z y]

/-- Strict positivity of `colimitHSInner` on nonzero elements of `RealBlockColimit m`. -/
theorem colimitHSInner_self_pos_of_ne_zero {m : ℕ} {x : RealBlockColimit m} (hx : x ≠ 0) :
    0 < colimitHSInner x x := by
  apply lt_of_le_of_ne (colimitHSInner_self_nonneg x)
  intro hzero
  exact hx ((colimitHSInner_self_eq_zero_iff x).mp hzero.symm)

/-- Quadratic Souriau Massieu potential `(1 / 2) ⟨β, β⟩` on `RealBlockColimit m`. -/
def jaynesianMassieu {m : ℕ} (β : RealBlockColimit m) : ℝ :=
  (1 / 2 : ℝ) * colimitHSInner β β

/-- Partition functional `Z(β) = exp(jaynesianMassieu β)` on `RealBlockColimit m`. -/
def jaynesianPartition {m : ℕ} (β : RealBlockColimit m) : ℝ :=
  Real.exp (jaynesianMassieu β)

/-- Legendre-dual Souriau entropy `-(1 / 2) ⟨Q, Q⟩` on `RealBlockColimit m`. -/
def jaynesianEntropy {m : ℕ} (Q : RealBlockColimit m) : ℝ :=
  -(1 / 2 : ℝ) * colimitHSInner Q Q

/-- Exact quadratic directional expansion of `jaynesianMassieu` along `β + t • X`. -/
theorem jaynesianMassieu_expand {m : ℕ} (β X : RealBlockColimit m) (t : ℝ) :
    jaynesianMassieu (β + t • X) =
      jaynesianMassieu β + t * colimitHSInner β X +
        (1 / 2 : ℝ) * colimitHSInner X X * t ^ 2 := by
  unfold jaynesianMassieu
  rw [colimitHSInner_add_left, colimitHSInner_add_right, colimitHSInner_add_right,
      colimitHSInner_smul_left, colimitHSInner_smul_right, colimitHSInner_smul_right,
      colimitHSInner_smul_left, colimitHSInner_symm X β]
  ring

/-- Analytic directional derivative (`HasDerivAt`) of `jaynesianMassieu`: first variation is
the thermodynamic moment pairing `⟨β, X⟩`. -/
theorem hasDerivAt_jaynesianMassieu {m : ℕ} (β X : RealBlockColimit m) :
    HasDerivAt (fun t : ℝ => jaynesianMassieu (β + t • X)) (colimitHSInner β X) 0 := by
  have hfn :
      (fun t : ℝ => jaynesianMassieu (β + t • X)) =
        (fun t : ℝ =>
          jaynesianMassieu β + t * colimitHSInner β X +
            (1 / 2 : ℝ) * colimitHSInner X X * t ^ 2) :=
    funext (jaynesianMassieu_expand β X)
  rw [hfn]
  have hd :
      HasDerivAt
        (fun t : ℝ =>
          jaynesianMassieu β + t * colimitHSInner β X +
            (1 / 2 : ℝ) * colimitHSInner X X * t ^ 2)
        (0 + 1 * colimitHSInner β X + ((1 / 2 : ℝ) * colimitHSInner X X) * (2 * (0 : ℝ) ^ 1)) 0 :=
    ((hasDerivAt_const 0 (jaynesianMassieu β)).add
      ((hasDerivAt_id 0).mul_const (colimitHSInner β X))).add
      (((hasDerivAt_pow 2 0).const_mul ((1 / 2 : ℝ) * colimitHSInner X X)))
  simpa using hd

/-- Analytic second-variation derivative (`HasDerivAt`) of the Massieu gradient gives the
Fisher bilinear form `⟨X, Y⟩` on `RealBlockColimit m`. -/
theorem hasDerivAt_jaynesianGradient {m : ℕ} (β X Y : RealBlockColimit m) :
    HasDerivAt (fun t : ℝ => colimitHSInner (β + t • X) Y) (colimitHSInner X Y) 0 := by
  have hfn :
      (fun t : ℝ => colimitHSInner (β + t • X) Y) =
        (fun t : ℝ => colimitHSInner β Y + t * colimitHSInner X Y) := by
    ext t
    rw [colimitHSInner_add_left, colimitHSInner_smul_left]
  rw [hfn]
  have hd := ((hasDerivAt_id (0 : ℝ)).mul_const (colimitHSInner X Y)).const_add
    (colimitHSInner β Y)
  simpa using hd

/-- Exact Fenchel–Young divergence formula on `RealBlockColimit m`. -/
theorem jaynesian_fenchel_young_gap {m : ℕ} (β Q : RealBlockColimit m) :
    jaynesianMassieu β - jaynesianEntropy Q - colimitHSInner β Q =
      (1 / 2 : ℝ) * colimitHSInner (β - Q) (β - Q) := by
  unfold jaynesianMassieu jaynesianEntropy
  rw [colimitHSInner_sub_left, colimitHSInner_sub_right, colimitHSInner_sub_right,
      colimitHSInner_symm Q β]
  ring

theorem jaynesian_fenchel_young_nonneg {m : ℕ} (β Q : RealBlockColimit m) :
    0 ≤ jaynesianMassieu β - jaynesianEntropy Q - colimitHSInner β Q := by
  rw [jaynesian_fenchel_young_gap]
  exact mul_nonneg (by norm_num) (colimitHSInner_self_nonneg _)

/-- Exact Fenchel–Young Legendre-duality characterization: equality holds iff `β = Q`. -/
theorem jaynesian_fenchel_young_eq_zero_iff {m : ℕ} (β Q : RealBlockColimit m) :
    jaynesianMassieu β - jaynesianEntropy Q - colimitHSInner β Q = 0 ↔ β = Q := by
  rw [jaynesian_fenchel_young_gap, mul_eq_zero]
  simp only [one_div, inv_eq_zero, OfNat.ofNat_ne_zero, false_or,
    colimitHSInner_self_eq_zero_iff, sub_eq_zero]

/-- Skew-adjoint matrix generators produce zero Hilbert–Schmidt radial rate along
coadjoint brackets `[B, X] = B X - X B`. -/
theorem hsInner_skew_commutator_eq_zero {p : ℕ} (B X : Matrix (Fin p) (Fin p) ℝ)
    (hB : Bᵀ = -B) :
    hsInner X (B * X - X * B) = 0 := by
  have h1 : (Xᵀ * (B * X)).trace = 0 := by
    have hneg : (Xᵀ * (B * X)).trace = -(Xᵀ * (B * X)).trace := by
      calc
        (Xᵀ * (B * X)).trace
            = ((Xᵀ * (B * X))ᵀ).trace := (Matrix.trace_transpose _).symm
        _ = (Xᵀ * (Bᵀ * X)).trace := by
            rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
                Matrix.mul_assoc]
        _ = -(Xᵀ * (B * X)).trace := by
            rw [hB, Matrix.neg_mul, Matrix.mul_neg, Matrix.trace_neg]
    linarith
  have h2 : (Xᵀ * (X * B)).trace = 0 := by
    have hneg : (Xᵀ * (X * B)).trace = -(Xᵀ * (X * B)).trace := by
      calc
        (Xᵀ * (X * B)).trace
            = ((Xᵀ * (X * B))ᵀ).trace := (Matrix.trace_transpose _).symm
        _ = (Bᵀ * (Xᵀ * X)).trace := by
            rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
                Matrix.mul_assoc]
        _ = ((Xᵀ * X) * Bᵀ).trace := Matrix.trace_mul_comm _ _
        _ = -(Xᵀ * (X * B)).trace := by
            rw [hB, Matrix.mul_neg, Matrix.trace_neg, Matrix.mul_assoc]
    linarith
  unfold hsInner
  rw [Matrix.mul_sub, Matrix.trace_sub, h1, h2, sub_zero]

/-- Coadjoint Casimir conservation in the Jaynesian colimit: for any skew-adjoint generator
`β₀* = -β₀`, the coadjoint bracket `[β₀, x]` is strictly `colimitHSInner`-orthogonal to `x`. -/
theorem colimit_coadjoint_casimir_orthogonal {m : ℕ} (β₀ x : RealBlockColimit m)
    (hβ : star β₀ = -β₀) :
    colimitHSInner x (β₀ * x - x * β₀) = 0 := by
  rcases toBlockColimit_lift_two β₀ x with ⟨k, B, X, rfl, rfl⟩
  have hB : Bᵀ = -B := by
    rw [star_toBlockColimit_transpose, neg_toBlockColimit] at hβ
    exact toBlockColimit_injective k hβ
  have hsub :
      toBlockColimit k B * toBlockColimit k X - toBlockColimit k X * toBlockColimit k B =
        toBlockColimit k (B * X - X * B) := by
    rw [mul_toBlockColimit, mul_toBlockColimit, sub_eq_add_neg, neg_toBlockColimit,
        add_toBlockColimit, ← sub_eq_add_neg]
  rw [hsub, colimitHSInner_toBlockColimit]
  unfold normHSInner
  rw [hsInner_skew_commutator_eq_zero B X hB, mul_zero]

/-- Analytic entropy conservation along infinitesimal coadjoint motion generated by `β₀`. -/
theorem hasDerivAt_jaynesianEntropy_coadjoint_zero {m : ℕ} (β₀ x : RealBlockColimit m)
    (hβ : star β₀ = -β₀) :
    HasDerivAt (fun t : ℝ => jaynesianEntropy (x + t • (β₀ * x - x * β₀))) 0 0 := by
  have hfn :
      (fun t : ℝ => jaynesianEntropy (x + t • (β₀ * x - x * β₀))) =
        (fun t : ℝ => -(jaynesianMassieu (x + t • (β₀ * x - x * β₀)))) := by
    ext t
    unfold jaynesianEntropy jaynesianMassieu
    ring
  rw [hfn]
  have hd := (hasDerivAt_jaynesianMassieu x (β₀ * x - x * β₀)).neg
  rw [colimit_coadjoint_casimir_orthogonal β₀ x hβ, neg_zero] at hd
  exact hd

/-- Constructive end-to-end coadjoint-orbit Souriau strict Hessian, Fenchel–Young contact,
Fisher positivity, Casimir conservation, and metriplectic entropy theorem directly on the
Jaynesian inductive colimit `RealBlockColimit m` (zero postulated non-inductive continuum
or context-packet assumptions). -/
theorem jaynesianSouriau_coadjoint_strict_hessian_metriplectic (m : ℕ)
    (β β₀ Q X Y x : RealBlockColimit m) (hX : X ≠ 0) (hβ : star β₀ = -β₀) :
    jaynesianMassieu β = Real.log (jaynesianPartition β)
      ∧ HasDerivAt (fun t : ℝ => jaynesianMassieu (β + t • X)) (colimitHSInner β X) 0
      ∧ HasDerivAt (fun t : ℝ => colimitHSInner (β + t • X) Y) (colimitHSInner X Y) 0
      ∧ colimitHSInner X Y = colimitHSInner Y X
      ∧ 0 ≤ colimitHSInner X X
      ∧ 0 < colimitHSInner X X
      ∧ (jaynesianMassieu β - jaynesianEntropy Q - colimitHSInner β Q = 0 ↔ β = Q)
      ∧ colimitHSInner x (β₀ * x - x * β₀) = 0
      ∧ HasDerivAt (fun t : ℝ => jaynesianEntropy (x + t • (β₀ * x - x * β₀))) 0 0
      ∧ 0 ≤ colimitHSInner x x :=
  ⟨(Real.log_exp (jaynesianMassieu β)).symm,
    hasDerivAt_jaynesianMassieu β X,
    hasDerivAt_jaynesianGradient β X Y,
    colimitHSInner_symm X Y,
    colimitHSInner_self_nonneg X,
    colimitHSInner_self_pos_of_ne_zero hX,
    jaynesian_fenchel_young_eq_zero_iff β Q,
    colimit_coadjoint_casimir_orthogonal β₀ x hβ,
    hasDerivAt_jaynesianEntropy_coadjoint_zero β₀ x hβ,
    colimitHSInner_self_nonneg x⟩

end JaynesianSouriau

/-!
## 3. D16: Parabolic Time Clock & Graded Nullcone Soldering in `RealBlockColimit 2`
-/

section JaynesianParabolicClock

/-- Canonical square-zero parabolic clock generator `K = !![0, 1; 0, 0]` in `RealBlockColimit 2`. -/
def colimitParabolicK : RealBlockColimit 2 :=
  toBlockColimit 0 (InfoGeometry.Physics.K (R := ℝ))

/-- Canonical `ℤ/2`-grading involution `Γ = diag(1, -1)` in `RealBlockColimit 2`. -/
def colimitParabolicGamma : RealBlockColimit 2 :=
  toBlockColimit 0 !![1, 0; 0, -1]

/-- One-parameter unipotent parabolic flow `exp(t K) = 1 + t • K` in `RealBlockColimit 2`. -/
def colimitParabolicFlow (t : ℝ) : RealBlockColimit 2 :=
  1 + t • colimitParabolicK

/-- Conjugation action `Ad(exp(t K))(x) = (1 + tK) x (1 - tK)` in `RealBlockColimit 2`. -/
def colimitParabolicAdFlow (t : ℝ) (x : RealBlockColimit 2) : RealBlockColimit 2 :=
  colimitParabolicFlow t * x * colimitParabolicFlow (-t)

theorem colimitParabolicK_onForbiddenCone :
    OnForbiddenCone (RealBlockColimit 2) colimitParabolicK := by
  unfold OnForbiddenCone colimitParabolicK
  rw [mul_toBlockColimit, InfoGeometry.Physics.K_sq_eq_zero, toBlockColimit_zero]

theorem colimitParabolicK_pow_zero (n : ℕ) (hn : n ≥ 2) :
    colimitParabolicK ^ n = 0 :=
  modularFlow_nilpotent_generator (RealBlockColimit 2) colimitParabolicK
    colimitParabolicK_onForbiddenCone n hn

theorem colimitParabolicK_ne_zero : colimitParabolicK ≠ 0 := by
  intro h
  have hmat : InfoGeometry.Physics.K (R := ℝ) = 0 :=
    toBlockColimit_injective 0 (h.trans (toBlockColimit_zero 0).symm)
  have h01 := congr_fun (congr_fun hmat 0) 1
  norm_num [InfoGeometry.Physics.K] at h01

theorem colimitParabolicGamma_sq :
    colimitParabolicGamma * colimitParabolicGamma = 1 := by
  unfold colimitParabolicGamma
  rw [mul_toBlockColimit]
  have hsq : (!![(1 : ℝ), 0; 0, -1]) * !![(1 : ℝ), 0; 0, -1] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hsq, toBlockColimit_one]

theorem colimitParabolicK_odd :
    parityConj colimitParabolicGamma colimitParabolicK = -colimitParabolicK := by
  rw [parityConj_apply]
  unfold colimitParabolicGamma colimitParabolicK
  rw [mul_toBlockColimit, mul_toBlockColimit, neg_toBlockColimit]
  have hodd :
      (!![(1 : ℝ), 0; 0, -1]) * InfoGeometry.Physics.K * !![(1 : ℝ), 0; 0, -1] =
        -(InfoGeometry.Physics.K (R := ℝ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [InfoGeometry.Physics.K, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hodd]

/-- OpenGauss T16 non-commutativity witness `[K, Γ] ≠ 0` in `RealBlockColimit 2`. -/
theorem colimitParabolicK_gamma_noncomm :
    colimitParabolicK * colimitParabolicGamma ≠ colimitParabolicGamma * colimitParabolicK := by
  intro h
  unfold colimitParabolicK colimitParabolicGamma at h
  rw [mul_toBlockColimit, mul_toBlockColimit] at h
  have hmat := toBlockColimit_injective 0 h
  have h01 := congr_fun (congr_fun hmat 0) 1
  norm_num [InfoGeometry.Physics.K, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Graded inner differential `∂_K` squares to zero across all of `RealBlockColimit 2`. -/
theorem colimitParabolic_gradedInnerDiff_sq_zero (x : RealBlockColimit 2) :
    gradedInnerDiff colimitParabolicGamma colimitParabolicK
      (gradedInnerDiff colimitParabolicGamma colimitParabolicK x) = 0 :=
  (unilateral_onForbiddenCone_gradedInnerDiff_parabolic (A := RealBlockColimit 2)
    colimitParabolicGamma_sq colimitParabolicK_odd colimitParabolicK_onForbiddenCone x).1

theorem colimitParabolicK_sq : colimitParabolicK * colimitParabolicK = 0 :=
  colimitParabolicK_onForbiddenCone

@[simp]
theorem colimitParabolicFlow_zero : colimitParabolicFlow 0 = 1 := by
  unfold colimitParabolicFlow
  rw [zero_smul, add_zero]

theorem colimitParabolicFlow_add (s t : ℝ) :
    colimitParabolicFlow (s + t) = colimitParabolicFlow s * colimitParabolicFlow t := by
  unfold colimitParabolicFlow
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc_block, mul_smul_comm_block,
    colimitParabolicK_sq, smul_zero, add_zero, add_smul, add_assoc]

theorem colimitParabolicFlow_inv (t : ℝ) :
    colimitParabolicFlow t * colimitParabolicFlow (-t) = 1 := by
  rw [← colimitParabolicFlow_add, add_neg_cancel, colimitParabolicFlow_zero]

theorem colimitParabolicFlow_sub_one_sq (t : ℝ) :
    (colimitParabolicFlow t - 1) * (colimitParabolicFlow t - 1) = 0 := by
  have hsub : colimitParabolicFlow t - 1 = t • colimitParabolicK := by
    unfold colimitParabolicFlow
    rw [add_sub_cancel_left]
  rw [hsub, smul_mul_assoc_block, mul_smul_comm_block,
      colimitParabolicK_onForbiddenCone, smul_zero, smul_zero]

theorem colimitParabolicFlow_injective : Function.Injective colimitParabolicFlow := by
  intro s t h
  unfold colimitParabolicFlow at h
  have hs : s • colimitParabolicK = t • colimitParabolicK := add_left_cancel h
  unfold colimitParabolicK at hs
  rw [← toBlockColimit_one 0, smul_toBlockColimit, smul_toBlockColimit] at *
  have hmat := toBlockColimit_injective 0 hs
  have h01 := congr_fun (congr_fun hmat 0) 1
  simpa [InfoGeometry.Physics.K] using h01

/-- Integer winding labels embed additively into the unipotent parabolic flow in `RealBlockColimit 2`. -/
theorem colimitParabolicFlow_timeOfWinding_add (C : ThermalTimeWindingCalibration) (m n : ℤ) :
    colimitParabolicFlow (C.timeOfWinding (m + n)) =
      colimitParabolicFlow (C.timeOfWinding m) * colimitParabolicFlow (C.timeOfWinding n) := by
  rw [timeOfWinding_add, colimitParabolicFlow_add]

theorem colimitParabolicFlow_timeOfWinding_injective (C : ThermalTimeWindingCalibration) :
    Function.Injective (fun n : ℤ => colimitParabolicFlow (C.timeOfWinding n)) :=
  colimitParabolicFlow_injective.comp (timeOfWinding_injective C)

@[simp]
theorem colimitParabolicAdFlow_zero (x : RealBlockColimit 2) :
    colimitParabolicAdFlow 0 x = x := by
  unfold colimitParabolicAdFlow
  rw [neg_zero, colimitParabolicFlow_zero, one_mul, mul_one]

theorem colimitParabolicAdFlow_add (s t : ℝ) (x : RealBlockColimit 2) :
    colimitParabolicAdFlow (s + t) x =
      colimitParabolicAdFlow s (colimitParabolicAdFlow t x) := by
  unfold colimitParabolicAdFlow
  have hneg : -(s + t) = -t + -s := by ring
  rw [colimitParabolicFlow_add s t, hneg, colimitParabolicFlow_add (-t) (-s)]
  simp only [mul_assoc]

theorem colimitParabolicAdFlow_mul (t : ℝ) (x y : RealBlockColimit 2) :
    colimitParabolicAdFlow t (x * y) =
      colimitParabolicAdFlow t x * colimitParabolicAdFlow t y := by
  have hinv : colimitParabolicFlow (-t) * colimitParabolicFlow t = 1 := by
    rw [← colimitParabolicFlow_add, neg_add_cancel, colimitParabolicFlow_zero]
  unfold colimitParabolicAdFlow
  calc
    colimitParabolicFlow t * (x * y) * colimitParabolicFlow (-t)
        = colimitParabolicFlow t * x * 1 * y * colimitParabolicFlow (-t) := by
          simp only [mul_assoc, mul_one]
    _ = colimitParabolicFlow t * x *
          (colimitParabolicFlow (-t) * colimitParabolicFlow t) *
          y * colimitParabolicFlow (-t) := by rw [hinv]
    _ = (colimitParabolicFlow t * x * colimitParabolicFlow (-t)) *
          (colimitParabolicFlow t * y * colimitParabolicFlow (-t)) := by
          simp only [mul_assoc]

/-- Exact quadratic Baker–Campbell–Hausdorff / adjoint truncation in `RealBlockColimit 2`
forced by `colimitParabolicK^2 = 0`. -/
theorem colimitParabolicAdFlow_quadratic_expansion (t : ℝ) (x : RealBlockColimit 2) :
    colimitParabolicAdFlow t x =
      x + t • (colimitParabolicK * x - x * colimitParabolicK) -
        (t * t) • (colimitParabolicK * x * colimitParabolicK) := by
  unfold colimitParabolicAdFlow colimitParabolicFlow
  rw [add_mul, one_mul, smul_mul_assoc_block, add_mul, mul_add, mul_add, mul_one, mul_one,
      mul_smul_comm_block, smul_mul_assoc_block, mul_smul_comm_block, smul_smul, mul_assoc,
      show t * -t = -(t * t) by ring, neg_smul, neg_smul, smul_sub]
  abel

end JaynesianParabolicClock

end InfoGeometry.Canonical.JaynesianSouriauParabolicColimit
