import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic

/-!
# A native split-real null tetrad

The carrier is the native real module `Fin 4 → ℝ`, equipped with the explicit
split `(2,2)` form.  Two real Witt pairs replace the real/complex split of a
Lorentzian Newman--Penrose tetrad.  No scalar complexification and no assumed
geometry packet are used.

An internal real endomorphism `internalJ` squares to `-Id` and exchanges the
two hyperbolic planes.  A separate boost fixes the causal plane and rescales
the entropy Witt pair by `exp (±t)`.  No identification with a Zorn or
split-octonion flow is asserted without an explicit intertwiner.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Clifford.SplitRealNullTetrad

abbrev Carrier := Fin 4 → ℝ

/-- The symmetric split `(2,2)` pairing. -/
def pairing (X Y : Carrier) : ℝ :=
  X 0 * Y 0 - X 1 * Y 1 + X 2 * Y 2 - X 3 * Y 3

/-- The associated split quadratic form. -/
noncomputable def quad : QuadraticForm ℝ Carrier :=
  QuadraticMap.ofPolar
    (fun X => pairing X X)
    (fun r X => by simp [pairing]; ring)
    (fun X Y Z => by simp [pairing, QuadraticMap.polar]; ring)
    (fun r X Y => by
      simp only [QuadraticMap.polar, pairing, Pi.smul_apply, Pi.add_apply,
        smul_eq_mul]
      ring)

@[simp] theorem quad_apply (X : Carrier) : quad X = pairing X X := rfl

/-- The two causal null directions. -/
def causalMinus : Carrier := ![1 / 2, 1 / 2, 0, 0]
def causalPlus : Carrier := ![1 / 2, -(1 / 2), 0, 0]

/-- The two entropy/Weyl null directions. -/
def entropyMinus : Carrier := ![0, 0, 1 / 2, 1 / 2]
def entropyPlus : Carrier := ![0, 0, 1 / 2, -(1 / 2)]

@[simp] theorem causalMinus_apply (i : Fin 4) :
    causalMinus i = ![1 / 2, 1 / 2, 0, 0] i := rfl

@[simp] theorem causalPlus_apply (i : Fin 4) :
    causalPlus i = ![1 / 2, -(1 / 2), 0, 0] i := rfl

@[simp] theorem entropyMinus_apply (i : Fin 4) :
    entropyMinus i = ![0, 0, 1 / 2, 1 / 2] i := rfl

@[simp] theorem entropyPlus_apply (i : Fin 4) :
    entropyPlus i = ![0, 0, 1 / 2, -(1 / 2)] i := rfl

@[simp] theorem causalMinus_zero : causalMinus 0 = 1 / 2 := rfl
@[simp] theorem causalMinus_one : causalMinus 1 = 1 / 2 := rfl
@[simp] theorem causalMinus_two : causalMinus 2 = 0 := rfl
@[simp] theorem causalMinus_three : causalMinus 3 = 0 := rfl
@[simp] theorem causalPlus_zero : causalPlus 0 = 1 / 2 := rfl
@[simp] theorem causalPlus_one : causalPlus 1 = -(1 / 2) := rfl
@[simp] theorem causalPlus_two : causalPlus 2 = 0 := rfl
@[simp] theorem causalPlus_three : causalPlus 3 = 0 := rfl
@[simp] theorem entropyMinus_zero : entropyMinus 0 = 0 := rfl
@[simp] theorem entropyMinus_one : entropyMinus 1 = 0 := rfl
@[simp] theorem entropyMinus_two : entropyMinus 2 = 1 / 2 := rfl
@[simp] theorem entropyMinus_three : entropyMinus 3 = 1 / 2 := rfl
@[simp] theorem entropyPlus_zero : entropyPlus 0 = 0 := rfl
@[simp] theorem entropyPlus_one : entropyPlus 1 = 0 := rfl
@[simp] theorem entropyPlus_two : entropyPlus 2 = 1 / 2 := rfl
@[simp] theorem entropyPlus_three : entropyPlus 3 = -(1 / 2) := rfl

@[simp] theorem causalMinus_isotropic : quad causalMinus = 0 := by
  simp only [quad_apply, pairing, causalMinus_zero, causalMinus_one,
    causalMinus_two, causalMinus_three]
  norm_num

@[simp] theorem causalPlus_isotropic : quad causalPlus = 0 := by
  simp only [quad_apply, pairing, causalPlus_zero, causalPlus_one,
    causalPlus_two, causalPlus_three]
  norm_num

@[simp] theorem entropyMinus_isotropic : quad entropyMinus = 0 := by
  simp only [quad_apply, pairing, entropyMinus_zero, entropyMinus_one,
    entropyMinus_two, entropyMinus_three]
  norm_num

@[simp] theorem entropyPlus_isotropic : quad entropyPlus = 0 := by
  simp only [quad_apply, pairing, entropyPlus_zero, entropyPlus_one,
    entropyPlus_two, entropyPlus_three]
  norm_num

@[simp] theorem causal_pairing : pairing causalMinus causalPlus = 1 / 2 := by
  simp only [pairing, causalMinus_zero, causalMinus_one, causalMinus_two,
    causalMinus_three, causalPlus_zero, causalPlus_one, causalPlus_two,
    causalPlus_three]
  norm_num

@[simp] theorem causal_pairing_swap : pairing causalPlus causalMinus = 1 / 2 := by
  simp only [pairing, causalMinus_zero, causalMinus_one, causalMinus_two,
    causalMinus_three, causalPlus_zero, causalPlus_one, causalPlus_two,
    causalPlus_three]
  norm_num

@[simp] theorem entropy_pairing : pairing entropyMinus entropyPlus = 1 / 2 := by
  simp only [pairing, entropyMinus_zero, entropyMinus_one, entropyMinus_two,
    entropyMinus_three, entropyPlus_zero, entropyPlus_one, entropyPlus_two,
    entropyPlus_three]
  norm_num

@[simp] theorem entropy_pairing_swap : pairing entropyPlus entropyMinus = 1 / 2 := by
  simp only [pairing, entropyMinus_zero, entropyMinus_one, entropyMinus_two,
    entropyMinus_three, entropyPlus_zero, entropyPlus_one, entropyPlus_two,
    entropyPlus_three]
  norm_num

@[simp] theorem causalMinus_entropyMinus_pairing :
    pairing causalMinus entropyMinus = 0 := by
  simp only [pairing, causalMinus_zero, causalMinus_one, causalMinus_two,
    causalMinus_three, entropyMinus_zero, entropyMinus_one, entropyMinus_two,
    entropyMinus_three]
  norm_num

@[simp] theorem causalMinus_entropyPlus_pairing :
    pairing causalMinus entropyPlus = 0 := by
  simp only [pairing, causalMinus_zero, causalMinus_one, causalMinus_two,
    causalMinus_three, entropyPlus_zero, entropyPlus_one, entropyPlus_two,
    entropyPlus_three]
  norm_num

@[simp] theorem causalPlus_entropyMinus_pairing :
    pairing causalPlus entropyMinus = 0 := by
  simp only [pairing, causalPlus_zero, causalPlus_one, causalPlus_two,
    causalPlus_three, entropyMinus_zero, entropyMinus_one, entropyMinus_two,
    entropyMinus_three]
  norm_num

@[simp] theorem causalPlus_entropyPlus_pairing :
    pairing causalPlus entropyPlus = 0 := by
  simp only [pairing, causalPlus_zero, causalPlus_one, causalPlus_two,
    causalPlus_three, entropyPlus_zero, entropyPlus_one, entropyPlus_two,
    entropyPlus_three]
  norm_num

/-! ## The real double-Witt Gram readout -/

def nullTetrad : Fin 4 → Carrier :=
  ![causalMinus, causalPlus, entropyMinus, entropyPlus]

def nullTetradGram : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => pairing (nullTetrad i) (nullTetrad j)

theorem nullTetradGram_eq :
    nullTetradGram =
      !![0, (1 / 2 : ℝ), 0, 0;
         (1 / 2 : ℝ), 0, 0, 0;
         0, 0, 0, (1 / 2 : ℝ);
         0, 0, (1 / 2 : ℝ), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nullTetradGram, nullTetrad, pairing] <;>
    norm_num

theorem nullTetrad_linearIndependent :
    LinearIndependent ℝ nullTetrad := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h0 := congrArg (fun X : Carrier => X 0) hg
  have h1 := congrArg (fun X : Carrier => X 1) hg
  have h2 := congrArg (fun X : Carrier => X 2) hg
  have h3 := congrArg (fun X : Carrier => X 3) hg
  fin_cases i <;>
    simp [nullTetrad, causalMinus, causalPlus, entropyMinus, entropyPlus,
      Fin.sum_univ_four] at h0 h1 h2 h3 ⊢ <;>
    linarith

/-! ## Witt coordinates and metric reconstruction -/

def wittCoordinates (X : Carrier) : Fin 4 → ℝ :=
  ![X 0 + X 1, X 0 - X 1, X 2 + X 3, X 2 - X 3]

theorem tetrad_reconstruction (X : Carrier) :
    X =
      wittCoordinates X 0 • causalMinus +
      wittCoordinates X 1 • causalPlus +
      wittCoordinates X 2 • entropyMinus +
      wittCoordinates X 3 • entropyPlus := by
  funext i
  fin_cases i <;>
    simp [wittCoordinates, causalMinus, causalPlus, entropyMinus, entropyPlus] <;>
    ring

noncomputable def nullTetradBasis :
    Module.Basis (Fin 4) ℝ Carrier :=
  Module.Basis.mk nullTetrad_linearIndependent (by
    intro X _
    rw [tetrad_reconstruction X]
    let S := Submodule.span ℝ (Set.range nullTetrad)
    have h0 : causalMinus ∈ S := by
      exact Submodule.subset_span (Set.mem_range.mpr ⟨0, by rfl⟩)
    have h1 : causalPlus ∈ S := by
      exact Submodule.subset_span (Set.mem_range.mpr ⟨1, by rfl⟩)
    have h2 : entropyMinus ∈ S := by
      exact Submodule.subset_span (Set.mem_range.mpr ⟨2, by rfl⟩)
    have h3 : entropyPlus ∈ S := by
      exact Submodule.subset_span (Set.mem_range.mpr ⟨3, by rfl⟩)
    exact add_mem (add_mem (add_mem (S.smul_mem _ h0) (S.smul_mem _ h1))
      (S.smul_mem _ h2)) (S.smul_mem _ h3))

@[simp] theorem nullTetradBasis_apply (i : Fin 4) :
    nullTetradBasis i = nullTetrad i := by
  exact Module.Basis.mk_apply _ _ _

theorem nullTetradBasis_sum_repr (X : Carrier) :
    ∑ i, (nullTetradBasis.repr X i) • nullTetradBasis i = X := by
  exact nullTetradBasis.sum_repr X

theorem pairing_eq_wittCoordinates (X Y : Carrier) :
    pairing X Y =
      (wittCoordinates X 0 * wittCoordinates Y 1 +
        wittCoordinates X 1 * wittCoordinates Y 0 +
        wittCoordinates X 2 * wittCoordinates Y 3 +
        wittCoordinates X 3 * wittCoordinates Y 2) / 2 := by
  simp [pairing, wittCoordinates]
  ring

theorem quad_eq_wittCoordinates (X : Carrier) :
    quad X =
      wittCoordinates X 0 * wittCoordinates X 1 +
      wittCoordinates X 2 * wittCoordinates X 3 := by
  rw [quad_apply, pairing_eq_wittCoordinates]
  ring

/-! ## Internal real complex structure -/

/-- `J(x₀,x₁,x₂,x₃)=(-x₂,-x₃,x₀,x₁)`. -/
def internalJ : Carrier →ₗ[ℝ] Carrier where
  toFun X := ![-X 2, -X 3, X 0, X 1]
  map_add' X Y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' r X := by funext i; fin_cases i <;> simp

@[simp] theorem internalJ_apply (X : Carrier) :
    internalJ X = ![-X 2, -X 3, X 0, X 1] := rfl

@[simp] theorem internalJ_sq (X : Carrier) : internalJ (internalJ X) = -X := by
  funext i
  fin_cases i <;> simp [internalJ]

theorem internalJ_sq_endomorphism :
    internalJ.comp internalJ = -(LinearMap.id : Carrier →ₗ[ℝ] Carrier) := by
  apply LinearMap.ext
  intro X
  exact internalJ_sq X

theorem internalJ_pairing (X Y : Carrier) :
    pairing (internalJ X) (internalJ Y) = pairing X Y := by
  simp [pairing, internalJ]
  ring

theorem internalJ_pairing_skew (X Y : Carrier) :
    pairing (internalJ X) Y = -pairing X (internalJ Y) := by
  simp [pairing, internalJ]
  ring

@[simp] theorem internalJ_causalMinus : internalJ causalMinus = entropyMinus := by
  funext i
  fin_cases i <;> simp [internalJ]

@[simp] theorem internalJ_causalPlus : internalJ causalPlus = entropyPlus := by
  funext i
  fin_cases i <;> simp [internalJ]

@[simp] theorem internalJ_entropyMinus : internalJ entropyMinus = -causalMinus := by
  funext i
  fin_cases i <;> simp [internalJ]

@[simp] theorem internalJ_entropyPlus : internalJ entropyPlus = -causalPlus := by
  funext i
  fin_cases i <;> simp [internalJ]

/-! ## Entropy-plane boost -/

/-- A boost of the second hyperbolic plane, fixing the first plane. -/
def entropyBoost (t : ℝ) : Carrier →ₗ[ℝ] Carrier where
  toFun X := ![X 0, X 1,
    Real.cosh t * X 2 + Real.sinh t * X 3,
    Real.sinh t * X 2 + Real.cosh t * X 3]
  map_add' X Y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' r X := by funext i; fin_cases i <;> simp [smul_eq_mul] <;> ring

@[simp] theorem entropyBoost_causalMinus (t : ℝ) :
    entropyBoost t causalMinus = causalMinus := by
  funext i; fin_cases i <;> simp [entropyBoost, causalMinus]

@[simp] theorem entropyBoost_causalPlus (t : ℝ) :
    entropyBoost t causalPlus = causalPlus := by
  funext i; fin_cases i <;> simp [entropyBoost, causalPlus]

@[simp] theorem entropyBoost_entropyMinus (t : ℝ) :
    entropyBoost t entropyMinus = Real.exp t • entropyMinus := by
  have h := Real.cosh_add_sinh t
  funext i
  fin_cases i <;> simp [entropyBoost, entropyMinus] <;> linarith

@[simp] theorem entropyBoost_entropyPlus (t : ℝ) :
    entropyBoost t entropyPlus = Real.exp (-t) • entropyPlus := by
  have h := Real.cosh_sub_sinh t
  funext i
  fin_cases i <;> simp [entropyBoost, entropyPlus] <;> linarith

theorem entropyBoost_add (s t : ℝ) (X : Carrier) :
    entropyBoost (s + t) X = entropyBoost s (entropyBoost t X) := by
  funext i
  fin_cases i <;>
    simp [entropyBoost, Real.cosh_add, Real.sinh_add] <;> ring

@[simp] theorem entropyBoost_zero (X : Carrier) : entropyBoost 0 X = X := by
  funext i
  fin_cases i <;> simp [entropyBoost]

theorem entropyBoost_neg_apply (t : ℝ) (X : Carrier) :
    entropyBoost (-t) (entropyBoost t X) = X := by
  rw [← entropyBoost_add]
  simp

theorem entropyBoost_apply_neg (t : ℝ) (X : Carrier) :
    entropyBoost t (entropyBoost (-t) X) = X := by
  rw [← entropyBoost_add]
  simp

def entropyBoostEquiv (t : ℝ) : Carrier ≃ₗ[ℝ] Carrier where
  toLinearMap := entropyBoost t
  invFun := entropyBoost (-t)
  left_inv := entropyBoost_neg_apply t
  right_inv := entropyBoost_apply_neg t

theorem entropyBoost_pairing (t : ℝ) (X Y : Carrier) :
    pairing (entropyBoost t X) (entropyBoost t Y) = pairing X Y := by
  have h := Real.cosh_sq_sub_sinh_sq t
  simp [pairing, entropyBoost]
  linear_combination (X 2 * Y 2 - X 3 * Y 3) * h

theorem entropyBoost_quad (t : ℝ) (X : Carrier) :
    quad (entropyBoost t X) = quad X := by
  simp only [quad_apply]
  exact entropyBoost_pairing t X X

theorem entropyBoost_quad_eq_zero_iff (t : ℝ) (X : Carrier) :
    quad (entropyBoost t X) = 0 ↔ quad X = 0 := by
  rw [entropyBoost_quad]

/-! ## Projectivized null rays -/

abbrev ProjectiveCarrier := ℙ ℝ Carrier

def entropyBoostProjective (t : ℝ) : ProjectiveCarrier → ProjectiveCarrier :=
  Projectivization.map (entropyBoostEquiv t).toLinearMap
    (entropyBoostEquiv t).injective

/-- The projective boost is an equivalence; reversing rapidity is its inverse. -/
def entropyBoostProjectiveEquiv (t : ℝ) :
    ProjectiveCarrier ≃ ProjectiveCarrier where
  toFun := entropyBoostProjective t
  invFun := entropyBoostProjective (-t)
  left_inv p := by
    refine Projectivization.ind (p := p) ?_
    intro X hX
    simp only [entropyBoostProjective, Projectivization.map_mk]
    congr 1
    exact entropyBoost_neg_apply t X
  right_inv p := by
    refine Projectivization.ind (p := p) ?_
    intro X hX
    simp only [entropyBoostProjective, Projectivization.map_mk]
    congr 1
    exact entropyBoost_apply_neg t X

@[simp] theorem entropyBoostProjectiveEquiv_apply (t : ℝ)
    (p : ProjectiveCarrier) :
    entropyBoostProjectiveEquiv t p = entropyBoostProjective t p := rfl

@[simp] theorem entropyBoostProjectiveEquiv_symm_apply (t : ℝ)
    (p : ProjectiveCarrier) :
    (entropyBoostProjectiveEquiv t).symm p =
      entropyBoostProjective (-t) p := rfl

theorem causalMinus_ne_zero : causalMinus ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [causalMinus] at h0

theorem causalPlus_ne_zero : causalPlus ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [causalPlus] at h0

theorem entropyMinus_ne_zero : entropyMinus ≠ 0 := by
  intro h
  have h2 := congrFun h 2
  change (1 / 2 : ℝ) = 0 at h2
  norm_num at h2

theorem entropyPlus_ne_zero : entropyPlus ≠ 0 := by
  intro h
  have h2 := congrFun h 2
  change (1 / 2 : ℝ) = 0 at h2
  norm_num at h2

theorem entropyBoostProjective_entropyMinus_fixed (t : ℝ) :
    entropyBoostProjective t
        (Projectivization.mk ℝ entropyMinus entropyMinus_ne_zero) =
      Projectivization.mk ℝ entropyMinus entropyMinus_ne_zero := by
  rw [entropyBoostProjective, Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
  exact ⟨Units.mk0 (Real.exp t) (Real.exp_ne_zero t), by
    change Real.exp t • entropyMinus = entropyBoost t entropyMinus
    rw [entropyBoost_entropyMinus]⟩

theorem entropyBoostProjective_entropyPlus_fixed (t : ℝ) :
    entropyBoostProjective t
        (Projectivization.mk ℝ entropyPlus entropyPlus_ne_zero) =
      Projectivization.mk ℝ entropyPlus entropyPlus_ne_zero := by
  rw [entropyBoostProjective, Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
  exact ⟨Units.mk0 (Real.exp (-t)) (Real.exp_ne_zero (-t)), by
    change Real.exp (-t) • entropyPlus = entropyBoost t entropyPlus
    rw [entropyBoost_entropyPlus]⟩

theorem entropyBoostProjective_add (s t : ℝ) (p : ProjectiveCarrier) :
    entropyBoostProjective (s + t) p =
      entropyBoostProjective s (entropyBoostProjective t p) := by
  refine Projectivization.ind (p := p) ?_
  intro X hX
  rw [entropyBoostProjective, Projectivization.map_mk]
  change Projectivization.mk ℝ (entropyBoost (s + t) X) _ =
    Projectivization.mk ℝ (entropyBoost s (entropyBoost t X)) _
  congr 1
  exact entropyBoost_add s t X

end InfoGeometry.Clifford.SplitRealNullTetrad
