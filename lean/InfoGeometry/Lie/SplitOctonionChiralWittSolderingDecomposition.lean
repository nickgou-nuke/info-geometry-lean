import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionCircularWittForm
import InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge

/-!
# Chiral Witt soldering decomposition

Finite-dimensional coordinate-level κ decomposition.  This owner deliberately
uses only the linear involution and Witt carrier; it does not identify the
transported exterior endomorphism algebra with split-octonion multiplication.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionChiralWittSolderingDecomposition

open InfoGeometry.Lie.SplitOctonionCircularWittForm
open InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge

abbrev Coord := InfoGeometry.Algebra.FiniteSpin.Vec8R
abbrev Four := InfoGeometry.Algebra.FiniteSpin.Vec4R

def minkowskiSignEquiv : Four ≃ₗ[ℝ] Four where
  toFun ξ := ![ξ 0, -ξ 1, -ξ 2, -ξ 3]
  invFun ξ := ![ξ 0, -ξ 1, -ξ 2, -ξ 3]
  left_inv := by intro ξ; funext i; fin_cases i <;> simp
  right_inv := by intro ξ; funext i; fin_cases i <;> simp
  map_add' ξ η := by funext i; fin_cases i <;> simp [add_comm]
  map_smul' c ξ := by funext i; fin_cases i <;> simp

def wittCovectorDuality : Four ≃ₗ[ℝ] Module.Dual ℝ Four :=
  minkowskiSignEquiv.trans ((Pi.basisFun ℝ (Fin 4)).toDualEquiv)

theorem wittCovectorDuality_injective :
    Function.Injective wittCovectorDuality := wittCovectorDuality.injective

@[simp] theorem wittCovectorDuality_apply (ξ x : Four) :
    wittCovectorDuality ξ x =
      ξ 0 * x 0 - ξ 1 * x 1 - ξ 2 * x 2 - ξ 3 * x 3 := by
  let b := Pi.basisFun ℝ (Fin 4)
  change b.toDual (minkowskiSignEquiv ξ) x = _
  rw [← b.sum_repr x]
  simp_rw [map_sum, LinearMap.map_smul, smul_eq_mul, b.toDual_apply_left]
  simp [b, minkowskiSignEquiv, Fin.sum_univ_succ, Pi.single_apply]
  ring

def symmetrize (X : Coord) : Coord :=
  fun i => (1 / 2 : ℝ) * (X i + kappa X i)

def antisymmetrize (X : Coord) : Coord :=
  fun i => (1 / 2 : ℝ) * (X i - kappa X i)

def kappaEnd : Module.End ℝ Coord where
  toFun := kappa
  map_add' X Y := by
    ext i
    fin_cases i <;> simp [kappa]
  map_smul' c X := by
    ext i
    fin_cases i <;> simp [kappa]

def symmetrizeEnd : Module.End ℝ Coord :=
  (1 / 2 : ℝ) • (1 + kappaEnd)

def antisymmetrizeEnd : Module.End ℝ Coord :=
  (1 / 2 : ℝ) • (1 - kappaEnd)

theorem kappaEnd_apply (X : Coord) : kappaEnd X = kappa X := rfl

theorem kappaEnd_sq : kappaEnd * kappaEnd = (1 : Module.End ℝ Coord) := by
  apply LinearMap.ext
  intro X
  ext i
  fin_cases i <;> simp [kappaEnd, kappa]

theorem symmetrizeEnd_apply (X : Coord) : symmetrizeEnd X = symmetrize X := by
  ext i
  fin_cases i <;> dsimp [symmetrizeEnd, symmetrize, kappaEnd, kappa]

theorem antisymmetrizeEnd_apply (X : Coord) :
    antisymmetrizeEnd X = antisymmetrize X := by
  ext i
  fin_cases i <;> dsimp [antisymmetrizeEnd, antisymmetrize, kappaEnd, kappa]

theorem symmetrizeEnd_sq :
    symmetrizeEnd * symmetrizeEnd = symmetrizeEnd := by
  apply LinearMap.ext
  intro X
  ext i
  fin_cases i <;> dsimp [symmetrizeEnd, kappaEnd, kappa] <;> ring

theorem antisymmetrizeEnd_sq :
    antisymmetrizeEnd * antisymmetrizeEnd = antisymmetrizeEnd := by
  apply LinearMap.ext
  intro X
  ext i
  fin_cases i <;> dsimp [antisymmetrizeEnd, kappaEnd, kappa] <;> ring

theorem symmetrizeEnd_add_antisymmetrizeEnd :
    symmetrizeEnd + antisymmetrizeEnd = (1 : Module.End ℝ Coord) := by
  apply LinearMap.ext
  intro X
  ext i
  fin_cases i <;> dsimp [symmetrizeEnd, antisymmetrizeEnd, kappaEnd, kappa] <;> ring

theorem symmetrizeEnd_mul_antisymmetrizeEnd :
    symmetrizeEnd * antisymmetrizeEnd = (0 : Module.End ℝ Coord) := by
  apply LinearMap.ext
  intro X
  ext i
  fin_cases i <;> dsimp [symmetrizeEnd, antisymmetrizeEnd, kappaEnd, kappa] <;> ring

theorem antisymmetrizeEnd_mul_symmetrizeEnd :
    antisymmetrizeEnd * symmetrizeEnd = (0 : Module.End ℝ Coord) := by
  apply LinearMap.ext
  intro X
  ext i
  fin_cases i <;> dsimp [symmetrizeEnd, antisymmetrizeEnd, kappaEnd, kappa] <;> ring

def VPlus : Submodule ℝ Coord :=
  LinearMap.ker (kappaEnd - 1)

def VMinus : Submodule ℝ Coord :=
  LinearMap.ker (kappaEnd + 1)

theorem mem_VPlus_iff (X : Coord) :
    X ∈ VPlus ↔ kappa X = X := by
  dsimp [VPlus]
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    ext i
    have hi := congrFun h i
    dsimp [kappaEnd] at hi
    linarith
  · intro h
    ext i
    dsimp [kappaEnd]
    have hi := congrFun h i
    linarith

theorem mem_VMinus_iff (X : Coord) :
    X ∈ VMinus ↔ kappa X = -X := by
  dsimp [VMinus]
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    ext i
    have hi := congrFun h i
    dsimp [kappaEnd] at hi
    simp only [Pi.neg_apply]
    linarith
  · intro h
    ext i
    dsimp [kappaEnd]
    have hi := congrFun h i
    simp only [Pi.neg_apply] at hi
    linarith

theorem range_symmetrizeEnd_eq_VPlus :
    LinearMap.range symmetrizeEnd = VPlus := by
  ext X
  rw [LinearMap.mem_range, mem_VPlus_iff]
  constructor
  · rintro ⟨Y, rfl⟩
    rw [symmetrizeEnd_apply]
    ext i
    fin_cases i <;> dsimp [symmetrize, kappa] <;> ring
  · intro hX
    use X
    rw [symmetrizeEnd_apply]
    ext i
    dsimp [symmetrize]
    rw [congrFun hX i]
    ring

theorem range_antisymmetrizeEnd_eq_VMinus :
    LinearMap.range antisymmetrizeEnd = VMinus := by
  ext X
  rw [LinearMap.mem_range, mem_VMinus_iff]
  constructor
  · rintro ⟨Y, rfl⟩
    rw [antisymmetrizeEnd_apply]
    ext i
    fin_cases i <;> dsimp [antisymmetrize, kappa] <;> ring
  · intro hX
    use X
    rw [antisymmetrizeEnd_apply]
    ext i
    dsimp [antisymmetrize]
    rw [congrFun hX i]
    simp only [Pi.neg_apply]
    ring

theorem VPlus_inf_VMinus_eq_bot :
    VPlus ⊓ VMinus = ⊥ := by
  ext X
  simp only [Submodule.mem_inf, mem_VPlus_iff, mem_VMinus_iff, Submodule.mem_bot]
  constructor
  · rintro ⟨hP, hM⟩
    ext i
    have hp := congrFun hP i
    have hm := congrFun hM i
    simp only [Pi.neg_apply] at hm
    have : X i = 0 := by linarith [hp, hm]
    exact this
  · rintro rfl
    simp only [neg_zero, and_self]
    ext i
    fin_cases i <;> dsimp [kappa]

theorem kappa_symmetrize (X : Coord) :
    kappa (symmetrize X) = symmetrize X := by
  ext i
  fin_cases i <;> dsimp [symmetrize, kappa] <;> ring

theorem kappa_antisymmetrize (X : Coord) :
    kappa (antisymmetrize X) = -antisymmetrize X := by
  ext i
  fin_cases i <;> dsimp [antisymmetrize, kappa] <;> ring

theorem symmetrize_add_antisymmetrize (X : Coord) :
    symmetrize X + antisymmetrize X = X := by
  ext i
  dsimp [symmetrize, antisymmetrize]
  ring

theorem symmetrize_idempotent (X : Coord) :
    symmetrize (symmetrize X) = symmetrize X := by
  ext i
  fin_cases i <;> dsimp [symmetrize, kappa] <;> ring

theorem antisymmetrize_idempotent (X : Coord) :
    antisymmetrize (antisymmetrize X) = antisymmetrize X := by
  ext i
  fin_cases i <;> dsimp [antisymmetrize, kappa] <;> ring

theorem map_preserves_kappa_fixed
    (T : Coord → Coord)
    (hT : ∀ X, T (kappa X) = kappa (T X))
    {X : Coord} (hX : kappa X = X) :
    kappa (T X) = T X := by
  rw [← hT X, hX]

theorem map_preserves_kappa_antifixed
    (T : Coord → Coord)
    (hT : ∀ X, T (kappa X) = kappa (T X))
    (hneg : ∀ X, T (-X) = -T X)
    {X : Coord} (hX : kappa X = -X) :
    kappa (T X) = -T X := by
  calc
    kappa (T X) = T (kappa X) := (hT X).symm
    _ = T (-X) := by rw [hX]
    _ = -T X := hneg X

theorem circularPeircePolar_symmetrize_antisymmetrize (X Y : Coord) :
    circularPeircePolar (symmetrize X) (antisymmetrize Y) = 0 := by
  dsimp [circularPeircePolar, symmetrize, antisymmetrize, kappa]
  ring

def splitOctonionBilinear (X Y : Coord) : ℝ :=
  (circularWittQuadratic (X + Y) - circularWittQuadratic X -
      circularWittQuadratic Y) / 2

theorem splitOctonionBilinear_eq_half_circularPeircePolar (X Y : Coord) :
    splitOctonionBilinear X Y = circularPeircePolar X Y / 2 := by
  unfold splitOctonionBilinear
  rw [← circularPeircePolar_from_wittQuadratic]

theorem splitOctonionBilinear_symmetrize_antisymmetrize (X Y : Coord) :
    splitOctonionBilinear (symmetrize X) (antisymmetrize Y) = 0 := by
  rw [splitOctonionBilinear_eq_half_circularPeircePolar,
    circularPeircePolar_symmetrize_antisymmetrize]
  ring

theorem splitOctonionBilinear_fixed_antifixed
    (X Y : Coord)
    (hX : kappa X = X)
    (hY : kappa Y = -Y) :
    splitOctonionBilinear X Y = 0 := by
  have hX' : symmetrize X = X := by
    ext i
    dsimp [symmetrize]
    rw [congrFun hX i]
    ring
  have hY' : antisymmetrize Y = Y := by
    ext i
    dsimp [antisymmetrize]
    rw [congrFun hY i]
    simp only [Pi.neg_apply]
    ring
  rw [← hX', ← hY']
  exact splitOctonionBilinear_symmetrize_antisymmetrize X Y

end InfoGeometry.Lie.SplitOctonionChiralWittSolderingDecomposition
