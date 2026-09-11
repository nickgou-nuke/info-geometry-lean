import InfoGeometry.Lie.SplitRealNullTetradZornProjectiveBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Projective fixed sectors of the split `(2,2)` tetrad boost

The two-dimensional eigenspaces of the uniform double-Witt boost descend to
pointwise-fixed projective sectors.  We record this inclusion of the fixed
locus without claiming that it is the whole fixed locus.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Lie.SplitRealNullTetradProjectiveFixedLocus

open InfoGeometry.Clifford.SplitRealNullTetrad
open InfoGeometry.Lie.SplitRealNullTetradZornBridge.Tetrad
open InfoGeometry.Lie.SplitRealNullTetradZornProjectiveBridge

abbrev Coeff2 := InfoGeometry.Algebra.FiniteSpin.Vec2R

noncomputable def positiveWittEmbedding : Coeff2 →ₗ[ℝ] Carrier where
  toFun a := a 0 • causalMinus + a 1 • entropyMinus
  map_add' a b := by
    simp only [Pi.add_apply, add_smul]
    module
  map_smul' r a := by simp [smul_smul]

noncomputable def negativeWittEmbedding : Coeff2 →ₗ[ℝ] Carrier where
  toFun a := a 0 • causalPlus + a 1 • entropyPlus
  map_add' a b := by
    simp only [Pi.add_apply, add_smul]
    module
  map_smul' r a := by simp [smul_smul]

def positiveWittEigenspace : Submodule ℝ Carrier :=
  LinearMap.range positiveWittEmbedding

def negativeWittEigenspace : Submodule ℝ Carrier :=
  LinearMap.range negativeWittEmbedding

theorem positiveWittEigenspace_mem_iff (X : Carrier) :
    X ∈ positiveWittEigenspace ↔
      X 1 = X 0 ∧ X 3 = X 2 := by
  constructor
  · rintro ⟨a, rfl⟩
    simp [positiveWittEmbedding, causalMinus, entropyMinus]
  · rintro ⟨h₁, h₃⟩
    refine ⟨![2 * X 0, 2 * X 2], ?_⟩
    funext i
    fin_cases i <;>
      simp [positiveWittEmbedding, causalMinus, entropyMinus, h₁, h₃] <;>
      ring

theorem negativeWittEigenspace_mem_iff (X : Carrier) :
    X ∈ negativeWittEigenspace ↔
      X 1 = -X 0 ∧ X 3 = -X 2 := by
  constructor
  · rintro ⟨a, rfl⟩
    simp [negativeWittEmbedding, causalPlus, entropyPlus]
  · rintro ⟨h₁, h₃⟩
    refine ⟨![2 * X 0, 2 * X 2], ?_⟩
    funext i
    fin_cases i <;>
      simp [negativeWittEmbedding, causalPlus, entropyPlus, h₁, h₃] <;>
      ring

theorem positive_negativeWittEigenspace_decomposition (X : Carrier) :
    ∃ Xplus Xminus,
      Xplus ∈ positiveWittEigenspace ∧
      Xminus ∈ negativeWittEigenspace ∧
      Xplus + Xminus = X := by
  let Xplus : Carrier :=
    positiveWittEmbedding ![X 0 + X 1, X 2 + X 3]
  let Xminus : Carrier :=
    negativeWittEmbedding ![X 0 - X 1, X 2 - X 3]
  refine ⟨Xplus, Xminus, ⟨_, rfl⟩, ⟨_, rfl⟩, ?_⟩
  funext i
  fin_cases i <;>
    simp [Xplus, Xminus, positiveWittEmbedding, negativeWittEmbedding,
      causalMinus, causalPlus, entropyMinus, entropyPlus] <;>
    ring

theorem doubleWittBoost_positiveWittEigenspace (t : ℝ) (X : Carrier)
    (hX : X ∈ positiveWittEigenspace) :
    doubleWittBoost t X = Real.exp t • X := by
  rcases hX with ⟨a, rfl⟩
  change doubleWittBoost t
      (a 0 • causalMinus + a 1 • entropyMinus) =
        Real.exp t • (a 0 • causalMinus + a 1 • entropyMinus)
  rw [map_add, map_smul, map_smul,
    doubleWittBoost_causalMinus, doubleWittBoost_entropyMinus,
    smul_add]
  module

theorem doubleWittBoost_negativeWittEigenspace (t : ℝ) (X : Carrier)
    (hX : X ∈ negativeWittEigenspace) :
    doubleWittBoost t X = Real.exp (-t) • X := by
  rcases hX with ⟨a, rfl⟩
  change doubleWittBoost t
      (a 0 • causalPlus + a 1 • entropyPlus) =
        Real.exp (-t) • (a 0 • causalPlus + a 1 • entropyPlus)
  rw [map_add, map_smul, map_smul,
    doubleWittBoost_causalPlus, doubleWittBoost_entropyPlus,
    smul_add]
  module

theorem doubleWittBoostProjective_positiveWitt_fixed (t : ℝ)
    (X : Carrier) (hX : X ∈ positiveWittEigenspace) (hX0 : X ≠ 0) :
    doubleWittBoostProjectiveMap t (Projectivization.mk ℝ X hX0) =
      Projectivization.mk ℝ X hX0 := by
  rw [doubleWittBoostProjectiveMap, Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
  exact ⟨Units.mk0 (Real.exp t) (Real.exp_ne_zero t), by
    change Real.exp t • X = doubleWittBoost t X
    rw [doubleWittBoost_positiveWittEigenspace t X hX]
  ⟩

theorem doubleWittBoostProjective_negativeWitt_fixed (t : ℝ)
    (X : Carrier) (hX : X ∈ negativeWittEigenspace) (hX0 : X ≠ 0) :
    doubleWittBoostProjectiveMap t (Projectivization.mk ℝ X hX0) =
      Projectivization.mk ℝ X hX0 := by
  rw [doubleWittBoostProjectiveMap, Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
  exact ⟨Units.mk0 (Real.exp (-t)) (Real.exp_ne_zero (-t)), by
    change Real.exp (-t) • X = doubleWittBoost t X
    rw [doubleWittBoost_negativeWittEigenspace t X hX]
  ⟩

end InfoGeometry.Lie.SplitRealNullTetradProjectiveFixedLocus
