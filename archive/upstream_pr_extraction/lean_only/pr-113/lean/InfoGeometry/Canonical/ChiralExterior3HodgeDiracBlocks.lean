import Mathlib.Tactic
import InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge

/-!
# Chiral blocks of the finite exterior Hodge--Dirac operator

For the native three-dimensional exterior carrier, `exteriorGrade3` is the
grading involution and the two projectors split the carrier into its even and
odd sectors.  The chiral Hodge--Dirac blocks are the off-diagonal pieces

`D₊ = P₋ D P₊` and `D₋ = P₊ D P₋`.

This is a finite algebraic block decomposition.  It does not assert a Hilbert
completion, a spectral theorem, or an analytic Dirac operator.
-/

noncomputable section

namespace InfoGeometry.Canonical.ChiralExterior3HodgeDiracBlocks

open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge

abbrev ChiralEnd := Exterior3End

def chiralProjectorPlus : ChiralEnd :=
  (1 / 2 : ℝ) • ((1 : ChiralEnd) + exteriorGrade3.toLinearMap)

def chiralProjectorMinus : ChiralEnd :=
  (1 / 2 : ℝ) • ((1 : ChiralEnd) - exteriorGrade3.toLinearMap)

theorem chiralProjectorPlus_add_minus :
    chiralProjectorPlus + chiralProjectorMinus = (1 : ChiralEnd) := by
  apply LinearMap.ext
  intro ψ
  simp [chiralProjectorPlus, chiralProjectorMinus]
  module

theorem chiralProjectorPlus_mul_minus :
    chiralProjectorPlus * chiralProjectorMinus = 0 := by
  apply LinearMap.ext
  intro ψ
  simp [chiralProjectorPlus, chiralProjectorMinus,
    exteriorGrade3_involutive]
  module

theorem chiralProjectorMinus_mul_plus :
    chiralProjectorMinus * chiralProjectorPlus = 0 := by
  apply LinearMap.ext
  intro ψ
  simp [chiralProjectorPlus, chiralProjectorMinus,
    exteriorGrade3_involutive]
  module

theorem chiralProjectorPlus_sq :
    chiralProjectorPlus * chiralProjectorPlus = chiralProjectorPlus := by
  apply LinearMap.ext
  intro ψ
  simp [chiralProjectorPlus, exteriorGrade3_involutive]
  module

theorem chiralProjectorMinus_sq :
    chiralProjectorMinus * chiralProjectorMinus = chiralProjectorMinus := by
  apply LinearMap.ext
  intro ψ
  simp [chiralProjectorMinus, exteriorGrade3_involutive]
  module

def chiralHodgeDiracPlus (v : V3) (φ : Module.Dual ℝ V3) : ChiralEnd :=
  chiralProjectorMinus * exteriorHodgeDirac3 v φ * chiralProjectorPlus

def chiralHodgeDiracMinus (v : V3) (φ : Module.Dual ℝ V3) : ChiralEnd :=
  chiralProjectorPlus * exteriorHodgeDirac3 v φ * chiralProjectorMinus

theorem chiralProjectorPlus_mul_hodgeDirac_eq_hodgeDirac_mul_minus
    (v : V3) (φ : Module.Dual ℝ V3) :
    chiralProjectorPlus * exteriorHodgeDirac3 v φ =
      exteriorHodgeDirac3 v φ * chiralProjectorMinus := by
  apply LinearMap.ext
  intro ψ
  have hodd : exteriorGrade3.toLinearMap (exteriorHodgeDirac3 v φ ψ) =
      -(exteriorHodgeDirac3 v φ (exteriorGrade3.toLinearMap ψ)) :=
    exteriorHodgeDirac3_odd v φ ψ
  simp only [chiralProjectorPlus, chiralProjectorMinus,
    LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply,
    Module.End.mul_apply, LinearMap.smul_apply, map_smul, map_sub]
  rw [hodd]
  module

theorem chiralProjectorMinus_mul_hodgeDirac_eq_hodgeDirac_mul_plus
    (v : V3) (φ : Module.Dual ℝ V3) :
    chiralProjectorMinus * exteriorHodgeDirac3 v φ =
      exteriorHodgeDirac3 v φ * chiralProjectorPlus := by
  apply LinearMap.ext
  intro ψ
  have hodd : exteriorGrade3.toLinearMap (exteriorHodgeDirac3 v φ ψ) =
      -(exteriorHodgeDirac3 v φ (exteriorGrade3.toLinearMap ψ)) :=
    exteriorHodgeDirac3_odd v φ ψ
  simp only [chiralProjectorPlus, chiralProjectorMinus,
    LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply,
    Module.End.mul_apply, LinearMap.smul_apply, map_smul, map_add]
  rw [hodd]
  module

theorem chiralHodgeDiracPlus_eq_hodgeDirac_mul_plus
    (v : V3) (φ : Module.Dual ℝ V3) :
    chiralHodgeDiracPlus v φ =
      exteriorHodgeDirac3 v φ * chiralProjectorPlus := by
  dsimp [chiralHodgeDiracPlus]
  rw [chiralProjectorMinus_mul_hodgeDirac_eq_hodgeDirac_mul_plus]
  rw [mul_assoc, chiralProjectorPlus_sq]

theorem chiralHodgeDiracMinus_eq_hodgeDirac_mul_minus
    (v : V3) (φ : Module.Dual ℝ V3) :
    chiralHodgeDiracMinus v φ =
      exteriorHodgeDirac3 v φ * chiralProjectorMinus := by
  dsimp [chiralHodgeDiracMinus]
  rw [chiralProjectorPlus_mul_hodgeDirac_eq_hodgeDirac_mul_minus]
  rw [mul_assoc, chiralProjectorMinus_sq]

theorem chiralHodgeDiracPlus_eq_minus_mul_hodgeDirac
    (v : V3) (φ : Module.Dual ℝ V3) :
    chiralHodgeDiracPlus v φ =
      chiralProjectorMinus * exteriorHodgeDirac3 v φ := by
  rw [chiralHodgeDiracPlus_eq_hodgeDirac_mul_plus]
  rw [← chiralProjectorMinus_mul_hodgeDirac_eq_hodgeDirac_mul_plus]

theorem chiralHodgeDiracMinus_eq_plus_mul_hodgeDirac
    (v : V3) (φ : Module.Dual ℝ V3) :
    chiralHodgeDiracMinus v φ =
      chiralProjectorPlus * exteriorHodgeDirac3 v φ := by
  rw [chiralHodgeDiracMinus_eq_hodgeDirac_mul_minus]
  rw [← chiralProjectorPlus_mul_hodgeDirac_eq_hodgeDirac_mul_minus]

theorem chiralHodgeDirac_plus_diagonal_zero
    (v : V3) (φ : Module.Dual ℝ V3) :
    chiralProjectorPlus * exteriorHodgeDirac3 v φ * chiralProjectorPlus = 0 := by
  rw [chiralProjectorPlus_mul_hodgeDirac_eq_hodgeDirac_mul_minus]
  rw [mul_assoc, chiralProjectorMinus_mul_plus]
  simp

theorem chiralHodgeDirac_minus_diagonal_zero
    (v : V3) (φ : Module.Dual ℝ V3) :
    chiralProjectorMinus * exteriorHodgeDirac3 v φ * chiralProjectorMinus = 0 := by
  rw [chiralProjectorMinus_mul_hodgeDirac_eq_hodgeDirac_mul_plus]
  rw [mul_assoc, chiralProjectorPlus_mul_minus]
  simp

theorem chiralHodgeDiracPlus_is_off_diagonal
    (v : V3) (φ : Module.Dual ℝ V3) :
    chiralProjectorMinus * chiralHodgeDiracPlus v φ =
      chiralHodgeDiracPlus v φ ∧
    chiralHodgeDiracPlus v φ * chiralProjectorPlus =
      chiralHodgeDiracPlus v φ := by
  constructor
  · rw [chiralHodgeDiracPlus_eq_minus_mul_hodgeDirac]
    calc chiralProjectorMinus * (chiralProjectorMinus * exteriorHodgeDirac3 v φ)
      _ = (chiralProjectorMinus * chiralProjectorMinus) * exteriorHodgeDirac3 v φ := by noncomm_ring
      _ = chiralProjectorMinus * exteriorHodgeDirac3 v φ := by rw [chiralProjectorMinus_sq]
  · rw [chiralHodgeDiracPlus_eq_hodgeDirac_mul_plus]
    calc (exteriorHodgeDirac3 v φ * chiralProjectorPlus) * chiralProjectorPlus
      _ = exteriorHodgeDirac3 v φ * (chiralProjectorPlus * chiralProjectorPlus) := by noncomm_ring
      _ = exteriorHodgeDirac3 v φ * chiralProjectorPlus := by rw [chiralProjectorPlus_sq]

theorem chiralHodgeDiracMinus_is_off_diagonal
    (v : V3) (φ : Module.Dual ℝ V3) :
    chiralProjectorPlus * chiralHodgeDiracMinus v φ =
      chiralHodgeDiracMinus v φ ∧
    chiralHodgeDiracMinus v φ * chiralProjectorMinus =
      chiralHodgeDiracMinus v φ := by
  constructor
  · rw [chiralHodgeDiracMinus_eq_plus_mul_hodgeDirac]
    calc chiralProjectorPlus * (chiralProjectorPlus * exteriorHodgeDirac3 v φ)
      _ = (chiralProjectorPlus * chiralProjectorPlus) * exteriorHodgeDirac3 v φ := by noncomm_ring
      _ = chiralProjectorPlus * exteriorHodgeDirac3 v φ := by rw [chiralProjectorPlus_sq]
  · rw [chiralHodgeDiracMinus_eq_hodgeDirac_mul_minus]
    calc (exteriorHodgeDirac3 v φ * chiralProjectorMinus) * chiralProjectorMinus
      _ = exteriorHodgeDirac3 v φ * (chiralProjectorMinus * chiralProjectorMinus) := by noncomm_ring
      _ = exteriorHodgeDirac3 v φ * chiralProjectorMinus := by rw [chiralProjectorMinus_sq]

theorem chiralHodgeDiracPlus_sq_zero
    (v : V3) (φ : Module.Dual ℝ V3) :
    chiralHodgeDiracPlus v φ * chiralHodgeDiracPlus v φ = 0 := by
  dsimp [chiralHodgeDiracPlus]
  calc
    chiralProjectorMinus * exteriorHodgeDirac3 v φ * chiralProjectorPlus *
        (chiralProjectorMinus * exteriorHodgeDirac3 v φ * chiralProjectorPlus)
      = chiralProjectorMinus * exteriorHodgeDirac3 v φ *
        (chiralProjectorPlus * chiralProjectorMinus) *
        exteriorHodgeDirac3 v φ * chiralProjectorPlus := by noncomm_ring
    _ = 0 := by rw [chiralProjectorPlus_mul_minus]; simp

theorem chiralHodgeDiracMinus_sq_zero
    (v : V3) (φ : Module.Dual ℝ V3) :
    chiralHodgeDiracMinus v φ * chiralHodgeDiracMinus v φ = 0 := by
  dsimp [chiralHodgeDiracMinus]
  calc
    chiralProjectorPlus * exteriorHodgeDirac3 v φ * chiralProjectorMinus *
        (chiralProjectorPlus * exteriorHodgeDirac3 v φ * chiralProjectorMinus)
      = chiralProjectorPlus * exteriorHodgeDirac3 v φ *
        (chiralProjectorMinus * chiralProjectorPlus) *
        exteriorHodgeDirac3 v φ * chiralProjectorMinus := by noncomm_ring
    _ = 0 := by rw [chiralProjectorMinus_mul_plus]; simp

theorem exteriorHodgeDirac3_eq_chiral_blocks
    (v : V3) (φ : Module.Dual ℝ V3) :
    exteriorHodgeDirac3 v φ =
      chiralHodgeDiracPlus v φ + chiralHodgeDiracMinus v φ := by
  rw [chiralHodgeDiracPlus_eq_hodgeDirac_mul_plus,
    chiralHodgeDiracMinus_eq_hodgeDirac_mul_minus]
  calc exteriorHodgeDirac3 v φ = exteriorHodgeDirac3 v φ * 1 := by rw [mul_one]
    _ = exteriorHodgeDirac3 v φ * (chiralProjectorPlus + chiralProjectorMinus) := by rw [chiralProjectorPlus_add_minus]
    _ = exteriorHodgeDirac3 v φ * chiralProjectorPlus +
        exteriorHodgeDirac3 v φ * chiralProjectorMinus := by noncomm_ring

theorem exteriorHodgeDirac3_sq_eq_chiral_block_products
    (v : V3) (φ : Module.Dual ℝ V3) :
    exteriorHodgeDirac3 v φ * exteriorHodgeDirac3 v φ =
      chiralHodgeDiracMinus v φ * chiralHodgeDiracPlus v φ +
        chiralHodgeDiracPlus v φ * chiralHodgeDiracMinus v φ := by
  have hdec := exteriorHodgeDirac3_eq_chiral_blocks v φ
  calc exteriorHodgeDirac3 v φ * exteriorHodgeDirac3 v φ
    _ = (chiralHodgeDiracPlus v φ + chiralHodgeDiracMinus v φ) *
        (chiralHodgeDiracPlus v φ + chiralHodgeDiracMinus v φ) := by rw [← hdec]
    _ = chiralHodgeDiracPlus v φ * chiralHodgeDiracPlus v φ +
        chiralHodgeDiracPlus v φ * chiralHodgeDiracMinus v φ +
        chiralHodgeDiracMinus v φ * chiralHodgeDiracPlus v φ +
        chiralHodgeDiracMinus v φ * chiralHodgeDiracMinus v φ := by noncomm_ring
    _ = 0 + chiralHodgeDiracPlus v φ * chiralHodgeDiracMinus v φ +
        chiralHodgeDiracMinus v φ * chiralHodgeDiracPlus v φ + 0 := by
        rw [chiralHodgeDiracPlus_sq_zero, chiralHodgeDiracMinus_sq_zero]
    _ = chiralHodgeDiracMinus v φ * chiralHodgeDiracPlus v φ +
        chiralHodgeDiracPlus v φ * chiralHodgeDiracMinus v φ := by abel

def chiralHodgeLaplacianPlus (v : V3) (φ : Module.Dual ℝ V3) : ChiralEnd :=
  chiralProjectorPlus * exteriorHodgeLaplacian3 v φ * chiralProjectorPlus

def chiralHodgeLaplacianMinus (v : V3) (φ : Module.Dual ℝ V3) : ChiralEnd :=
  chiralProjectorMinus * exteriorHodgeLaplacian3 v φ * chiralProjectorMinus

theorem chiralHodgeLaplacianPlus_eq_minus_plus
    (v : V3) (φ : Module.Dual ℝ V3) :
    chiralHodgeLaplacianPlus v φ =
      chiralHodgeDiracMinus v φ * chiralHodgeDiracPlus v φ := by
  dsimp [chiralHodgeLaplacianPlus]
  rw [← exteriorHodgeDirac3_sq v φ]
  rw [chiralHodgeDiracMinus_eq_plus_mul_hodgeDirac,
    chiralHodgeDiracPlus_eq_hodgeDirac_mul_plus]
  noncomm_ring

theorem chiralHodgeLaplacianMinus_eq_plus_minus
    (v : V3) (φ : Module.Dual ℝ V3) :
    chiralHodgeLaplacianMinus v φ =
      chiralHodgeDiracPlus v φ * chiralHodgeDiracMinus v φ := by
  dsimp [chiralHodgeLaplacianMinus]
  rw [← exteriorHodgeDirac3_sq v φ]
  rw [chiralHodgeDiracPlus_eq_minus_mul_hodgeDirac,
    chiralHodgeDiracMinus_eq_hodgeDirac_mul_minus]
  noncomm_ring

theorem exteriorHodgeLaplacian3_eq_chiral_blocks
    (v : V3) (φ : Module.Dual ℝ V3) :
    exteriorHodgeLaplacian3 v φ =
      chiralHodgeLaplacianPlus v φ + chiralHodgeLaplacianMinus v φ := by
  rw [← exteriorHodgeDirac3_sq v φ,
    exteriorHodgeDirac3_sq_eq_chiral_block_products,
    ← chiralHodgeLaplacianPlus_eq_minus_plus,
    ← chiralHodgeLaplacianMinus_eq_plus_minus]

end InfoGeometry.Canonical.ChiralExterior3HodgeDiracBlocks
