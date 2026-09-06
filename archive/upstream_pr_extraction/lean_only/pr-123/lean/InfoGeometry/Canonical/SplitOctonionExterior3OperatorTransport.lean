import Mathlib.Tactic
import InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
import InfoGeometry.Canonical.ExteriorAlgebraChiralHodgeDiracBlockBridge

/-!
# Operator transport from the exterior Hodge--Dirac carrier to split coordinates

The finite-dimensional linear equivalence already owned by
`SplitOctonionExterior3HodgeDiracBridge` transports the exterior creation,
contraction, grading, and Hodge--Dirac operators to the split-octonion
coordinate carrier.

## Key Formalized Results:
1. `transportEndAlgEquiv`: Conjugation $\operatorname{Ad}_e$ is a full $\mathbb{R}$-algebra equivalence:
   $$\operatorname{End}_{\mathbb{R}}(\Lambda^\bullet \mathbb{R}^3) \simeq_{\mathrm{Alg}} \operatorname{End}_{\mathbb{R}}(\mathrm{SplitCarrier})$$
2. `transportEnd_intertwines`: Downstream intertwiner diagram:
   $$\operatorname{Ad}_e(T) \circ e = e \circ T$$
3. `splitCoordinateCliffordGenerator_sq`: Transported hyperbolic Clifford representation on $V_3 \oplus V_3^*$:
   $$c(v, \varphi)^2 = \varphi(v) \cdot I$$
4. Chiral Projectors & Nilpotent Blocks on Split Coordinates:
   - $(P_\pm^e)^2 = P_\pm^e, \quad P_+^e P_-^e = 0$
   - $(D_\pm^e)^2 = 0$
   - $e \circ D_\pm = D_\pm^{\mathrm{split}} \circ e$

This is an operator-level realization only: it does not assert that the transported
maps are multiplication or norm maps of the nonassociative split-octonion algebra.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport

open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.ExteriorAlgebraChiralHodgeDiracBlockBridge

abbrev SplitCarrier := SplitOctonionCoordinateCarrier
abbrev SplitEnd := Module.End ℝ SplitCarrier

/-- Generic endomorphism conjugation by a linear equivalence. -/
def transportEndGeneric {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (e : E ≃ₗ[ℝ] F) (T : Module.End ℝ E) : Module.End ℝ F :=
  e.toLinearMap ∘ₗ T ∘ₗ e.symm.toLinearMap

def transportEnd (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (T : Exterior3End) : SplitEnd :=
  transportEndGeneric e T

@[simp] theorem transportEnd_apply
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (T : Exterior3End)
    (x : SplitCarrier) :
    transportEnd e T x = e (T (e.symm x)) := by
  rfl

theorem transportEnd_mul
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (S T : Exterior3End) :
    transportEnd e (S * T) = transportEnd e S * transportEnd e T := by
  apply LinearMap.ext
  intro x
  simp [transportEnd, transportEndGeneric, LinearMap.comp_apply, Module.End.mul_apply]

theorem transportEnd_add
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (S T : Exterior3End) :
    transportEnd e (S + T) = transportEnd e S + transportEnd e T := by
  apply LinearMap.ext
  intro x
  simp [transportEnd, transportEndGeneric, LinearMap.comp_apply, LinearMap.add_apply]

@[simp] theorem transportEnd_one
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) :
    transportEnd e (1 : Exterior3End) = (1 : SplitEnd) := by
  apply LinearMap.ext
  intro x
  simp [transportEnd, transportEndGeneric]

theorem transportEnd_smul
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (a : ℝ) (T : Exterior3End) :
    transportEnd e (a • T) = a • transportEnd e T := by
  apply LinearMap.ext
  intro x
  simp [transportEnd, transportEndGeneric]

theorem transportEnd_neg
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (T : Exterior3End) :
    transportEnd e (-T) = -transportEnd e T := by
  apply LinearMap.ext
  intro x
  simp [transportEnd, transportEndGeneric]

theorem transportEnd_pow
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (T : Exterior3End) (n : ℕ) :
    transportEnd e (T ^ n) = (transportEnd e T) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ, transportEnd_mul, ih]

/-- Transport preserves every power identity, in particular N-potency. -/
theorem transportEnd_nPotent
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (T : Exterior3End)
    (n : ℕ) (hT : T ^ n = T) :
    (transportEnd e T) ^ n = transportEnd e T := by
  rw [← transportEnd_pow, hT]

theorem transportEnd_symm_transportEnd
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (T : Exterior3End) :
    transportEndGeneric e.symm (transportEnd e T) = T := by
  apply LinearMap.ext
  intro x
  simp [transportEnd, transportEndGeneric]

theorem transportEnd_transportEnd_symm
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (T : SplitEnd) :
    transportEnd e (transportEndGeneric e.symm T) = T := by
  apply LinearMap.ext
  intro x
  simp [transportEnd, transportEndGeneric]

/-- 🏆 THEOREM: transportEnd packaged as an Algebra Equivalence. -/
def transportEndAlgEquiv (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) :
    Exterior3End ≃ₐ[ℝ] SplitEnd where
  toFun := transportEnd e
  invFun := transportEndGeneric e.symm
  left_inv := transportEnd_symm_transportEnd e
  right_inv := transportEnd_transportEnd_symm e
  map_mul' := transportEnd_mul e
  map_add' := transportEnd_add e
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [transportEnd_smul, transportEnd_one]

/-- 🏆 THEOREM: Polynomial evaluation commutes with transportEnd. -/
theorem transportEnd_polynomial_eval
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (p : Polynomial ℝ) (T : Exterior3End) :
    Polynomial.eval₂ (algebraMap ℝ SplitEnd) (transportEnd e T) p =
      transportEnd e (Polynomial.eval₂ (algebraMap ℝ Exterior3End) T p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.eval₂_add, Polynomial.eval₂_add, hp, hq]
      exact ((transportEndAlgEquiv e).map_add _ _).symm
  | monomial n a =>
      rw [Polynomial.eval₂_monomial, Polynomial.eval₂_monomial]
      have h1 : (transportEnd e T) ^ n = transportEnd e (T ^ n) := (transportEnd_pow e T n).symm
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
      rw [h1, smul_mul_assoc, one_mul, smul_mul_assoc, one_mul, transportEnd_smul]

/-- Transport preserves polynomial annihilating identities. -/
theorem transportEnd_polynomial_eq_zero
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (p : Polynomial ℝ) (T : Exterior3End)
    (h : Polynomial.eval₂ (algebraMap ℝ Exterior3End) T p = 0) :
    Polynomial.eval₂ (algebraMap ℝ SplitEnd) (transportEnd e T) p = 0 := by
  rw [transportEnd_polynomial_eval, h]
  exact map_zero (transportEndAlgEquiv e)

theorem transportEnd_intertwines
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (T : Exterior3End) :
    (transportEnd e T) ∘ₗ e.toLinearMap = e.toLinearMap ∘ₗ T := by
  apply LinearMap.ext
  intro x
  simp [transportEnd, transportEndGeneric]

def splitCoordinateWedge3 (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (v : V3) : SplitEnd :=
  transportEnd e (exteriorWedge3 v)

def splitCoordinateContract3
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (φ : Module.Dual ℝ V3) : SplitEnd :=
  transportEnd e (exteriorContract3 φ)

def splitCoordinateGrade3 (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) : SplitEnd :=
  transportEnd e exteriorGrade3.toLinearMap

def splitCoordinateHodgeDirac3
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (v : V3) (φ : Module.Dual ℝ V3) : SplitEnd :=
  transportEnd e (exteriorHodgeDirac3 v φ)

def splitCoordinateHodgeLaplacian3
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (v : V3) (φ : Module.Dual ℝ V3) : SplitEnd :=
  transportEnd e (exteriorHodgeLaplacian3 v φ)

theorem splitCoordinateWedge3_sq
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (v : V3) :
    splitCoordinateWedge3 e v * splitCoordinateWedge3 e v = 0 := by
  dsimp [splitCoordinateWedge3]
  rw [← transportEnd_mul, exteriorWedge3_sq]
  apply LinearMap.ext
  intro x
  simp [transportEnd, transportEndGeneric]

theorem splitCoordinateContract3_sq
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (φ : Module.Dual ℝ V3) :
    splitCoordinateContract3 e φ * splitCoordinateContract3 e φ = 0 := by
  dsimp [splitCoordinateContract3]
  rw [← transportEnd_mul, exteriorContract3_sq]
  apply LinearMap.ext
  intro x
  simp [transportEnd, transportEndGeneric]

theorem splitCoordinateWedgeContract_CAR
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (v : V3) (φ : Module.Dual ℝ V3) :
    splitCoordinateContract3 e φ * splitCoordinateWedge3 e v +
        splitCoordinateWedge3 e v * splitCoordinateContract3 e φ =
      (φ v) • (1 : SplitEnd) := by
  dsimp [splitCoordinateContract3, splitCoordinateWedge3]
  rw [← transportEnd_mul, ← transportEnd_mul, ← transportEnd_add]
  rw [exteriorContract3_wedge3_CAR φ v]
  rw [transportEnd_smul, transportEnd_one]

theorem splitCoordinateHodgeDirac3_sq
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (v : V3) (φ : Module.Dual ℝ V3) :
    splitCoordinateHodgeDirac3 e v φ * splitCoordinateHodgeDirac3 e v φ =
      splitCoordinateHodgeLaplacian3 e v φ := by
  dsimp [splitCoordinateHodgeDirac3, splitCoordinateHodgeLaplacian3]
  rw [← transportEnd_mul, exteriorHodgeDirac3_sq]

theorem splitCoordinateGrade3_sq
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) :
    splitCoordinateGrade3 e * splitCoordinateGrade3 e = (1 : SplitEnd) := by
  dsimp [splitCoordinateGrade3]
  rw [← transportEnd_mul]
  have h_invol : exteriorGrade3.toLinearMap * exteriorGrade3.toLinearMap = 1 := by
    apply LinearMap.ext
    intro x
    exact exteriorGrade3_involutive x
  rw [h_invol, transportEnd_one]

theorem splitCoordinateHodgeDirac3_odd
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (v : V3) (φ : Module.Dual ℝ V3) :
    splitCoordinateGrade3 e * splitCoordinateHodgeDirac3 e v φ =
      -(splitCoordinateHodgeDirac3 e v φ * splitCoordinateGrade3 e) := by
  dsimp [splitCoordinateGrade3, splitCoordinateHodgeDirac3]
  rw [← transportEnd_mul, ← transportEnd_mul, ← transportEnd_neg]
  have h_odd : exteriorGrade3.toLinearMap * exteriorHodgeDirac3 v φ =
      -(exteriorHodgeDirac3 v φ * exteriorGrade3.toLinearMap) := by
    apply LinearMap.ext
    intro x
    simp only [Module.End.mul_apply, LinearMap.neg_apply]
    exact exteriorHodgeDirac3_odd v φ x
  rw [h_odd]

/-- 🏆 THEOREM: Hyperbolic Clifford generator c(v, φ) = ε(v) + ι(φ) on the split-coordinate carrier. -/
def splitCoordinateCliffordGenerator
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (v : V3) (φ : Module.Dual ℝ V3) : SplitEnd :=
  splitCoordinateWedge3 e v + splitCoordinateContract3 e φ

theorem splitCoordinateCliffordGenerator_sq
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (v : V3) (φ : Module.Dual ℝ V3) :
    splitCoordinateCliffordGenerator e v φ * splitCoordinateCliffordGenerator e v φ =
      (φ v) • (1 : SplitEnd) := by
  dsimp [splitCoordinateCliffordGenerator, splitCoordinateWedge3, splitCoordinateContract3]
  rw [← transportEnd_add, ← transportEnd_mul]
  have hcar : (exteriorWedge3 v + exteriorContract3 φ) * (exteriorWedge3 v + exteriorContract3 φ) =
      (φ v) • (1 : Exterior3End) := by
    have h1 := exteriorWedge3_sq v
    have h2 := exteriorContract3_sq φ
    have h3 := exteriorContract3_wedge3_CAR φ v
    calc (exteriorWedge3 v + exteriorContract3 φ) * (exteriorWedge3 v + exteriorContract3 φ)
      _ = exteriorWedge3 v * exteriorWedge3 v +
          (exteriorContract3 φ * exteriorWedge3 v + exteriorWedge3 v * exteriorContract3 φ) +
          exteriorContract3 φ * exteriorContract3 φ := by noncomm_ring
      _ = 0 + (φ v) • (1 : Exterior3End) + 0 := by rw [h1, h2, h3]
      _ = (φ v) • (1 : Exterior3End) := by simp
  rw [hcar, transportEnd_smul, transportEnd_one]

/-! ## Chiral Blocks on Split Coordinates -/

theorem exteriorGrade3_toLinearMap_sq :
    exteriorGrade3.toLinearMap * exteriorGrade3.toLinearMap = (1 : Exterior3End) := by
  apply LinearMap.ext
  intro x
  exact exteriorGrade3_involutive x

theorem exteriorGrade3_toLinearMap_odd (v : V3) (φ : Module.Dual ℝ V3) :
    exteriorGrade3.toLinearMap * exteriorHodgeDirac3 v φ =
      -(exteriorHodgeDirac3 v φ * exteriorGrade3.toLinearMap) := by
  apply LinearMap.ext
  intro x
  simp only [Module.End.mul_apply, LinearMap.neg_apply]
  exact exteriorHodgeDirac3_odd v φ x

def exteriorProjectorPlus3 : Exterior3End :=
  chiralProjectorPlus exteriorGrade3.toLinearMap

def exteriorProjectorMinus3 : Exterior3End :=
  chiralProjectorMinus exteriorGrade3.toLinearMap

def exteriorChiralDiracPlus3 (v : V3) (φ : Module.Dual ℝ V3) : Exterior3End :=
  chiralDiracPlus exteriorGrade3.toLinearMap (exteriorHodgeDirac3 v φ)

def exteriorChiralDiracMinus3 (v : V3) (φ : Module.Dual ℝ V3) : Exterior3End :=
  chiralDiracMinus exteriorGrade3.toLinearMap (exteriorHodgeDirac3 v φ)

def splitCoordinateProjectorPlus (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) : SplitEnd :=
  transportEnd e exteriorProjectorPlus3

def splitCoordinateProjectorMinus (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) : SplitEnd :=
  transportEnd e exteriorProjectorMinus3

def splitCoordinateChiralDiracPlus
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (v : V3) (φ : Module.Dual ℝ V3) : SplitEnd :=
  transportEnd e (exteriorChiralDiracPlus3 v φ)

def splitCoordinateChiralDiracMinus
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (v : V3) (φ : Module.Dual ℝ V3) : SplitEnd :=
  transportEnd e (exteriorChiralDiracMinus3 v φ)

theorem splitCoordinateProjectorPlus_sq (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) :
    splitCoordinateProjectorPlus e * splitCoordinateProjectorPlus e =
      splitCoordinateProjectorPlus e := by
  dsimp [splitCoordinateProjectorPlus, exteriorProjectorPlus3]
  rw [← transportEnd_mul, chiralProjectorPlus_sq exteriorGrade3_toLinearMap_sq]

theorem splitCoordinateProjectorMinus_sq (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) :
    splitCoordinateProjectorMinus e * splitCoordinateProjectorMinus e =
      splitCoordinateProjectorMinus e := by
  dsimp [splitCoordinateProjectorMinus, exteriorProjectorMinus3]
  rw [← transportEnd_mul, chiralProjectorMinus_sq exteriorGrade3_toLinearMap_sq]

theorem splitCoordinateProjector_ortho (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) :
    splitCoordinateProjectorPlus e * splitCoordinateProjectorMinus e = 0 := by
  dsimp [splitCoordinateProjectorPlus, splitCoordinateProjectorMinus,
         exteriorProjectorPlus3, exteriorProjectorMinus3]
  rw [← transportEnd_mul, chiralProjector_orthogonal_plus_minus exteriorGrade3_toLinearMap_sq]
  apply LinearMap.ext
  intro x
  simp [transportEnd, transportEndGeneric]

theorem splitCoordinateProjector_ortho_reverse
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) :
    splitCoordinateProjectorMinus e * splitCoordinateProjectorPlus e = 0 := by
  dsimp [splitCoordinateProjectorPlus, splitCoordinateProjectorMinus,
    exteriorProjectorPlus3, exteriorProjectorMinus3]
  rw [← transportEnd_mul,
    chiralProjector_orthogonal_minus_plus exteriorGrade3_toLinearMap_sq]
  apply LinearMap.ext
  intro x
  simp [transportEnd, transportEndGeneric]

theorem splitCoordinateProjector_sum
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) :
    splitCoordinateProjectorPlus e + splitCoordinateProjectorMinus e =
      (1 : SplitEnd) := by
  dsimp [splitCoordinateProjectorPlus, splitCoordinateProjectorMinus,
    exteriorProjectorPlus3, exteriorProjectorMinus3]
  rw [← transportEnd_add, chiralProjector_sum]
  exact transportEnd_one e

theorem splitCoordinateChiralDiracPlus_sq_zero
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (v : V3) (φ : Module.Dual ℝ V3) :
    splitCoordinateChiralDiracPlus e v φ * splitCoordinateChiralDiracPlus e v φ = 0 := by
  dsimp [splitCoordinateChiralDiracPlus, exteriorChiralDiracPlus3]
  rw [← transportEnd_mul,
      chiralDiracPlus_sq_zero exteriorGrade3_toLinearMap_sq (exteriorGrade3_toLinearMap_odd v φ)]
  apply LinearMap.ext
  intro x
  simp [transportEnd, transportEndGeneric]

theorem splitCoordinateChiralDiracMinus_sq_zero
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (v : V3) (φ : Module.Dual ℝ V3) :
    splitCoordinateChiralDiracMinus e v φ * splitCoordinateChiralDiracMinus e v φ = 0 := by
  dsimp [splitCoordinateChiralDiracMinus, exteriorChiralDiracMinus3]
  rw [← transportEnd_mul,
      chiralDiracMinus_sq_zero exteriorGrade3_toLinearMap_sq (exteriorGrade3_toLinearMap_odd v φ)]
  apply LinearMap.ext
  intro x
  simp [transportEnd, transportEndGeneric]

theorem splitCoordinateChiralDirac_decomposition
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (v : V3) (φ : Module.Dual ℝ V3) :
    splitCoordinateHodgeDirac3 e v φ =
      splitCoordinateChiralDiracPlus e v φ +
        splitCoordinateChiralDiracMinus e v φ := by
  dsimp [splitCoordinateHodgeDirac3, splitCoordinateChiralDiracPlus,
    splitCoordinateChiralDiracMinus]
  have h := chiralDirac_decomposition exteriorGrade3_toLinearMap_sq
    (exteriorGrade3_toLinearMap_odd v φ)
  simpa only [transportEnd_add] using congrArg (transportEnd e) h

theorem splitCoordinateHodgeLaplacian3_chiral_block_decomposition
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (v : V3) (φ : Module.Dual ℝ V3) :
    splitCoordinateHodgeLaplacian3 e v φ =
      splitCoordinateChiralDiracMinus e v φ *
          splitCoordinateChiralDiracPlus e v φ +
        splitCoordinateChiralDiracPlus e v φ *
          splitCoordinateChiralDiracMinus e v φ := by
  dsimp [splitCoordinateHodgeLaplacian3, splitCoordinateHodgeDirac3,
    splitCoordinateChiralDiracPlus, splitCoordinateChiralDiracMinus]
  have h : exteriorHodgeLaplacian3 v φ =
      exteriorChiralDiracMinus3 v φ * exteriorChiralDiracPlus3 v φ +
        exteriorChiralDiracPlus3 v φ * exteriorChiralDiracMinus3 v φ := by
    calc
      exteriorHodgeLaplacian3 v φ = exteriorHodgeDirac3 v φ * exteriorHodgeDirac3 v φ :=
        (exteriorHodgeDirac3_sq v φ).symm
      _ = _ := dirac_sq_eq_chiral_sum exteriorGrade3_toLinearMap_sq
        (exteriorGrade3_toLinearMap_odd v φ)
  simpa only [transportEnd_add, transportEnd_mul] using congrArg (transportEnd e) h

theorem splitCoordinateChiralDirac_intertwines_plus
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (v : V3) (φ : Module.Dual ℝ V3) :
    splitCoordinateChiralDiracPlus e v φ ∘ₗ e.toLinearMap =
      e.toLinearMap ∘ₗ exteriorChiralDiracPlus3 v φ := by
  dsimp [splitCoordinateChiralDiracPlus]
  exact transportEnd_intertwines e (exteriorChiralDiracPlus3 v φ)

theorem splitCoordinateChiralDirac_intertwines_minus
    (e : Exterior3 ≃ₗ[ℝ] SplitCarrier) (v : V3) (φ : Module.Dual ℝ V3) :
    splitCoordinateChiralDiracMinus e v φ ∘ₗ e.toLinearMap =
      e.toLinearMap ∘ₗ exteriorChiralDiracMinus3 v φ := by
  dsimp [splitCoordinateChiralDiracMinus]
  exact transportEnd_intertwines e (exteriorChiralDiracMinus3 v φ)

end InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport
