import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import InfoGeometry.Physics.RealSpinorLorentzRepresentation

/-!
# Doubled real chiral Lorentz carrier

The real carrier is the product of two copies of the canonical complex
two-spinor.  Lorentz transformations act diagonally; the two copies are the
explicit chiral sheets.  The real complex structure supplies the internal
phase operator.
-/

noncomputable section

namespace InfoGeometry.Physics.RealChiralLorentzRepresentation

open InfoGeometry.Physics.LorentzChiralCuntzBridge
open InfoGeometry.Physics.RealSpinorLorentzRepresentation

abbrev ChiralCarrier := Spinor × Spinor
abbrev ChiralEnd := Module.End ℝ ChiralCarrier
abbrev ChiralUnits := LinearMap.GeneralLinearGroup ℝ ChiralCarrier

def diagonalRepresentation : SL2C →* ChiralUnits where
  toFun g :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv
      ((realSpinorRepresentation g).toLinearEquiv.prodCongr
        (realSpinorRepresentation g).toLinearEquiv)
  map_one' := by
    ext v <;> simp
  map_mul' := by
    intro g h
    ext v <;> simp [mul_assoc]

@[simp] theorem diagonalRepresentation_apply (g : SL2C) (v : ChiralCarrier) :
    (diagonalRepresentation g : ChiralCarrier → ChiralCarrier) v =
      ((realSpinorRepresentation g : Spinor → Spinor) v.1,
        (realSpinorRepresentation g : Spinor → Spinor) v.2) := by
  rfl

def chirality : ChiralEnd where
  toFun v := (v.1, -v.2)
  map_add' := by intro v w; ext <;> simp <;> abel
  map_smul' := by intro r v; ext <;> simp

def internalPhase : ChiralEnd where
  toFun v := (Complex.I • v.1, Complex.I • v.2)
  map_add' := by intro v w; ext <;> simp [add_smul] <;> ring
  map_smul' := by
    intro r v
    ext <;> simp [Algebra.smul_def, Pi.smul_apply, smul_smul] <;> ring

@[simp] theorem chirality_apply (v : ChiralCarrier) :
    chirality v = (v.1, -v.2) := rfl

@[simp] theorem internalPhase_apply (v : ChiralCarrier) :
    internalPhase v = (Complex.I • v.1, Complex.I • v.2) := rfl

theorem chirality_sq : chirality.comp chirality = LinearMap.id := by
  ext v <;> simp [chirality, LinearMap.comp_apply]

theorem internalPhase_sq : internalPhase.comp internalPhase = -LinearMap.id := by
  ext v <;> simp [internalPhase, LinearMap.comp_apply, smul_smul,
    Complex.I_mul_I]

theorem diagonalRepresentation_commutes_internalPhase (g : SL2C) :
    (diagonalRepresentation g : ChiralEnd).comp internalPhase =
      internalPhase.comp (diagonalRepresentation g : ChiralEnd) := by
  apply LinearMap.ext
  intro v
  apply Prod.ext
  · change (Matrix.SpecialLinearGroup.toLin' g) (Complex.I • v.1) =
      Complex.I • (Matrix.SpecialLinearGroup.toLin' g) v.1
    exact (Matrix.SpecialLinearGroup.toLin' g).map_smul Complex.I v.1
  · change (Matrix.SpecialLinearGroup.toLin' g) (Complex.I • v.2) =
      Complex.I • (Matrix.SpecialLinearGroup.toLin' g) v.2
    exact (Matrix.SpecialLinearGroup.toLin' g).map_smul Complex.I v.2

theorem diagonalRepresentation_commutes_chirality (g : SL2C) :
    (diagonalRepresentation g : ChiralEnd).comp chirality =
      chirality.comp (diagonalRepresentation g : ChiralEnd) := by
  ext v <;> simp [diagonalRepresentation, chirality, LinearMap.comp_apply]

theorem internalPhase_commutes_chirality :
    internalPhase.comp chirality = chirality.comp internalPhase := by
  ext v <;> simp [internalPhase, chirality, LinearMap.comp_apply]

def leftChiralProjector : ChiralEnd :=
  (1 / 2 : ℝ) • (LinearMap.id + chirality)

def rightChiralProjector : ChiralEnd :=
  (1 / 2 : ℝ) • (LinearMap.id - chirality)

@[simp] theorem leftChiralProjector_apply (v : ChiralCarrier) :
    leftChiralProjector v = (v.1, 0) := by
  ext <;> simp [leftChiralProjector, chirality] <;> ring

@[simp] theorem rightChiralProjector_apply (v : ChiralCarrier) :
    rightChiralProjector v = (0, v.2) := by
  ext <;> simp [rightChiralProjector, chirality] <;> ring

theorem leftChiralProjector_idempotent :
    leftChiralProjector.comp leftChiralProjector = leftChiralProjector := by
  ext v <;> simp [leftChiralProjector, chirality, LinearMap.comp_apply] <;> ring

theorem rightChiralProjector_idempotent :
    rightChiralProjector.comp rightChiralProjector = rightChiralProjector := by
  ext v <;> simp [rightChiralProjector, chirality, LinearMap.comp_apply] <;> ring

theorem leftChiralProjector_comp_rightChiralProjector :
    leftChiralProjector.comp rightChiralProjector = 0 := by
  ext v <;> simp [leftChiralProjector, rightChiralProjector, chirality,
    LinearMap.comp_apply] <;> ring

theorem rightChiralProjector_comp_leftChiralProjector :
    rightChiralProjector.comp leftChiralProjector = 0 := by
  ext v <;> simp [leftChiralProjector, rightChiralProjector, chirality,
    LinearMap.comp_apply] <;> ring

theorem leftChiralProjector_add_rightChiralProjector :
    leftChiralProjector + rightChiralProjector = LinearMap.id := by
  ext v <;> simp [leftChiralProjector, rightChiralProjector, chirality] <;> ring

theorem diagonalRepresentation_commutes_leftChiralProjector (g : SL2C) :
    (diagonalRepresentation g : ChiralEnd).comp leftChiralProjector =
      leftChiralProjector.comp (diagonalRepresentation g : ChiralEnd) := by
  apply LinearMap.ext
  intro v
  have h := congrArg (fun f : ChiralEnd => f v)
    (diagonalRepresentation_commutes_chirality g)
  simp only [LinearMap.comp_apply] at h
  change (diagonalRepresentation g : ChiralEnd)
      ((1 / 2 : ℝ) • (v + chirality v)) =
    (1 / 2 : ℝ) •
      ((diagonalRepresentation g : ChiralEnd) v + chirality
        ((diagonalRepresentation g : ChiralEnd) v))
  rw [map_smul, map_add, h]

theorem diagonalRepresentation_commutes_rightChiralProjector (g : SL2C) :
    (diagonalRepresentation g : ChiralEnd).comp rightChiralProjector =
      rightChiralProjector.comp (diagonalRepresentation g : ChiralEnd) := by
  apply LinearMap.ext
  intro v
  have h := congrArg (fun f : ChiralEnd => f v)
    (diagonalRepresentation_commutes_chirality g)
  simp only [LinearMap.comp_apply] at h
  change (diagonalRepresentation g : ChiralEnd)
      ((1 / 2 : ℝ) • (v - chirality v)) =
    (1 / 2 : ℝ) •
      ((diagonalRepresentation g : ChiralEnd) v - chirality
        ((diagonalRepresentation g : ChiralEnd) v))
  rw [map_smul, map_sub, h]

theorem internalPhase_commutes_leftChiralProjector :
    internalPhase.comp leftChiralProjector =
      leftChiralProjector.comp internalPhase := by
  apply LinearMap.ext
  intro v
  have h := congrArg (fun f : ChiralEnd => f v)
    internalPhase_commutes_chirality
  simp only [LinearMap.comp_apply] at h
  change internalPhase ((1 / 2 : ℝ) • (v + chirality v)) =
    (1 / 2 : ℝ) • (internalPhase v + chirality (internalPhase v))
  rw [map_smul, map_add, h]

theorem internalPhase_commutes_rightChiralProjector :
    internalPhase.comp rightChiralProjector =
      rightChiralProjector.comp internalPhase := by
  apply LinearMap.ext
  intro v
  have h := congrArg (fun f : ChiralEnd => f v)
    internalPhase_commutes_chirality
  simp only [LinearMap.comp_apply] at h
  change internalPhase ((1 / 2 : ℝ) • (v - chirality v)) =
    (1 / 2 : ℝ) • (internalPhase v - chirality (internalPhase v))
  rw [map_smul, map_sub, h]

end InfoGeometry.Physics.RealChiralLorentzRepresentation
