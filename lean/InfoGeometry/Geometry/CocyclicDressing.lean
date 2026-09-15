import InfoGeometry.Geometry.DressingField
import InfoGeometry.Cocycle.ActionCocycle
import Mathlib.Analysis.Complex.Circle

namespace InfoGeometry.Geometry.CocyclicDressing

open DressingField
open InfoGeometry.Canonical.Algebraic

variable {Gauge Configuration Coefficient Value : Type*}
variable [Group Gauge] [MulAction Gauge Configuration] [Group Coefficient]
variable [MulAction Coefficient Value]

def IsCocyclic (cocycle : MulActionCocycle Gauge Configuration Coefficient)
    (field : Configuration → Value) : Prop :=
  ∀ gauge configuration, field (gauge • configuration) =
    cocycle gauge configuration • field configuration

def dressedField (frame : Configuration →[Gauge] Gauge) (field : Configuration → Value) :
    Configuration → Value := field ∘ normalize frame

theorem dressedField_invariant (frame : Configuration →[Gauge] Gauge)
    (field : Configuration → Value) (gauge : Gauge) (configuration : Configuration) :
    dressedField frame field (gauge • configuration) = dressedField frame field configuration := by
  simp [dressedField, normalize_invariant]

theorem dressedField_formula (cocycle : MulActionCocycle Gauge Configuration Coefficient)
    (frame : Configuration →[Gauge] Gauge) (field : Configuration → Value)
    (equivariant : IsCocyclic cocycle field) (configuration : Configuration) :
    dressedField frame field configuration =
      cocycle (frame configuration)⁻¹ configuration • field configuration :=
  equivariant _ _

def frameTransport (cocycle : MulActionCocycle Gauge Configuration Coefficient)
    (first second : Configuration →[Gauge] Gauge) (configuration : Configuration) : Coefficient :=
  cocycle ((second configuration)⁻¹ * first configuration) (normalize first configuration)

theorem normalize_change_frame (first second : Configuration →[Gauge] Gauge)
    (configuration : Configuration) :
    ((second configuration)⁻¹ * first configuration) • normalize first configuration =
      normalize second configuration := by
  simp [DressingField.normalize, mul_smul]

theorem dressedField_change_frame
    (cocycle : MulActionCocycle Gauge Configuration Coefficient)
    (first second : Configuration →[Gauge] Gauge) (field : Configuration → Value)
    (equivariant : IsCocyclic cocycle field) (configuration : Configuration) :
    dressedField second field configuration =
      frameTransport cocycle first second configuration • dressedField first field configuration := by
  simpa only [normalize_change_frame] using
    equivariant ((second configuration)⁻¹ * first configuration) (normalize first configuration)

@[simp] theorem frameTransport_self
    (cocycle : MulActionCocycle Gauge Configuration Coefficient)
    (frame : Configuration →[Gauge] Gauge) (configuration : Configuration) :
    frameTransport cocycle frame frame configuration = 1 := by
  simp only [frameTransport, inv_mul_cancel]
  exact cocycle.map_one _

theorem frameTransport_comp
    (cocycle : MulActionCocycle Gauge Configuration Coefficient)
    (first second third : Configuration →[Gauge] Gauge) (configuration : Configuration) :
    frameTransport cocycle second third configuration *
      frameTransport cocycle first second configuration =
        frameTransport cocycle first third configuration := by
  have chain := cocycle.map_mul ((third configuration)⁻¹ * second configuration)
    ((second configuration)⁻¹ * first configuration) (normalize first configuration)
  simpa [frameTransport, mul_assoc, normalize_change_frame] using chain.symm

theorem frameTransport_invariant
    (cocycle : MulActionCocycle Gauge Configuration Coefficient)
    (first second : Configuration →[Gauge] Gauge) (gauge : Gauge)
    (configuration : Configuration) :
    frameTransport cocycle first second (gauge • configuration) =
      frameTransport cocycle first second configuration := by
  simp [frameTransport, map_smul, mul_assoc, normalize_invariant]

noncomputable def actionPhase (action : Configuration → ℝ) (hbar : ℝ) :
    MulActionCocycle Gauge Configuration Circle :=
  InfoGeometry.Cocycle.MulActionCocycle.coboundary
    (fun configuration => Circle.exp (-action configuration / hbar))

theorem actionPhase_apply (action : Configuration → ℝ) (hbar : ℝ)
    (gauge : Gauge) (configuration : Configuration) :
    actionPhase action hbar gauge configuration =
      Circle.exp (-(action (gauge • configuration) - action configuration) / hbar) := by
  change Circle.exp (-action (gauge • configuration) / hbar) *
    (Circle.exp (-action configuration / hbar))⁻¹ = _
  rw [← Circle.exp_neg, ← Circle.exp_add]
  congr 1
  ring

theorem frameTransport_actionPhase (action : Configuration → ℝ) (hbar : ℝ)
    (first second : Configuration →[Gauge] Gauge) (configuration : Configuration) :
    frameTransport (actionPhase action hbar) first second configuration =
      Circle.exp (-(action (normalize second configuration) -
        action (normalize first configuration)) / hbar) := by
  simp only [frameTransport, actionPhase_apply, normalize_change_frame]

theorem frameTransport_preserves_norm
    (cocycle : MulActionCocycle Gauge Configuration Circle)
    (first second : Configuration →[Gauge] Gauge) (configuration : Configuration)
    (amplitude : ℂ) :
    ‖(frameTransport (Coefficient := Circle) cocycle first second configuration : ℂ) *
      amplitude‖ = ‖amplitude‖ := by
  rw [norm_mul, Circle.norm_coe, one_mul]

end InfoGeometry.Geometry.CocyclicDressing
