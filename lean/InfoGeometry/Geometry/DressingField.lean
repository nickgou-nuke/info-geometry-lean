import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic

namespace InfoGeometry.Geometry.DressingField

variable {Gauge Configuration Value : Type*} [Group Gauge]
variable [MulAction Gauge Configuration] [MulAction Gauge Value]

def dressed (frame : Configuration →[Gauge] Gauge)
    (field : Configuration →[Gauge] Value) (configuration : Configuration) : Value :=
  (frame configuration)⁻¹ • field configuration

theorem dressed_invariant (frame : Configuration →[Gauge] Gauge)
    (field : Configuration →[Gauge] Value) (gauge : Gauge)
    (configuration : Configuration) :
    dressed frame field (gauge • configuration) = dressed frame field configuration := by
  simp [dressed, map_smul, mul_smul]

def onOrbit (frame : Configuration →[Gauge] Gauge)
    (field : Configuration →[Gauge] Value) :
    Quotient (MulAction.orbitRel Gauge Configuration) → Value :=
  Quotient.lift (dressed frame field) (by
    intro first second related
    obtain ⟨gauge, rfl⟩ := MulAction.mem_orbit_iff.mp related
    exact dressed_invariant frame field gauge second)

@[simp] theorem onOrbit_mk (frame : Configuration →[Gauge] Gauge)
    (field : Configuration →[Gauge] Value) (configuration : Configuration) :
    onOrbit frame field ⟦configuration⟧ = dressed frame field configuration := rfl

theorem onOrbit_unique (frame : Configuration →[Gauge] Gauge)
    (field : Configuration →[Gauge] Value)
    (observable : Quotient (MulAction.orbitRel Gauge Configuration) → Value)
    (agrees : ∀ configuration, observable ⟦configuration⟧ =
      dressed frame field configuration) : observable = onOrbit frame field := by
  funext orbit
  induction orbit using Quotient.inductionOn with
  | h configuration => exact agrees configuration

def transition (first second : Configuration →[Gauge] Gauge)
    (configuration : Configuration) : Gauge :=
  (first configuration)⁻¹ * second configuration

theorem transition_invariant (first second : Configuration →[Gauge] Gauge)
    (gauge : Gauge) (configuration : Configuration) :
    transition first second (gauge • configuration) = transition first second configuration := by
  simp [transition, map_smul, mul_assoc]

@[simp] theorem transition_self (frame : Configuration →[Gauge] Gauge)
    (configuration : Configuration) : transition frame frame configuration = 1 := by
  simp [transition]

theorem transition_cocycle (first second third : Configuration →[Gauge] Gauge)
    (configuration : Configuration) :
    transition first second configuration * transition second third configuration =
      transition first third configuration := by
  simp [transition, mul_assoc]

theorem dressed_change_frame (first second : Configuration →[Gauge] Gauge)
    (field : Configuration →[Gauge] Value) (configuration : Configuration) :
    dressed second field configuration =
      (transition first second configuration)⁻¹ • dressed first field configuration := by
  simp [dressed, transition, mul_smul]

theorem stabilizer_trivial (frame : Configuration →[Gauge] Gauge)
    (gauge : Gauge) (configuration : Configuration)
    (fixed : gauge • configuration = configuration) : gauge = 1 := by
  have equality := frame.map_smul gauge configuration
  rw [fixed] at equality
  change frame configuration = gauge * frame configuration at equality
  exact mul_right_cancel (show gauge * frame configuration = 1 * frame configuration by
    simpa using equality.symm)

theorem no_global_frame_of_stabilizer (gauge : Gauge) (configuration : Configuration)
    (nontrivial : gauge ≠ 1) (fixed : gauge • configuration = configuration) :
    ¬ Nonempty (Configuration →[Gauge] Gauge) := by
  rintro ⟨frame⟩
  exact nontrivial (stabilizer_trivial frame gauge configuration fixed)

def normalize (frame : Configuration →[Gauge] Gauge)
    (configuration : Configuration) : Configuration :=
  (frame configuration)⁻¹ • configuration

theorem normalize_invariant (frame : Configuration →[Gauge] Gauge)
    (gauge : Gauge) (configuration : Configuration) :
    normalize frame (gauge • configuration) = normalize frame configuration := by
  simp [normalize, map_smul, mul_smul]

@[simp] theorem frame_normalize (frame : Configuration →[Gauge] Gauge)
    (configuration : Configuration) : frame (normalize frame configuration) = 1 := by
  simp [normalize, map_smul]

@[simp] theorem normalize_idempotent (frame : Configuration →[Gauge] Gauge)
    (configuration : Configuration) :
    normalize frame (normalize frame configuration) = normalize frame configuration := by
  simp only [normalize, map_smul]
  simp

theorem normalize_eq_iff_orbit (frame : Configuration →[Gauge] Gauge)
    (first second : Configuration) :
    normalize frame first = normalize frame second ↔
      MulAction.orbitRel Gauge Configuration first second := by
  constructor
  · intro equal
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨frame first * (frame second)⁻¹, ?_⟩
    have transported := congrArg (fun value => frame first • value) equal
    simpa [normalize, mul_smul] using transported.symm
  · intro related
    obtain ⟨gauge, rfl⟩ := MulAction.mem_orbit_iff.mp related
    exact normalize_invariant frame gauge second

section ReferenceCoordinates

variable {Point Coordinate Result : Type*}

def relationalField (coordinate : Point ≃ Coordinate) (field : Point → Result) :
    Coordinate → Result := field ∘ coordinate.symm

theorem relationalField_relabel (coordinate : Point ≃ Coordinate)
    (field : Point → Result) (relabel : Point ≃ Point) :
    relationalField (relabel.symm.trans coordinate) (field ∘ relabel.symm) =
      relationalField coordinate field := by
  funext reference
  simp [relationalField]

theorem relationalField_change_reference (first second : Point ≃ Coordinate)
    (field : Point → Result) :
    relationalField second field =
      relationalField first field ∘ (second.symm.trans first) := by
  funext reference
  simp [relationalField]

end ReferenceCoordinates

end InfoGeometry.Geometry.DressingField
