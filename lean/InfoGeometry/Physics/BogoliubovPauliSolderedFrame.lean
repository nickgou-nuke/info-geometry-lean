import InfoGeometry.Clifford.Soldering
import InfoGeometry.OperatorAlgebra.SpinBogoliubovStinespring

/-!
# Bogoliubov/Pauli Soldered Frame

#### BUCKET 1: CLOSED FINITE THEOREMS

This file merges the previously separate finite corridors:

* the Pauli/tetrad soldering map
  `Vec22 -> Matrix (Fin 2) (Fin 2) R`;
* the Bogoliubov-frame interface with annihilator/creator legs.

The canonical merged finite frame below has one mode carrying both the
Bogoliubov operator coordinate and the Pauli/tetrad soldering coordinate.  Its
readout reconstructs both components at once: the operator from the existing
phase-linear/phase-antilinear Bogoliubov split, and the Pauli/tetrad matrix
from the soldering map.  Its soldering determinant is the split quadratic form.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

None.

#### BUCKET 3: OPEN CLOSURE DEBT

* Curved tetrad-derived spin connection.
* Curved tetrad postulate for arbitrary coframes.
* Global spinor-bundle/tangent-bundle equivalence.
* A nonzero creator leg with full CAR/Fock dynamics identified with curved
  soldering data.
-/

noncomputable section

namespace InfoGeometry.Physics.BogoliubovPauliSolderedFrame

open InfoGeometry.OperatorAlgebra.SpinBogoliubovStinespring

abbrev Vec22 := InfoGeometry.Clifford.Soldering.Vec22

abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ

/-- The Pauli/tetrad soldering map used as the frame selector. -/
abbrev pauliTetradSoldering : Vec22 →ₗ[ℝ] Mat2R :=
  InfoGeometry.Clifford.Soldering.soldering

/--
The merged finite object: a Bogoliubov frame whose annihilator leg is exactly
the Pauli/tetrad soldering map and whose complementary creator leg is zero.
-/
def pauliTetradSolderedBogoliubovFrame :
    BogoliubovFrame Vec22 Mat2R where
  annihilator := fun v => pauliTetradSoldering v
  creator := fun _ => 0

@[simp] theorem pauliTetradSolderedBogoliubovFrame_annihilator
    (v : Vec22) :
    pauliTetradSolderedBogoliubovFrame.annihilator v =
      pauliTetradSoldering v :=
  rfl

@[simp] theorem pauliTetradSolderedBogoliubovFrame_creator
    (v : Vec22) :
    pauliTetradSolderedBogoliubovFrame.creator v = 0 :=
  rfl

/--
The finite merged frame reconstructs the soldered Pauli/tetrad matrix.  This is
the theorem-level merge: the Bogoliubov frame is not a separate lane here; its
visible frame readout is the soldering map itself.
-/
theorem bogoliubov_frame_reconstructs_pauli_tetrad_soldering
    (v : Vec22) :
    pauliTetradSolderedBogoliubovFrame.annihilator v
      + pauliTetradSolderedBogoliubovFrame.creator v =
        pauliTetradSoldering v := by
  simp

/-- The merged Bogoliubov/Pauli frame has the soldering determinant readout. -/
theorem bogoliubov_pauli_tetrad_frame_det_eq_q22
    (v : Vec22) :
    (pauliTetradSolderedBogoliubovFrame.annihilator v).det =
      InfoGeometry.Clifford.Soldering.q22 v := by
  exact InfoGeometry.Clifford.Soldering.det_soldering_eq_q22 v

/--
Trivial spin-frame transport for the finite flat soldered corridor.  The point
of this object is to instantiate the existing spin/Bogoliubov calibration
interface with the soldered Pauli/tetrad frame, instead of leaving the two lanes
unconnected.
-/
def pauliTetradSolderingTransport :
    SpinConnectionTransport PUnit PUnit where
  transport := fun _ _ frame => frame

/--
The finite calibration selecting the merged Pauli/tetrad-soldered Bogoliubov
frame.
-/
def pauliTetradSolderingCalibration :
    SpinFrameBogoliubovCalibration PUnit PUnit Vec22 Mat2R where
  spinTransport := pauliTetradSolderingTransport
  bogoliubovOfFrame := fun _ => pauliTetradSolderedBogoliubovFrame

/--
The existing abstract Bogoliubov-frame selector, when instantiated by the
Pauli/tetrad soldering calibration, returns exactly the merged soldered frame.
-/
theorem bogoliubov_frame_eq_pauli_tetrad_soldered_frame :
    pauliTetradSolderingCalibration.bogoliubovOfFrame PUnit.unit =
      pauliTetradSolderedBogoliubovFrame :=
  rfl

/-- Transport does not move the finite flat soldering frame. -/
theorem pauliTetradSolderingTransport_fixed
    (source target frame : PUnit) :
    pauliTetradSolderingTransport.transport source target frame = frame :=
  rfl

/-! ## One Bogoliubov frame carrying operator and Pauli/tetrad data together -/

section UnifiedOperatorAndSoldering

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" =>
  InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E

/--
The canonical single mode: a Bogoljubov operator coordinate and a Pauli/tetrad
soldering coordinate carried together.
-/
abbrev BogoljubovPauliTetradMode := EndH × Vec22

namespace BogoljubovPauliTetradMode

abbrev operator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (m : BogoljubovPauliTetradMode (E := E)) :
    InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E := m.1
abbrev solder
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (m : BogoljubovPauliTetradMode (E := E)) : Vec22 := m.2

end BogoljubovPauliTetradMode

/-- Backwards English spelling for the same single merged mode. -/
abbrev BogoliubovPauliTetradMode :=
  BogoljubovPauliTetradMode (E := E)

/--
One output type for the canonical merged frame.

The first component is the operator/Fock readout.  The second component is the
Pauli/tetrad soldered matrix readout.
-/
abbrev BogoljubovPauliTetradState :=
  EndH × Mat2R

/--
The canonical merged Bogoljubov/Pauli/tetrad frame.  There is one input mode,
not separate cases: the operator coordinate is reconstructed by the existing
constructive Bogoliubov split, while the soldering coordinate is read out by
the Pauli/tetrad soldering map.
-/
def singleBogoljubovPauliTetradFrame :
    BogoliubovFrame (BogoljubovPauliTetradMode (E := E))
      (BogoljubovPauliTetradState (E := E)) where
  annihilator m :=
    ((canonicalPhaseBogoliubovFrame (E := E)).annihilator
        (BogoljubovPauliTetradMode.operator m),
      pauliTetradSoldering (BogoljubovPauliTetradMode.solder m))
  creator m :=
    ((canonicalPhaseBogoliubovFrame (E := E)).creator
        (BogoljubovPauliTetradMode.operator m), 0)

/-- Backwards English spelling for the canonical single merged frame. -/
abbrev singleBogoliubovPauliTetradFrame :
    BogoliubovFrame (BogoljubovPauliTetradMode (E := E))
      (BogoljubovPauliTetradState (E := E)) :=
  singleBogoljubovPauliTetradFrame (E := E)

/--
The single merged Bogoljubov frame reconstructs the operator and the
Pauli/tetrad soldered matrix in one readout.
-/
theorem singleBogoljubov_pauli_tetrad_reconstruct
    (m : BogoljubovPauliTetradMode (E := E)) :
    (singleBogoljubovPauliTetradFrame (E := E)).annihilator m
      + (singleBogoljubovPauliTetradFrame (E := E)).creator m =
        (BogoljubovPauliTetradMode.operator m,
          pauliTetradSoldering (BogoljubovPauliTetradMode.solder m)) := by
  apply Prod.ext
  · exact canonicalPhaseBogoliubovFrame_reconstruct (E := E)
      (BogoljubovPauliTetradMode.operator m)
  · ext i j
    simp [singleBogoljubovPauliTetradFrame]

/--
The soldering component of the single merged Bogoljubov frame has the
Pauli/tetrad determinant readout.
-/
theorem singleBogoljubov_pauli_tetrad_det_eq_q22
    (m : BogoljubovPauliTetradMode (E := E)) :
    ((singleBogoljubovPauliTetradFrame (E := E)).annihilator m).2.det =
      InfoGeometry.Clifford.Soldering.q22
        (BogoljubovPauliTetradMode.solder m) := by
  exact InfoGeometry.Clifford.Soldering.det_soldering_eq_q22
    (BogoljubovPauliTetradMode.solder m)

/--
Compatibility input type for the merged Bogoliubov frame.

`inl A` is the old operator/Fock mode.  `inr v` is the Pauli/tetrad soldering
mode.  The canonical merged object is `BogoljubovPauliTetradMode`; this sum
form remains as an adapter for code that already chose one component at a time.
-/
abbrev UnifiedBogoliubovMode :=
  Sum EndH Vec22

/--
One output type for the merged Bogoliubov frame.

The first component is the operator/Fock readout.  The second component is the
Pauli/tetrad soldered matrix readout.
-/
abbrev UnifiedBogoliubovState :=
  EndH × Mat2R

/--
The merged Bogoliubov frame.  Operator modes use the existing constructive
phase-linear/phase-antilinear Bogoliubov split.  Pauli/tetrad modes use
soldering as the visible frame leg.
-/
def unifiedBogoliubovPauliTetradFrame :
    BogoliubovFrame (UnifiedBogoliubovMode (E := E)) (UnifiedBogoliubovState (E := E)) where
  annihilator
    | Sum.inl A =>
        ((canonicalPhaseBogoliubovFrame (E := E)).annihilator A, 0)
    | Sum.inr v =>
        (0, pauliTetradSoldering v)
  creator
    | Sum.inl A =>
        ((canonicalPhaseBogoliubovFrame (E := E)).creator A, 0)
    | Sum.inr _ =>
        (0, 0)

/-- Backwards spelling for the user's Bogoljubov terminology. -/
abbrev unifiedBogoljubovPauliTetradFrame :
    BogoliubovFrame (UnifiedBogoliubovMode (E := E)) (UnifiedBogoliubovState (E := E)) :=
  unifiedBogoliubovPauliTetradFrame (E := E)

omit [CompleteSpace E] in
@[simp] theorem unifiedBogoliubov_operator_annihilator
    (A : EndH) :
    (unifiedBogoliubovPauliTetradFrame (E := E)).annihilator (Sum.inl A) =
      ((canonicalPhaseBogoliubovFrame (E := E)).annihilator A, 0) :=
  rfl

omit [CompleteSpace E] in
@[simp] theorem unifiedBogoliubov_operator_creator
    (A : EndH) :
    (unifiedBogoliubovPauliTetradFrame (E := E)).creator (Sum.inl A) =
      ((canonicalPhaseBogoliubovFrame (E := E)).creator A, 0) :=
  rfl

omit [CompleteSpace E] in
@[simp] theorem unifiedBogoliubov_pauli_annihilator
    (v : Vec22) :
    (unifiedBogoliubovPauliTetradFrame (E := E)).annihilator (Sum.inr v) =
      (0, pauliTetradSoldering v) :=
  rfl

omit [CompleteSpace E] in
@[simp] theorem unifiedBogoliubov_pauli_creator
    (v : Vec22) :
    (unifiedBogoliubovPauliTetradFrame (E := E)).creator (Sum.inr v) =
      (0, 0) :=
  rfl

omit [CompleteSpace E] in
/-- The single merged frame reconstructs operator/Fock modes in its first component. -/
theorem unifiedBogoliubov_operator_reconstruct
    (A : EndH) :
    (unifiedBogoliubovPauliTetradFrame (E := E)).annihilator (Sum.inl A)
      + (unifiedBogoliubovPauliTetradFrame (E := E)).creator (Sum.inl A) =
        (A, 0) := by
  apply Prod.ext
  · exact canonicalPhaseBogoliubovFrame_reconstruct (E := E) A
  · ext i j
    simp

omit [CompleteSpace E] in
/-- The same merged frame reconstructs Pauli/tetrad soldering in its second component. -/
theorem unifiedBogoliubov_pauli_tetrad_reconstruct
    (v : Vec22) :
    (unifiedBogoliubovPauliTetradFrame (E := E)).annihilator (Sum.inr v)
      + (unifiedBogoliubovPauliTetradFrame (E := E)).creator (Sum.inr v) =
        (0, pauliTetradSoldering v) := by
  apply Prod.ext
  · apply ContinuousLinearMap.ext
    intro x
    simp
  · ext i j
    simp

omit [CompleteSpace E] in
/--
The one merged Bogoliubov frame has the Pauli/tetrad determinant readout on
Pauli/tetrad modes.
-/
theorem unifiedBogoliubov_pauli_tetrad_det_eq_q22
    (v : Vec22) :
    ((unifiedBogoliubovPauliTetradFrame (E := E)).annihilator (Sum.inr v)).2.det =
      InfoGeometry.Clifford.Soldering.q22 v := by
  exact InfoGeometry.Clifford.Soldering.det_soldering_eq_q22 v

end UnifiedOperatorAndSoldering

end InfoGeometry.Physics.BogoliubovPauliSolderedFrame
