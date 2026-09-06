import InfoGeometry.Krein.HestenesKreinVacuumBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

namespace InfoGeometry.Krein.HestenesPhaseVolumeBridge

open InfoGeometry.Krein
open InfoGeometry.Krein.HestenesModularKMSBridge
open InfoGeometry.Krein.HestenesKreinVacuumBridge

section PhaseVolume

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [KreinSpace E]

local notation "EndH" => E →L[ℝ] E

noncomputable local instance instNormedRingEndH : NormedRing EndH := inferInstance
noncomputable local instance instNormedAlgebraRealEndH : NormedAlgebra ℝ EndH := inferInstance
local instance instTopologicalRingEndH : IsTopologicalRing EndH := inferInstance
local instance instCompleteSpaceEndH : CompleteSpace EndH := inferInstance

/--
Hestenes/Krein phase-volume bridge.

This is the theorem-safe replacement for a Type-III determinant/trace formula.
The determinant-like channel is only installed on invertible operators, as a
multiplicative readout `Units EndH →* ℝˣ`.  The trace replacement is supplied as
the vacuum Krein expectation `[XΩ, Ω]_J` through `HestenesKreinVacuum`.

No global trace, Fuglede--Kadison determinant, or analytic operator logarithm is
constructed here.  The logarithm branch and log-det/vacuum-expectation identity
are explicit model data.
-/
@[rep_depth krein]
structure HestenesPhaseVolumeBridge
    (P : HestenesKreinKMSPacket (E := E))
    (V : HestenesKreinVacuum P) where
  /-- Multiplicative determinant/phase-volume channel on invertible operators. -/
  detUnits : Units EndH →* ℝˣ

  /-- Supplied operator logarithm branch. -/
  opLog : EndH → EndH

  /--
  Hestenes/Krein determinant-trace replacement:
  `log det(U) = [log(U) Ω, Ω]_J`.
  -/
  log_det_eq_vacuumExpectation :
    ∀ U : Units EndH,
      Real.log ((detUnits U : ℝˣ) : ℝ) =
        V.vacuumRealState (opLog (U : EndH))

namespace HestenesPhaseVolumeBridge

variable {P : HestenesKreinKMSPacket (E := E)}
variable {V : HestenesKreinVacuum P}
variable (B : HestenesPhaseVolumeBridge P V)

/-- Direct readback of the supplied Hestenes/Krein log-det formula. -/
@[rep_depth krein]
theorem log_det_eq_vacuumExpectation_apply
    (U : Units EndH) :
    Real.log ((B.detUnits U : ℝˣ) : ℝ) =
      V.vacuumRealState (B.opLog (U : EndH)) :=
  B.log_det_eq_vacuumExpectation U

/-- The determinant/phase-volume channel is multiplicative on invertible operators. -/
@[rep_depth krein]
theorem detUnits_mul
    (U W : Units EndH) :
    B.detUnits (U * W) = B.detUnits U * B.detUnits W :=
  map_mul B.detUnits U W

/-- The determinant/phase-volume channel sends the identity unit to one. -/
@[rep_depth krein]
theorem detUnits_one :
    B.detUnits (1 : Units EndH) = 1 :=
  map_one B.detUnits

/--
Logarithmic product law for the multiplicative determinant/phase-volume channel.

The theorem is stated on `Units EndH`, not all operators.
-/
@[rep_depth krein]
theorem log_det_product_eq_sum_log_det
    (U W : Units EndH) :
    Real.log ((B.detUnits (U * W) : ℝˣ) : ℝ) =
      Real.log ((B.detUnits U : ℝˣ) : ℝ) +
        Real.log ((B.detUnits W : ℝˣ) : ℝ) := by
  have hU : ((B.detUnits U : ℝˣ) : ℝ) ≠ 0 := Units.ne_zero _
  have hW : ((B.detUnits W : ℝˣ) : ℝ) ≠ 0 := Units.ne_zero _
  rw [B.detUnits_mul U W]
  simpa using Real.log_mul hU hW

/--
Log-determinant product law read through Hestenes/Krein vacuum expectations.

This is the determinant-trace identity after replacing trace by the supplied
vacuum state.
-/
@[rep_depth krein]
theorem log_det_product_eq_sum_expectation
    (U W : Units EndH) :
    Real.log ((B.detUnits (U * W) : ℝˣ) : ℝ) =
      V.vacuumRealState (B.opLog (U : EndH)) +
        V.vacuumRealState (B.opLog (W : EndH)) := by
  calc
    Real.log ((B.detUnits (U * W) : ℝˣ) : ℝ)
        =
      Real.log ((B.detUnits U : ℝˣ) : ℝ) +
        Real.log ((B.detUnits W : ℝˣ) : ℝ) :=
          B.log_det_product_eq_sum_log_det U W
    _ =
      V.vacuumRealState (B.opLog (U : EndH)) +
        V.vacuumRealState (B.opLog (W : EndH)) := by
          rw [B.log_det_eq_vacuumExpectation_apply U,
            B.log_det_eq_vacuumExpectation_apply W]

/--
Finite additivity of Hestenes/Krein vacuum expectation over a list of atom
operators.
-/
@[rep_depth krein]
theorem vacuumExpectation_list_sum
    (atoms : List EndH) :
    V.vacuumRealState atoms.sum =
      (atoms.map (fun A : EndH => V.vacuumRealState A)).sum := by
  induction atoms with
  | nil =>
      simp [HestenesKreinVacuum.vacuumRealState,
        HestenesKreinKMSPacket.hestenesExpectation]
  | cons A atoms ih =>
      calc
        V.vacuumRealState (A + atoms.sum)
            = V.vacuumRealState A + V.vacuumRealState atoms.sum := by
                unfold HestenesKreinVacuum.vacuumRealState
                unfold HestenesKreinKMSPacket.hestenesExpectation
                simp [ContinuousLinearMap.add_apply, KreinSpace.kreinInner_def, inner_add_left]
        _ = V.vacuumRealState A +
              (atoms.map (fun A : EndH => V.vacuumRealState A)).sum := by
                rw [ih]

/--
If a finite Wigner--Jones/symmetry atom family splits the identity, then its
vacuum expectations sum to the normalized unit volume.
-/
@[rep_depth krein]
theorem wignerJones_atom_sum_invariant
    (atoms : List EndH)
    (h_split : atoms.sum = (1 : EndH)) :
    (atoms.map (fun A : EndH => V.vacuumRealState A)).sum = 1 := by
  calc
    (atoms.map (fun A : EndH => V.vacuumRealState A)).sum
        = V.vacuumRealState atoms.sum := (vacuumExpectation_list_sum (V := V) atoms).symm
    _ = V.vacuumRealState (1 : EndH) := by rw [h_split]
    _ = 1 := V.vacuumRealState_id

end HestenesPhaseVolumeBridge

end PhaseVolume

end InfoGeometry.Krein.HestenesPhaseVolumeBridge
