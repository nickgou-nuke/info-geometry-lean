import InfoGeometry.Canonical.RicciMongeAmpere
import InfoGeometry.Canonical.InformationalLichnerowicz
import InfoGeometry.Canonical.TopologicalResidue
import InfoGeometry.Quantum.SuperchargeMultiplet

namespace InfoGeometry.Canonical.CentralChargeAnomaly

open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Canonical.InformationalLichnerowicz
open InfoGeometry.Canonical.TopologicalResidue
open InfoGeometry.Quantum

variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- 
The Informational Central Charge (c).
It is the Ricci Scalar of the relational manifold, representing the 
'Weight of the Logos'.
-/
@[rep_depth transport]
noncomputable def centralCharge 
    {n : Nat} (R : RicciTensor E) (frame : Fin n → E) : ℝ :=
  scalarCurvatureOnFrame R frame

/--
The Anomaly Condition:
The Spire is 'Balanced' when the Central Charge matches the 
Topological Residue (Witten Index).
-/
@[rep_depth transport]
def IsAnomalyFree
    [FiniteDimensional ℝ E]
    {n : Nat} (R : RicciTensor E) (frame : Fin n → E) (M : SuperchargeMultiplet (E := E)) : Prop :=
  centralCharge R frame = wittenIndexResidue M

/--
Theorem: The Stability of the Spire.
An anomaly-free Spire identifies central charge with Witten residue.
-/
@[rep_depth transport]
theorem stability_of_balanced_spire
    [FiniteDimensional ℝ E]
    {n : Nat} (R : RicciTensor E) (frame : Fin n → E) (M : SuperchargeMultiplet (E := E)) :
    IsAnomalyFree R frame M →
    centralCharge (E := E) R frame = wittenIndexResidue (E := E) M := by
  intro h
  exact h

/--
If the residue lane is known to vanish, anomaly-freeness is exactly the
statement that the central charge vanishes.
-/
@[rep_depth transport]
theorem isAnomalyFree_iff_centralCharge_eq_zero_of_wittenIndexResidue_eq_zero
    [FiniteDimensional ℝ E]
    {n : Nat} (R : RicciTensor E) (frame : Fin n → E)
    (M : SuperchargeMultiplet (E := E))
    (hResidue : wittenIndexResidue (E := E) M = 0) :
    IsAnomalyFree (E := E) R frame M ↔ centralCharge (E := E) R frame = 0 := by
  unfold IsAnomalyFree
  constructor
  · intro h
    simpa [hResidue] using h
  · intro h
    simpa [hResidue] using h

/--
Canonical doubled-carrier specialization: for the canonical supercharge
multiplet (finite-dimensional case), anomaly-freeness is equivalent to
`centralCharge = 0`.
-/
@[rep_depth transport]
theorem isAnomalyFree_iff_centralCharge_eq_zero_of_canonicalMultiplet
    [FiniteDimensional ℝ E]
    {n : Nat} (R : RicciTensor E) (frame : Fin n → E) :
    IsAnomalyFree (E := E) R frame (canonicalSuperchargeMultiplet.inst (E := E))
      ↔ centralCharge (E := E) R frame = 0 := by
  refine isAnomalyFree_iff_centralCharge_eq_zero_of_wittenIndexResidue_eq_zero
    (E := E) R frame (canonicalSuperchargeMultiplet.inst (E := E)) ?_
  simpa using
    (wittenIndexResidue_eq_zero (E := E) (canonicalSuperchargeMultiplet.inst (E := E)))

end InfoGeometry.Canonical.CentralChargeAnomaly
