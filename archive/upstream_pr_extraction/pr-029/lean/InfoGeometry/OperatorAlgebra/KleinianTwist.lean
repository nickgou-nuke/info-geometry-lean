/-
InfoGeometry/OperatorAlgebra/KleinianTwist.lean

Kleinian/projective Tomita twist.

This module records a witness-gated boundary return:

  observable boundary data return through the Tomita mirror into the commutant.

It does not assert that a bare Clifford algebra has a Klein-bottle topology.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.DrazinRepresentedSplit
import InfoGeometry.OperatorAlgebra.TomitaCartanSplit

noncomputable section

namespace InfoGeometry.OperatorAlgebra.KleinianTwist

open InfoGeometry.OperatorAlgebra.TomitaCartanSplit

/-! ## 1. Projective boundary and Tomita commutant routing -/

/--
A projective/null boundary datum for a Tomita commutant split.

The boundary is allowed to hit a defect locus and to be supported by the
Drazin nil branch.
-/
structure ProjectiveBoundaryDatum
    (Op : Type*) [Ring Op]
    (T : TomitaCommutantDatum Op) where
  /-- Boundary limit/readout. -/
  boundaryLimit : Op → Op

  /-- Defect locus hit by boundary-routed observables. -/
  defect : Set Op

  /-- Observable boundary data hit the defect locus. -/
  boundary_hits_defect :
    ∀ x : Op, x ∈ T.M → boundaryLimit x ∈ defect

  /-- Drazin core/nil projector pair. -/
  projectors : DrazinProjectorPair Op

  /-- Boundary data are supported on the nil branch. -/
  boundary_supported_by_nil :
    ∀ x : Op, x ∈ T.M →
      IsLeftNilSupported projectors (boundaryLimit x)

/--
Kleinian/projective twist datum.

The twist law says that observable boundary return is Tomita mirroring.
-/
structure KleinianTwistDatum
    (Op : Type*) [Ring Op]
    (T : TomitaCommutantDatum Op)
    (B : ProjectiveBoundaryDatum Op T) where
  /-- Boundary return applies the Tomita mirror. -/
  boundary_twist :
    ∀ x : Op, x ∈ T.M → B.boundaryLimit x = T.tomitaMirror x

namespace KleinianTwistDatum

variable
    {Op : Type*} [Ring Op]
    {T : TomitaCommutantDatum Op}
    {B : ProjectiveBoundaryDatum Op T}

variable (K : KleinianTwistDatum Op T B)

/--
Observable boundary data return into the commutant.
-/
theorem observable_boundary_in_commutant
    (K : KleinianTwistDatum Op T B)
    (x : Op)
    (hx : x ∈ T.M) :
    B.boundaryLimit x ∈ T.Mcomm := by
  rcases K with ⟨boundary_twist⟩
  rw [boundary_twist x hx]
  exact T.mirror_M_to_comm x hx

/--
Observable boundary data are nil-supported by the selected Drazin branch.
-/
theorem observable_boundary_nil_supported
    (x : Op)
    (hx : x ∈ T.M) :
    IsLeftNilSupported B.projectors (B.boundaryLimit x) :=
  B.boundary_supported_by_nil x hx

end KleinianTwistDatum

/-! ## 2. Chiral boundary flip branch -/

/--
Chiral Kleinian twist.

This is the branch where the same boundary/Tomita mirror anticommutes with the
Cartan/chiral operator.
-/
structure ChiralKleinianTwistDatum
    (Op : Type*) [Ring Op]
    (T : TomitaCommutantDatum Op)
    (B : ProjectiveBoundaryDatum Op T)
    extends KleinianTwistDatum Op T B where
  /-- Mirror/CPT operator. -/
  J : Op

  /-- Chiral/Cartan operator. -/
  chi : Op

  /-- Boundary return is conjugation by `J` on observable elements. -/
  boundary_eq_J_conj :
    ∀ x : Op, x ∈ T.M → B.boundaryLimit x = (J * x) * J

  /-- Chiral flip relation `Jχ = -χJ`. -/
  J_chi_anticomm :
    J * chi = -(chi * J)

namespace ChiralKleinianTwistDatum

variable
    {Op : Type*} [Ring Op]
    {T : TomitaCommutantDatum Op}
    {B : ProjectiveBoundaryDatum Op T}

variable (K : ChiralKleinianTwistDatum Op T B)

/--
At a chiral Kleinian boundary, left multiplication by the chiral axis flips
through the Tomita mirror.
-/
theorem chiral_left_action_flips_at_boundary
    (x : Op)
    (hx : x ∈ T.M) :
    K.J * (K.chi * x) * K.J =
      -K.chi * (B.boundaryLimit x) := by
  rw [K.boundary_eq_J_conj x hx]
  calc
    K.J * (K.chi * x) * K.J
        = (K.J * K.chi) * x * K.J := by
            noncomm_ring
    _ = (-(K.chi * K.J)) * x * K.J := by
            rw [K.J_chi_anticomm]
    _ = -K.chi * ((K.J * x) * K.J) := by
            noncomm_ring

end ChiralKleinianTwistDatum

end InfoGeometry.OperatorAlgebra.KleinianTwist
