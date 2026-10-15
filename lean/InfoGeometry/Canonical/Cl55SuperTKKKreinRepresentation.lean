import InfoGeometry.Canonical.RealCl55FiniteModuleEndBridge
import InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge
import InfoGeometry.Clifford.Cl55SpinBivectorImage
import InfoGeometry.Clifford.Cl55ChiralityProjectors
import InfoGeometry.OperatorAlgebra.SuperTKK
import Mathlib.Algebra.Lie.OfAssociative

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-!
# Concrete Cl(5,5) supercharge operators and the spinor Krein adjoint

This module joins the native finite-spinor supercharge and Krein-adjoint
owners.  It proves the oddness, nilpotence, mixed even momentum relation, and
Krein-adjoint laws for the actual operators on `EuclideanSpace ℝ (Fin 32)`.
The vacuum-ideal equivalence is imported as the algebraic spinor realization.

The result is the concrete supercharge representation layer.  It does not
identify the integer operator-number grading with the independent TKK
five-grading; that requires a concrete TKK Lie carrier and its bracket map.
The reference-coordinate idempotent used below has only a three-step adjoint
action, as recorded by `vacuumIdempotent_adjoint_cubic`.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl55SuperTKKKreinRepresentation

open InfoGeometry.Canonical.RealCl55FiniteModuleEndBridge
open InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge
open InfoGeometry.Clifford.Clifford55

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

theorem nativeSuperchargeQ_krein_adjoint :
    nativeKreinAdjoint nativeSuperchargeQ = -nativeSuperchargeQBar := by
  unfold nativeKreinAdjoint
  rw [nativeSuperchargeQBar_is_hilbert_adjoint]
  have hanti := (nativeMasterChirality_anticomm_supercharge).2
  have hleft : nativeChirality.comp nativeSuperchargeQBar =
      -(nativeSuperchargeQBar.comp nativeChirality) :=
    eq_neg_of_add_eq_zero_left hanti
  calc
    nativeChirality.comp (nativeSuperchargeQBar.comp nativeChirality) =
        (nativeChirality.comp nativeSuperchargeQBar).comp nativeChirality := by
          rw [ContinuousLinearMap.comp_assoc]
    _ = (-(nativeSuperchargeQBar.comp nativeChirality)).comp nativeChirality := by
          rw [hleft]
    _ = -(nativeSuperchargeQBar.comp
          (nativeChirality.comp nativeChirality)) := by
          rw [ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_assoc]
    _ = -nativeSuperchargeQBar := by
          rw [nativeChirality_sq]
          simp

theorem nativeSuperchargeQBar_krein_adjoint :
    nativeKreinAdjoint nativeSuperchargeQBar = -nativeSuperchargeQ := by
  unfold nativeKreinAdjoint
  rw [nativeSuperchargeQ_is_hilbert_adjoint]
  have hanti := (nativeMasterChirality_anticomm_supercharge).1
  have hleft : nativeChirality.comp nativeSuperchargeQ =
      -(nativeSuperchargeQ.comp nativeChirality) :=
    eq_neg_of_add_eq_zero_left hanti
  calc
    nativeChirality.comp (nativeSuperchargeQ.comp nativeChirality) =
        (nativeChirality.comp nativeSuperchargeQ).comp nativeChirality := by
          rw [ContinuousLinearMap.comp_assoc]
    _ = (-(nativeSuperchargeQ.comp nativeChirality)).comp nativeChirality := by
          rw [hleft]
    _ = -(nativeSuperchargeQ.comp
          (nativeChirality.comp nativeChirality)) := by
          rw [ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_assoc]
    _ = -nativeSuperchargeQ := by
          rw [nativeChirality_sq]
          simp

theorem nativeInducedEvenMomentum_krein_self_adjoint :
    nativeKreinAdjoint nativeInducedEvenMomentum =
      nativeInducedEvenMomentum := by
  unfold nativeKreinAdjoint
  rw [nativeInducedEvenMomentum_is_hilbert_self_adjoint]
  have hcomm := nativeMasterChirality_commutes_inducedEvenMomentum
  calc
    nativeChirality.comp
        (nativeInducedEvenMomentum.comp nativeChirality) =
        (nativeChirality.comp nativeInducedEvenMomentum).comp
          nativeChirality := by rw [ContinuousLinearMap.comp_assoc]
    _ = (nativeInducedEvenMomentum.comp nativeChirality).comp
          nativeChirality := by rw [hcomm]
    _ = nativeInducedEvenMomentum := by
          rw [ContinuousLinearMap.comp_assoc, nativeChirality_sq]
          simp

/-- The represented chiral charges are odd for the Cl(5,5) fundamental
symmetry, square to zero, and close to the even momentum operator. -/
theorem native_supercharge_representation_relations :
    nativeChirality.comp nativeSuperchargeQ +
        nativeSuperchargeQ.comp nativeChirality = 0 ∧
    nativeChirality.comp nativeSuperchargeQBar +
        nativeSuperchargeQBar.comp nativeChirality = 0 ∧
    nativeSuperchargeQ.comp nativeSuperchargeQ = 0 ∧
    nativeSuperchargeQBar.comp nativeSuperchargeQBar = 0 ∧
    nativeSuperchargeQ.comp nativeSuperchargeQBar +
        nativeSuperchargeQBar.comp nativeSuperchargeQ =
      (2 : ℝ) • nativeInducedEvenMomentum := by
  exact ⟨(nativeMasterChirality_anticomm_supercharge).1,
    (nativeMasterChirality_anticomm_supercharge).2,
    nativeSuperchargeQ_sq_zero, nativeSuperchargeQBar_sq_zero,
    nativeSupercharge_anticommutator_eq_two_momentum⟩

/-- The Krein adjoint turns the two chiral Hilbert-adjoint charges into the
opposite charge with the sign dictated by odd parity. -/
theorem native_supercharge_krein_adjoint_relations :
    nativeKreinAdjoint nativeSuperchargeQ = -nativeSuperchargeQBar ∧
    nativeKreinAdjoint nativeSuperchargeQBar = -nativeSuperchargeQ ∧
    nativeKreinAdjoint nativeInducedEvenMomentum =
      nativeInducedEvenMomentum :=
  ⟨nativeSuperchargeQ_krein_adjoint,
    nativeSuperchargeQBar_krein_adjoint,
    nativeInducedEvenMomentum_krein_self_adjoint⟩

/-- Left multiplication of Cl(5,5) on its vacuum principal ideal. -/
def cl55VacuumIdealAction (a : Cl55) :
    Module.End ℝ cl55VacuumIdeal where
  toFun x := ⟨a * x.1, by
    change (a * x.1) * cl55VacuumIdempotent = a * x.1
    rw [mul_assoc, x.2]
  ⟩
  map_add' x y := by
    apply Subtype.ext
    simp [mul_add]
  map_smul' c x := by
    apply Subtype.ext
    simp

/-- The induced commutator action is a genuine Lie representation of the
Cl(5,5) commutator Lie algebra on the 32-dimensional vacuum ideal. -/
def cl55VacuumIdealLieRepresentation :
    Cl55 →ₗ⁅ℝ⁆ Module.End ℝ cl55VacuumIdeal where
  toFun := cl55VacuumIdealAction
  map_add' := by
    intro a b
    ext x
    change (a + b) * x.1 = a * x.1 + b * x.1
    rw [add_mul]
  map_smul' := by
    intro c a
    ext x
    change (c • a) * x.1 = c • (a * x.1)
    exact smul_mul_assoc c a x.1
  map_lie' := by
    intro a b
    ext x
    change ⁅a, b⁆ * x.1 = a * (b * x.1) - b * (a * x.1)
    rw [Ring.lie_def]
    noncomm_ring

/-- Restriction of the vacuum-ideal action to the native Cl(5,5) spin-bivector
Lie algebra. -/
def spinBivectorVacuumIdealRepresentation :
    InfoGeometry.Clifford.Cl55SpinBivectorImage.SpinBivector55 →ₗ⁅ℝ⁆
      Module.End ℝ cl55VacuumIdeal where
  toFun X := cl55VacuumIdealAction (X : Cl55)
  map_add' X Y := by
    ext x
    change ((X : Cl55) + (Y : Cl55)) * x.1 =
      (X : Cl55) * x.1 + (Y : Cl55) * x.1
    rw [add_mul]
  map_smul' c X := by
    ext x
    change (c • (X : Cl55)) * x.1 = c • ((X : Cl55) * x.1)
    exact smul_mul_assoc c (X : Cl55) x.1
  map_lie' := by
    intro X Y
    change cl55VacuumIdealAction ⁅(X : Cl55), (Y : Cl55)⁆ =
      ⁅cl55VacuumIdealAction (X : Cl55),
        cl55VacuumIdealAction (Y : Cl55)⁆
    exact cl55VacuumIdealLieRepresentation.map_lie (X : Cl55) (Y : Cl55)

theorem spinBivectorVacuumIdealRepresentation_apply
    (X : InfoGeometry.Clifford.Cl55SpinBivectorImage.SpinBivector55) :
    spinBivectorVacuumIdealRepresentation X =
      cl55VacuumIdealAction (X : Cl55) := by
  rfl

theorem spinBivectorVacuumIdealRepresentation_lie
    (X Y : InfoGeometry.Clifford.Cl55SpinBivectorImage.SpinBivector55) :
    spinBivectorVacuumIdealRepresentation ⁅X, Y⁆ =
      ⁅spinBivectorVacuumIdealRepresentation X,
        spinBivectorVacuumIdealRepresentation Y⁆ := by
  exact spinBivectorVacuumIdealRepresentation.map_lie X Y

/-! ### Transport of the five-step TKK adjoint identity

The TKK owner states its tripotent relation on an associative algebra.  The
vacuum ideal action above is a Lie representation of that algebra's
commutator Lie ring, so the same polynomial identity holds for the represented
operators.  This is the representation-level bridge; it does not identify the
Clifford operator-number grading with the TKK eigenspace decomposition. -/

/-- The adjoint action of a tripotent on the represented vacuum module obeys
the five-step polynomial from the TKK owner. -/
theorem vacuumIdeal_representation_superTKK_polynomial
    (sys : InfoGeometry.OperatorAlgebra.TKK.SuperTKKStructure Cl55)
    (X : Cl55) :
    let adP (T : Module.End ℝ cl55VacuumIdeal) :=
      ⁅cl55VacuumIdealLieRepresentation sys.P, T⁆
    adP (adP (adP (adP (adP (cl55VacuumIdealLieRepresentation X))))) -
      5 • adP (adP (adP (cl55VacuumIdealLieRepresentation X))) +
      4 • adP (cl55VacuumIdealLieRepresentation X) = 0 := by
  let adP (Y : Cl55) := sys.P * Y - Y * sys.P
  let adRep (Y : Module.End ℝ cl55VacuumIdeal) :=
    ⁅cl55VacuumIdealLieRepresentation sys.P, Y⁆
  have hpoly := InfoGeometry.OperatorAlgebra.TKK.super_tkk_5_grading sys X
  change adRep (adRep (adRep (adRep (adRep
      (cl55VacuumIdealLieRepresentation X))))) -
    5 • adRep (adRep (adRep (cl55VacuumIdealLieRepresentation X))) +
    4 • adRep (cl55VacuumIdealLieRepresentation X) = 0
  have hpoly' : adP (adP (adP (adP (adP X)))) -
      5 • adP (adP (adP X)) + 4 • adP X = 0 := by
    simpa [adP] using hpoly
  have hmap : ∀ Y : Cl55,
      cl55VacuumIdealLieRepresentation (adP Y) =
        adRep (cl55VacuumIdealLieRepresentation Y) := by
    intro Y
    change cl55VacuumIdealLieRepresentation ⁅sys.P, Y⁆ =
      ⁅cl55VacuumIdealLieRepresentation sys.P,
        cl55VacuumIdealLieRepresentation Y⁆
    exact cl55VacuumIdealLieRepresentation.map_lie sys.P Y
  have h5 : cl55VacuumIdealLieRepresentation (adP (adP (adP (adP (adP X))))) =
      adRep (adRep (adRep (adRep (adRep
        (cl55VacuumIdealLieRepresentation X))))) := by
    rw [hmap, hmap, hmap, hmap, hmap]
  have h3 : cl55VacuumIdealLieRepresentation (adP (adP (adP X))) =
      adRep (adRep (adRep (cl55VacuumIdealLieRepresentation X))) := by
    rw [hmap, hmap, hmap]
  have h1 : cl55VacuumIdealLieRepresentation (adP X) =
      adRep (cl55VacuumIdealLieRepresentation X) := hmap X
  have h := congrArg cl55VacuumIdealLieRepresentation hpoly'
  simp only [map_sub, map_add, map_zero, map_nsmul] at h
  rw [h5, h3, h1] at h
  exact h

/-! ### The reference-coordinate idempotent

This idempotent supplies the TKK owner's tripotent polynomial, and the ideal
Lie representation transports that polynomial.  Its cubic adjoint identity
below shows that it does not by itself construct the five graded pieces. -/

/-- The vacuum projector, regarded as a tripotent for the TKK adjoint law. -/
def vacuumIdempotentSuperTKK :
    InfoGeometry.OperatorAlgebra.TKK.SuperTKKStructure Cl55 where
  P := cl55VacuumIdempotent
  tripotent_P := by
      rw [pow_succ, pow_two, cl55VacuumIdempotent_idempotent,
      cl55VacuumIdempotent_idempotent]

/-- The reference idempotent tripotent has the stronger cubic adjoint
identity `ad(P)^3 = ad(P)`.  Its five-step polynomial therefore does not
provide the nonzero weight `±2` spaces of a genuine five-grading. -/
theorem vacuumIdempotent_adjoint_cubic (X : Cl55) :
    let adP (Y : Cl55) :=
      cl55VacuumIdempotent * Y - Y * cl55VacuumIdempotent
    adP (adP (adP X)) = adP X := by
  intro adP
  have h2 : cl55VacuumIdempotent ^ 2 = cl55VacuumIdempotent := by
    simpa [pow_two] using cl55VacuumIdempotent_idempotent
  have h3 : cl55VacuumIdempotent ^ 3 = cl55VacuumIdempotent := by
    calc
      cl55VacuumIdempotent ^ 3 =
          cl55VacuumIdempotent ^ 2 * cl55VacuumIdempotent := by
        rw [pow_succ]
      _ = cl55VacuumIdempotent * cl55VacuumIdempotent := by rw [h2]
      _ = cl55VacuumIdempotent := cl55VacuumIdempotent_idempotent
  have hformula : adP (adP (adP X)) =
      cl55VacuumIdempotent ^ 3 * X -
        3 • (cl55VacuumIdempotent ^ 2 * X * cl55VacuumIdempotent) +
        3 • (cl55VacuumIdempotent * X * cl55VacuumIdempotent ^ 2) -
        X * cl55VacuumIdempotent ^ 3 := by
    dsimp [adP]
    noncomm_ring
  rw [hformula, h3, h2]
  dsimp [adP]
  noncomm_ring

/-- The represented vacuum tripotent obeys the TKK five-step adjoint
polynomial on the vacuum ideal. -/
theorem vacuumIdempotent_representation_superTKK_polynomial (X : Cl55) :
    let adP (T : Module.End ℝ cl55VacuumIdeal) :=
      ⁅cl55VacuumIdealLieRepresentation cl55VacuumIdempotent, T⁆
    adP (adP (adP (adP (adP (cl55VacuumIdealLieRepresentation X))))) -
      5 • adP (adP (adP (cl55VacuumIdealLieRepresentation X))) +
      4 • adP (cl55VacuumIdealLieRepresentation X) = 0 := by
  simpa [vacuumIdempotentSuperTKK] using
    vacuumIdeal_representation_superTKK_polynomial
      vacuumIdempotentSuperTKK X

/-! ### The stronger represented identity for the reference idempotent

The abstract tripotent polynomial transports to the ideal representation, but
this particular tripotent is idempotent. Its represented adjoint therefore
satisfies the stronger cubic identity below. -/

/-- The represented reference idempotent has adjoint action satisfying
`ad(P)^3 = ad(P)` on the image of the Cl(5,5) action. -/
theorem vacuumIdempotent_representation_adjoint_cubic (X : Cl55) :
    let adP (T : Module.End ℝ cl55VacuumIdeal) :=
      ⁅cl55VacuumIdealLieRepresentation cl55VacuumIdempotent, T⁆
    adP (adP (adP (cl55VacuumIdealLieRepresentation X))) =
      adP (cl55VacuumIdealLieRepresentation X) := by
  let adP (Y : Cl55) := cl55VacuumIdempotent * Y - Y * cl55VacuumIdempotent
  let adRep (Y : Module.End ℝ cl55VacuumIdeal) :=
    ⁅cl55VacuumIdealLieRepresentation cl55VacuumIdempotent, Y⁆
  have hmap (Y : Cl55) :
      cl55VacuumIdealLieRepresentation (adP Y) =
        adRep (cl55VacuumIdealLieRepresentation Y) := by
    change cl55VacuumIdealLieRepresentation ⁅cl55VacuumIdempotent, Y⁆ =
      ⁅cl55VacuumIdealLieRepresentation cl55VacuumIdempotent,
        cl55VacuumIdealLieRepresentation Y⁆
    exact cl55VacuumIdealLieRepresentation.map_lie _ _
  have hmap3 (Y : Cl55) :
      cl55VacuumIdealLieRepresentation (adP (adP (adP Y))) =
        adRep (adRep (adRep (cl55VacuumIdealLieRepresentation Y))) := by
    rw [hmap, hmap, hmap]
  have hsource := vacuumIdempotent_adjoint_cubic X
  have h := congrArg cl55VacuumIdealLieRepresentation hsource
  change cl55VacuumIdealLieRepresentation (adP (adP (adP X))) =
    cl55VacuumIdealLieRepresentation (adP X) at h
  rw [hmap3, hmap] at h
  change adRep (adRep (adRep (cl55VacuumIdealLieRepresentation X))) =
    adRep (cl55VacuumIdealLieRepresentation X)
  exact h

/-- Every nonzero eigenvector in the represented Cl(5,5) image has adjoint
weight `-1`, `0`, or `1`. Thus the reference idempotent cannot produce the
extremal weights `±2` of a nontrivial five-grade action. -/
theorem vacuumIdempotent_representation_eigenvalue
    (X : Cl55) {r : ℝ}
    (hX : ⁅cl55VacuumIdealLieRepresentation cl55VacuumIdempotent,
        cl55VacuumIdealLieRepresentation X⁆ =
      r • cl55VacuumIdealLieRepresentation X)
    (hXne : cl55VacuumIdealLieRepresentation X ≠ 0) :
    r = -1 ∨ r = 0 ∨ r = 1 := by
  let v := cl55VacuumIdealLieRepresentation X
  let adRep (T : Module.End ℝ cl55VacuumIdeal) :=
    ⁅cl55VacuumIdealLieRepresentation cl55VacuumIdempotent, T⁆
  have had_smul (r : ℝ) (T : Module.End ℝ cl55VacuumIdeal) :
      adRep (r • T) = r • adRep T := by
    change (cl55VacuumIdealLieRepresentation cl55VacuumIdempotent) *
          (r • T) - (r • T) *
            cl55VacuumIdealLieRepresentation cl55VacuumIdempotent =
      r • ((cl55VacuumIdealLieRepresentation cl55VacuumIdempotent) * T -
        T * cl55VacuumIdealLieRepresentation cl55VacuumIdempotent)
    rw [mul_smul_comm, smul_mul_assoc]
    module
  have hX' : adRep v = r • v := hX
  have h2 : adRep (adRep v) = (r ^ 2) • v := by
    calc
      adRep (adRep v) = adRep (r • v) := by rw [hX']
      _ = r • adRep v := had_smul r v
      _ = r • (r • v) := by rw [hX']
      _ = (r ^ 2) • v := by
        rw [smul_smul]
        exact congrArg (fun c : ℝ => c • v) (by ring)
  have h3 : adRep (adRep (adRep v)) = (r ^ 3) • v := by
    calc
      adRep (adRep (adRep v)) = adRep ((r ^ 2) • v) := by rw [h2]
      _ = (r ^ 2) • adRep v := had_smul (r ^ 2) v
      _ = (r ^ 2) • (r • v) := by rw [hX']
      _ = (r ^ 3) • v := by
        rw [smul_smul]
        exact congrArg (fun c : ℝ => c • v) (by ring)
  have hcubic := vacuumIdempotent_representation_adjoint_cubic X
  change adRep (adRep (adRep v)) = adRep v at hcubic
  have hcoeff : (r ^ 3) • v = r • v := by
    calc
      (r ^ 3) • v = adRep (adRep (adRep v)) := h3.symm
      _ = adRep v := hcubic
      _ = r • v := hX'
  have hzero : (r ^ 3 - r) • v = 0 := by
    calc
      (r ^ 3 - r) • v = (r ^ 3) • v - r • v := by module
      _ = 0 := sub_eq_zero.mpr hcoeff
  have hroot : r ^ 3 - r = 0 := by
    rcases smul_eq_zero.mp hzero with h | h
    · exact h
    · exact (hXne h).elim
  have hfactor : r * (r - 1) * (r + 1) = 0 := by
    calc
      r * (r - 1) * (r + 1) = r ^ 3 - r := by ring
      _ = 0 := hroot
  rcases mul_eq_zero.mp hfactor with hleft | hadd
  · rcases mul_eq_zero.mp hleft with hzero | hminus
    · exact Or.inr (Or.inl hzero)
    · exact Or.inr (Or.inr (by linarith))
  · exact Or.inl (by linarith)

/-! ### Five-grade boundary

The reference idempotent above only supplies a three-weight adjoint action.
The volume element is not used as a substitute for the requested concrete TKK
five-grade action. A TKK graded Lie carrier and its action on this ideal remain
to be constructed. -/

end InfoGeometry.Canonical.Cl55SuperTKKKreinRepresentation

end
