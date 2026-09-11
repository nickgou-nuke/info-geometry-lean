import InfoGeometry.Clifford.Cl55WittQuadraticReflectionPin
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55WittPinParity
import InfoGeometry.Clifford.Cl55WittReflectionGeneratedSubgroup

namespace InfoGeometry.Clifford.Clifford55

open CliffordAlgebra

/-!
# Negative unit vectors in the native Pin group

For the split Witt form, a Clifford vector of quadratic value `-1` is a
native Pin element.  This file records the resulting reflection theorem for
the already defined `pinTwistedOrthogonalAction`; it does not assert the
Cartan--Dieudonné generation theorem.
-/

noncomputable def negativeVectorUnit (v : V55) (hv : Q55 v = -1) : Cl55ˣ :=
  (CliffordAlgebra.isUnit_ι_of_isUnit Q55 (by
    rw [hv]
    exact ⟨-1, by simp⟩)).unit

theorem negativeVectorUnit_coe (v : V55) (hv : Q55 v = -1) :
    (negativeVectorUnit v hv : Cl55) = ι55 v := by
  exact (CliffordAlgebra.isUnit_ι_of_isUnit Q55 (by
    rw [hv]
    exact ⟨-1, by simp⟩)).unit_spec

theorem negativeVector_mem_pinGroup (v : V55) (hv : Q55 v = -1) :
    ι55 v ∈ Pin55 := by
  rw [← negativeVectorUnit_coe v hv]
  apply pinGroup.mem_iff.mpr
  constructor
  · apply Submonoid.mem_map.mpr
    refine ⟨negativeVectorUnit v hv, ?_, rfl⟩
    apply Subgroup.subset_closure
    exact ⟨v, (negativeVectorUnit_coe v hv).symm⟩
  · rw [Unitary.mem_iff]
    constructor
    · rw [negativeVectorUnit_coe, CliffordAlgebra.star_ι, neg_mul,
        CliffordAlgebra.ι_sq_scalar]
      simp [hv]
    · rw [negativeVectorUnit_coe, CliffordAlgebra.star_ι, mul_neg,
        CliffordAlgebra.ι_sq_scalar]
      simp [hv]

noncomputable def negativeVectorPin (v : V55) (hv : Q55 v = -1) : Pin55 :=
  ⟨ι55 v, negativeVector_mem_pinGroup v hv⟩

theorem pinToUnits_negativeVector (v : V55) (hv : Q55 v = -1) :
    pinToUnits (negativeVectorPin v hv) = negativeVectorUnit v hv := by
  apply Units.ext
  exact negativeVectorUnit_coe v hv

theorem negativeVectorPin_twistedAction_eq_quadraticReflection
    (v : V55) (hv : Q55 v = -1) :
    pinTwistedActionEquiv (negativeVectorPin v hv) =
      quadraticReflection v (by simp [hv]) := by
  apply pinTwistedActionEquiv_eq_quadraticReflection
  · rw [pinToUnits_negativeVector]
    exact negativeVectorUnit_coe v hv
  · exact hv

theorem negativeVectorPin_orthogonalAction_eq_quadraticReflectionElement
    (v : V55) (hv : Q55 v = -1) :
    pinTwistedOrthogonalAction (negativeVectorPin v hv) =
      quadraticReflectionElement v (by simp [hv]) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change pinTwistedActionEquiv (negativeVectorPin v hv) x = _
  rw [negativeVectorPin_twistedAction_eq_quadraticReflection]
  rfl

noncomputable def negativeQuadraticReflectionElement
    (v : V55) (hv : Q55 v = -1) : orthogonalGroup55 :=
  quadraticReflectionElement v (by simp [hv])

def negativeQuadraticReflectionSet : Set orthogonalGroup55 :=
  {g | ∃ (v : V55) (hv : Q55 v = -1),
      g = negativeQuadraticReflectionElement v hv}

def negativeQuadraticReflectionSubgroup : Subgroup orthogonalGroup55 :=
  Subgroup.closure negativeQuadraticReflectionSet

theorem negativeQuadraticReflectionElement_mem
    (v : V55) (hv : Q55 v = -1) :
    negativeQuadraticReflectionElement v hv ∈
      negativeQuadraticReflectionSubgroup := by
  apply Subgroup.subset_closure
  exact ⟨v, hv, rfl⟩

theorem negativeQuadraticReflectionSubgroup_le_pinImage :
    negativeQuadraticReflectionSubgroup ≤
      Subgroup.map pinTwistedOrthogonalAction ⊤ := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨negativeVectorPin v hv, trivial, ?_⟩
  exact negativeVectorPin_orthogonalAction_eq_quadraticReflectionElement v hv

end InfoGeometry.Clifford.Clifford55
