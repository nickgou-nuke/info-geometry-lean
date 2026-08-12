import InfoGeometry.Clifford.Cl55WittNativeIsometryGroup
import InfoGeometry.Twistor.ProjectiveNullIsometryIncidence

/-!
# The real split-Pin action on native `Q55` null incidence

The concrete twisted split-Pin action on `V55` is already exposed as the
native Mathlib quadratic-isometry homomorphism
`realSplitPinNativeOrthogonalAction`.  This owner projectivizes that existing
action and restricts it to the `Q55` null boundary.

The resulting permutation action preserves the native polar-incidence
relation exactly.  This is a concrete split-Pin/projective-null bridge; it
does not identify the null boundary with a particular conformal compactification
or introduce a spinorial twistor representation.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Twistor.Cl55RealSplitPinNullIncidence

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor
open InfoGeometry.Twistor.ProjectiveNullPolarIncidence
open InfoGeometry.Twistor.ProjectiveNullIsometryIncidence

/-- The native split-Pin element acting on the projective `Q55` null
boundary. -/
def realSplitPinNullEquiv (g : realSplitPin55) :
    TwistorSpace Q55 ≃ TwistorSpace Q55 :=
  nullIsometryEquiv (realSplitPinNativeOrthogonalAction g)

@[simp] theorem realSplitPinNullEquiv_one :
    realSplitPinNullEquiv (1 : realSplitPin55) = 1 := by
  apply Equiv.ext
  intro p
  apply Subtype.ext
  change projectiveIsometryMap
      (realSplitPinNativeOrthogonalAction 1) p.1 = p.1
  refine Projectivization.ind (p := p.1) ?_
  intro x hx
  rw [map_one, projectiveIsometryMap_mk]
  apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
  refine ⟨1, ?_⟩
  simp only [one_smul]
  rfl

@[simp] theorem realSplitPinNullEquiv_mul (g h : realSplitPin55) :
    realSplitPinNullEquiv (g * h) =
      realSplitPinNullEquiv g * realSplitPinNullEquiv h := by
  apply Equiv.ext
  intro p
  apply Subtype.ext
  change projectiveIsometryMap
      (realSplitPinNativeOrthogonalAction (g * h)) p.1 =
    projectiveIsometryMap (realSplitPinNativeOrthogonalAction g)
      (projectiveIsometryMap (realSplitPinNativeOrthogonalAction h) p.1)
  refine Projectivization.ind (p := p.1) ?_
  intro x hx
  rw [map_mul, projectiveIsometryMap_mk, projectiveIsometryMap_mk,
    projectiveIsometryMap_mk]
  apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
  refine ⟨1, ?_⟩
  simp only [one_smul]
  rfl

/-- The concrete real split-Pin group action on projective `Q55` null
rays. -/
def realSplitPinNullAction :
    realSplitPin55 →* Equiv.Perm (TwistorSpace Q55) where
  toFun := realSplitPinNullEquiv
  map_one' := realSplitPinNullEquiv_one
  map_mul' := realSplitPinNullEquiv_mul

@[simp] theorem realSplitPinNullAction_apply
    (g : realSplitPin55) (p : TwistorSpace Q55) :
    realSplitPinNullAction g p = realSplitPinNullEquiv g p :=
  rfl

/-- Every concrete real split-Pin transformation preserves native polar
incidence on the projective `Q55` null boundary. -/
theorem realSplitPinNullAction_preserves_incidence
    (g : realSplitPin55) (p q : TwistorSpace Q55) :
    NullPolarIncident Q55 (realSplitPinNullAction g p)
        (realSplitPinNullAction g q) ↔
      NullPolarIncident Q55 p q := by
  exact nullIsometryEquiv_preserves_incidence
    (realSplitPinNativeOrthogonalAction g) p q

end InfoGeometry.Twistor.Cl55RealSplitPinNullIncidence
