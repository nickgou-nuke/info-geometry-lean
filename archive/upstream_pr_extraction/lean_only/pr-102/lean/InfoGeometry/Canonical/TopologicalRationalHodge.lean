import Mathlib
import InfoGeometry.Canonical.RationalHodgeSectorIntertwiner

/-!
  Continuous readouts of the explicit rational Hodge maps.  The algebraic
  Hodge equivalence remains primary; topology is obtained only under the
  stated normed-space and finite-dimensional hypotheses.
-/

noncomputable section

namespace InfoGeometry.Canonical

variable {V : Type*}
  [NormedAddCommGroup V]
  [NormedSpace ℚ V]
  [FiniteDimensional ℚ V]

noncomputable def continuousRationalLinearMap
    (L : V →ₗ[ℚ] V) (hL : Continuous L) : V →L[ℚ] V :=
  ⟨L, hL⟩

noncomputable def continuousRationalHodgeStar
    (H : RationalHodgeData V) (hStar : Continuous H.star.toLinearMap) : V →L[ℚ] V :=
  continuousRationalLinearMap H.star.toLinearMap hStar

noncomputable def continuousRationalHodgeStarSymm
    (H : RationalHodgeData V) (hStar : Continuous H.star.symm.toLinearMap) : V →L[ℚ] V :=
  continuousRationalLinearMap H.star.symm.toLinearMap hStar

theorem continuousRationalHodgeStar_continuous
    (H : RationalHodgeData V) (hStar : Continuous H.star.toLinearMap) :
    Continuous (continuousRationalHodgeStar H hStar) :=
  (continuousRationalHodgeStar H hStar).continuous

theorem continuousRationalHodgeStarSymm_continuous
    (H : RationalHodgeData V) (hStar : Continuous H.star.symm.toLinearMap) :
    Continuous (continuousRationalHodgeStarSymm H hStar) :=
  (continuousRationalHodgeStarSymm H hStar).continuous

@[simp] theorem continuousRationalHodgeStar_apply
    (H : RationalHodgeData V) (hStar : Continuous H.star.toLinearMap) (x : V) :
    continuousRationalHodgeStar H hStar x = H.star x := by
  rfl

@[simp] theorem continuousRationalHodgeStarSymm_apply
    (H : RationalHodgeData V) (hStar : Continuous H.star.symm.toLinearMap) (x : V) :
    continuousRationalHodgeStarSymm H hStar x = H.star.symm x := by
  rfl

noncomputable def continuousConjugateCodifferential
    (H : RationalHodgeData V)
    (d : V →ₗ[ℚ] V)
    (hStar : Continuous H.star.toLinearMap)
    (hStarSymm : Continuous H.star.symm.toLinearMap)
    (hd : Continuous d) : V →L[ℚ] V :=
  (continuousRationalHodgeStarSymm H hStarSymm).comp
    ((continuousRationalLinearMap d hd).comp (continuousRationalHodgeStar H hStar))

@[simp] theorem continuousConjugateCodifferential_apply
    (H : RationalHodgeData V)
    (d : V →ₗ[ℚ] V)
    (hStar : Continuous H.star.toLinearMap)
    (hStarSymm : Continuous H.star.symm.toLinearMap)
    (hd : Continuous d) (x : V) :
    continuousConjugateCodifferential H d hStar hStarSymm hd x =
      conjugateCodifferential H d x := by
  rfl

theorem continuousConjugateCodifferential_continuous
    (H : RationalHodgeData V)
    (d : V →ₗ[ℚ] V)
    (hStar : Continuous H.star.toLinearMap)
    (hStarSymm : Continuous H.star.symm.toLinearMap)
    (hd : Continuous d) :
    Continuous (continuousConjugateCodifferential H d hStar hStarSymm hd) :=
  (continuousConjugateCodifferential H d hStar hStarSymm hd).continuous

noncomputable def continuousRationalDiracKahler
    (d cod : V →ₗ[ℚ] V) (hd : Continuous d) (hcod : Continuous cod) : V →L[ℚ] V :=
  continuousRationalLinearMap (rationalDiracKahler d cod) (hd.add hcod)

noncomputable def continuousRationalHodgeLaplacian
    (d cod : V →ₗ[ℚ] V) (hd : Continuous d) (hcod : Continuous cod) : V →L[ℚ] V :=
  continuousRationalLinearMap (rationalHodgeLaplacian d cod)
    ((hd.comp hcod).add (hcod.comp hd))

@[simp] theorem continuousRationalDiracKahler_apply
    (d cod : V →ₗ[ℚ] V) (hd : Continuous d) (hcod : Continuous cod) (x : V) :
    continuousRationalDiracKahler d cod hd hcod x =
      rationalDiracKahler d cod x := by
  rfl

@[simp] theorem continuousRationalHodgeLaplacian_apply
    (d cod : V →ₗ[ℚ] V) (hd : Continuous d) (hcod : Continuous cod) (x : V) :
    continuousRationalHodgeLaplacian d cod hd hcod x =
      rationalHodgeLaplacian d cod x := by
  rfl

theorem continuousRationalDiracKahler_sq_eq_hodgeLaplacian
    (d cod : V →ₗ[ℚ] V)
    (hdc : Continuous d) (hcodc : Continuous cod)
    (hd : d.comp d = 0)
    (hcod : cod.comp cod = 0)
    (x : V) :
    continuousRationalDiracKahler d cod hdc hcodc
        (continuousRationalDiracKahler d cod hdc hcodc x) =
      continuousRationalHodgeLaplacian d cod hdc hcodc x := by
  have h := congrArg (fun L : V →ₗ[ℚ] V => L x)
    (rationalDiracKahler_sq_eq_hodgeLaplacian d cod hd hcod)
  simpa using h

theorem continuousRationalDiracKahler_preserves_sector
    (d cod : V →ₗ[ℚ] V)
    (hdc : Continuous d) (hcodc : Continuous cod)
    (S : Submodule ℚ V)
    (hd : LinearMapPreservesSubmodule d S)
    (hcod : LinearMapPreservesSubmodule cod S)
    {x : V} (hx : x ∈ S) :
    continuousRationalDiracKahler d cod hdc hcodc x ∈ S := by
  simpa using (rationalDiracKahler_preserves_sector d cod S hd hcod) x hx

theorem continuousConjugateCodifferential_preserves_sector
    (H : RationalHodgeData V)
    (d : V →ₗ[ℚ] V)
    (hStarc : Continuous H.star.toLinearMap)
    (hStarSymmc : Continuous H.star.symm.toLinearMap)
    (hdc : Continuous d)
    (S : Submodule ℚ V)
    (hStar : LinearMapPreservesSubmodule H.star.toLinearMap S)
    (hStarSymm : LinearMapPreservesSubmodule H.star.symm.toLinearMap S)
    (hD : LinearMapPreservesSubmodule d S)
    {x : V} (hx : x ∈ S) :
    continuousConjugateCodifferential H d hStarc hStarSymmc hdc x ∈ S := by
  simpa using (conjugateCodifferential_preserves_sector H d S
    hStar hStarSymm hD) x hx

theorem continuousRationalHodgeLaplacian_preserves_sector
    (d cod : V →ₗ[ℚ] V)
    (hdc : Continuous d) (hcodc : Continuous cod)
    (S : Submodule ℚ V)
    (hd : LinearMapPreservesSubmodule d S)
    (hcod : LinearMapPreservesSubmodule cod S)
    {x : V} (hx : x ∈ S) :
    continuousRationalHodgeLaplacian d cod hdc hcodc x ∈ S := by
  simpa using (rationalHodgeLaplacian_preserves_sector d cod S hd hcod) x hx

end InfoGeometry.Canonical
