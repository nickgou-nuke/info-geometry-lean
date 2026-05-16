import Mathlib
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet

Discrete wavelets with quaternion / Clifford coefficients.

Literature owner:
  Peter Fletcher, "Discrete Wavelets with Quaternion and Clifford Coefficients"
  in Advances in Applied Clifford Algebras.

This file owns the theorem-safe interface for the discrete Hurwitz--Clifford
filter-bank layer:

* Hurwitz-type discrete coefficient geometry;
* quaternion / Clifford-valued filter coefficients;
* polyphase / paraunitary completion;
* perfect reconstruction and energy preservation as owned consequences of
  paraunitarity;
* a cascade system with explicit convergence and regularity sockets.

It does not assert any prime-number, Lee--Yang, xi, or RH theorem.
-/

noncomputable section

namespace InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet

/-- Abstract Hurwitz integer lattice used as the discrete coefficient geometry. -/
@[rep_depth operator]
structure HurwitzIntegerModel where
  Point : Type
  additionClosed : Prop
  multiplicationClosed : Prop
  divisionWithRemainder : Prop

/-- Abstract quaternion / Clifford coefficient model. -/
@[rep_depth operator]
structure CliffordCoefficientModel where
  Coeff : Type
  zero : Coeff
  one : Coeff
  add : Coeff → Coeff → Coeff
  mul : Coeff → Coeff → Coeff
  conj : Coeff → Coeff
  normSq : Coeff → ℝ
  clifford_or_quaternion_structure : Prop

/-- Abstract discrete filter index set. -/
@[rep_depth operator]
structure DiscreteFilterIndex where
  Index : Type

/--
Paraunitary quaternion / Clifford filter bank.

The important boundary is explicit:

* `paraunitary` owns the perfect-reconstruction and energy-preservation
  consequences;
* the cascade convergence and regularity claims are separate sockets.
-/
@[rep_depth operator]
structure ParaunitaryCliffordFilterBank where
  lattice : HurwitzIntegerModel
  coeffs : CliffordCoefficientModel
  index : DiscreteFilterIndex

  lowPass : index.Index → coeffs.Coeff
  highPass : index.Index → coeffs.Coeff

  polyphaseMatrix : Prop
  paraunitary : Prop
  perfectReconstruction : Prop
  perfectReconstruction_certificate :
    paraunitary → perfectReconstruction
  energyPreservation : Prop
  energyPreservation_certificate :
    paraunitary → energyPreservation

/-- Extract the owned perfect-reconstruction certificate from paraunitarity. -/
@[rep_depth operator]
theorem perfectReconstruction_of_paraunitary
    (F : ParaunitaryCliffordFilterBank)
    (h : F.paraunitary) :
    F.perfectReconstruction :=
  F.perfectReconstruction_certificate h

/-- Extract the owned energy-preservation certificate from paraunitarity. -/
@[rep_depth operator]
theorem energyPreservation_of_paraunitary
    (F : ParaunitaryCliffordFilterBank)
    (h : F.paraunitary) :
    F.energyPreservation :=
  F.energyPreservation_certificate h

/--
Discrete cascade system attached to a paraunitary Clifford filter bank.

The convergence and regularity fields are intentionally separate from
paraunitarity.  The latter gives the L² perfect-reconstruction layer, while
the former are the analytic upgrade needed for compact-uniform convergence
questions.
-/
@[rep_depth operator]
structure CliffordCascadeSystem
    (F : ParaunitaryCliffordFilterBank) where
  Signal : Type
  scalingApproximation : ℕ → Signal
  waveletDetail : ℕ → Signal

  cascadeAlgorithm : Prop
  cascadeAlgorithm_certificate : cascadeAlgorithm
  regularityWitness : Prop
  regularityWitness_certificate : regularityWitness
  sumRuleWitness : Prop
  sumRuleWitness_certificate : sumRuleWitness
  cascadeConvergesL2 : Prop
  cascadeConvergesL2_certificate : cascadeConvergesL2
  compactUniformUpgrade : Prop
  compactUniformUpgrade_certificate : compactUniformUpgrade
  reconstructionExists : Prop
  reconstructionExists_certificate : reconstructionExists

namespace CliffordCascadeSystem

variable {F : ParaunitaryCliffordFilterBank}
variable (C : CliffordCascadeSystem F)

/-- Re-export of the stored cascade convergence claim. -/
@[rep_depth operator]
theorem cascadeConvergesL2_law :
    C.cascadeConvergesL2 :=
  C.cascadeConvergesL2_certificate

/-- Re-export of the stored compact-uniform upgrade claim. -/
@[rep_depth operator]
theorem compactUniformUpgrade_law :
    C.compactUniformUpgrade :=
  C.compactUniformUpgrade_certificate

end CliffordCascadeSystem

end InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet
