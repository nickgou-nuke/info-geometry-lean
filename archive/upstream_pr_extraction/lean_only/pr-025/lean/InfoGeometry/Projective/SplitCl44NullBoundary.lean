import Mathlib
import InfoGeometry.Clifford.SplitCl44CausalEnvelope
import InfoGeometry.Projective.NullBoundary

/-!
# Split `Cl(4,4)` projective null boundary

This module packages the split `Cl(4,4)` causal envelope as a generic
projective-null datum, parallel to the repo's twistor and split-octonion
adapters.

It does not identify the Penrose twistor carrier with the split `Cl(4,4)`
carrier.  It only records the common quotient pattern:

* a real quadratic null readout,
* a nonzero null representative,
* quotient by unit scaling.
-/

open scoped Classical

namespace InfoGeometry.Projective.SplitCl44NullBoundary

open InfoGeometry.Clifford.SplitCl44CausalEnvelope

/-- The split `Cl(4,4)` causal-envelope datum as a generic projective-null datum. -/
noncomputable def asProjectiveNullBoundaryDatum :
    ProjectiveNullBoundaryDatum ℝ ℝ SplitCl44Carrier where
  q := SplitCl44Quad
  zero := 0
  scale := fun u v => (u : ℝ) • v
  scale_one := by
    intro v
    simp
  scale_mul := by
    intro u v w
    simp [smul_smul]
  null_scale := by
    intro u v
    constructor
    · intro h
      have hmul : ((u : ℝ) * (u : ℝ)) * SplitCl44Quad v = 0 := by
        simpa [SplitCl44Quad.map_smul] using h
      rcases mul_eq_zero.mp hmul with husq | hv
      · exfalso
        have hu : (u : ℝ) = 0 := by
          rcases mul_eq_zero.mp husq with hu | hu
          · exact hu
          · exact hu
        exact Units.ne_zero u hu
      · exact hv
    · intro h
      rw [SplitCl44Quad.map_smul, h]
      simp
  scale_ne_zero := by
    intro u v hv
    exact smul_ne_zero (Units.ne_zero u) hv

/-- Split `Cl(4,4)` null representatives as projective-null data. -/
abbrev SplitCl44ProjectiveNullRep :=
  ProjectiveNullBoundaryDatum.NullRep asProjectiveNullBoundaryDatum

/-- Split `Cl(4,4)` projective null quotient as the generic quotient. -/
abbrev SplitCl44ProjectiveNullSpace :=
  ProjectiveNullBoundaryDatum.ProjectiveNullBoundary asProjectiveNullBoundaryDatum

/-- A nonzero split `Cl(4,4)` null representative defines a projective null point. -/
def splitCl44NullMk (Z : SplitCl44ProjectiveNullRep) : SplitCl44ProjectiveNullSpace :=
  ProjectiveNullBoundaryDatum.nullMk asProjectiveNullBoundaryDatum Z

@[simp] theorem splitCl44NullMk_scale
    (u : ℝˣ) (Z : SplitCl44ProjectiveNullRep) :
    splitCl44NullMk Z = splitCl44NullMk (ProjectiveNullBoundaryDatum.scaleNull
      asProjectiveNullBoundaryDatum u Z) := by
  exact ProjectiveNullBoundaryDatum.nullMk_scaleNull asProjectiveNullBoundaryDatum u Z

/-- The split `Cl(4,4)` causal boundary contains the concrete head-null ray. -/
theorem splitCl44ProjectiveNullBoundary_nonempty :
    ∃ Z : SplitCl44ProjectiveNullRep,
      Z.Z = InfoGeometry.Clifford.ClNN.headNullMinus 3 ∧
        splitCl44NullMk Z =
          ProjectiveNullBoundaryDatum.nullMk asProjectiveNullBoundaryDatum Z := by
  refine ⟨⟨InfoGeometry.Clifford.ClNN.headNullMinus 3,
      splitCl44_headNullMinus_isotropic,
      by
        intro hzero
        have hzeroγ : InfoGeometry.Clifford.ClNN.gammaHeadNullMinus 3 = 0 := by
          rw [InfoGeometry.Clifford.ClNN.gammaHeadNullMinus, hzero]
          exact LinearMap.map_zero (CliffordAlgebra.ι (Clifford.ClNN.Quad 4))
        have hcontr : (0 : SplitCl44Algebra) = 1 := by
          simpa [hzeroγ] using (splitCl44_headNull_clifford_car)
        have hExterior :=
          congrArg
            (CliffordAlgebra.equivExterior (InfoGeometry.Clifford.ClNN.Quad 4))
            hcontr
        simpa using hExterior⟩, rfl, rfl⟩

/-- The split `Cl(4,4)` projective null quotient is inhabited by the concrete
head-null ray. -/
theorem splitCl44ProjectiveNullSpace_nonempty :
    Nonempty SplitCl44ProjectiveNullSpace := by
  rcases splitCl44ProjectiveNullBoundary_nonempty with ⟨Z, _hZ, _hmk⟩
  exact ⟨splitCl44NullMk Z⟩

end InfoGeometry.Projective.SplitCl44NullBoundary
