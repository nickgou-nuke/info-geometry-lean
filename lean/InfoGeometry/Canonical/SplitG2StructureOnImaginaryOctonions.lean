import InfoGeometry.Canonical.SplitOctonionCanonicalThreeForm

namespace InfoGeometry.Canonical

/-!
The imaginary split-octonion carrier is the kernel of the scalar-coordinate
projection.  This file packages the canonical trilinear witness on that carrier
and the verified colour-cycle invariance.  It does not claim a holonomy theorem
or a full differential-geometric `G₂` structure.
-/

noncomputable def scalarPart :
    StandardRationalSplitOctonion →ₗ[ℚ] ℚ where
  toFun x := x .one
  map_add' x y := rfl
  map_smul' c x := rfl

theorem scalarPart_surjective : Function.Surjective scalarPart := by
  intro q
  refine ⟨Pi.single IntegralSplitBasis.one q, ?_⟩
  simp [scalarPart]

noncomputable abbrev imaginarySplitOctonion := LinearMap.ker scalarPart

namespace imaginarySplitOctonion

@[simp] theorem one_eq_zero (x : imaginarySplitOctonion) : x.1 .one = 0 := x.2

end imaginarySplitOctonion

theorem imaginarySplitOctonion_finrank_eq_seven :
    Module.finrank ℚ imaginarySplitOctonion = 7 := by
  have hcard : Fintype.card IntegralSplitBasis = 8 := by decide
  have hdim : Module.finrank ℚ StandardRationalSplitOctonion = 8 := by
    calc
      Module.finrank ℚ StandardRationalSplitOctonion
          = Fintype.card IntegralSplitBasis := by
              simpa [StandardRationalSplitOctonion] using
                (Module.finrank_pi (R := ℚ) (ι := IntegralSplitBasis))
      _ = 8 := hcard
  have htop : LinearMap.range scalarPart = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact scalarPart_surjective
  have h : 1 + Module.finrank ℚ imaginarySplitOctonion = 8 := by
    have h := LinearMap.finrank_range_add_finrank_ker (f := scalarPart)
    rw [htop, hdim] at h
    simpa [imaginarySplitOctonion] using h
  omega

theorem trialityColorCycle_one_coord
    (x : StandardRationalSplitOctonion) :
    (trialityColorCycle x) IntegralSplitBasis.one = x IntegralSplitBasis.one := by
  simp [trialityColorCycle, colorCycleBasisEquiv, colorCycleBasis, colorCycleBasisInv]

theorem colorReflection_one_coord
    (x : StandardRationalSplitOctonion) :
    (colorReflection x) IntegralSplitBasis.one = x IntegralSplitBasis.one := by
  simp [colorReflection, colorReflectionBasisEquiv, colorReflectionBasis,
    colorReflectionSign]

noncomputable def trialityColorCycleImaginary (x : imaginarySplitOctonion) : imaginarySplitOctonion :=
  ⟨trialityColorCycle x, by
    change (trialityColorCycle x) IntegralSplitBasis.one = 0
    rw [trialityColorCycle_one_coord]
    exact x.2⟩

noncomputable def colorReflectionImaginary (x : imaginarySplitOctonion) : imaginarySplitOctonion :=
  ⟨colorReflection x, by
    change (colorReflection x) IntegralSplitBasis.one = 0
    rw [colorReflection_one_coord]
    exact x.2⟩

def canonicalSplitG2ThreeFormValue
    (x y z : imaginarySplitOctonion) : ℚ :=
  canonicalThreeForm x.1 y.1 z.1

theorem canonicalSplitG2ThreeFormValue_apply
    (x y z : imaginarySplitOctonion) :
    canonicalSplitG2ThreeFormValue x y z = canonicalThreeForm x y z := rfl

theorem trialityColorCycle_preserves_canonicalSplitG2ThreeForm
    (x y z : imaginarySplitOctonion) :
    canonicalSplitG2ThreeFormValue
        (trialityColorCycleImaginary x)
        (trialityColorCycleImaginary y)
        (trialityColorCycleImaginary z) =
      canonicalSplitG2ThreeFormValue x y z := by
  simpa [canonicalSplitG2ThreeFormValue, trialityColorCycleImaginary]
    using trialityColorCycle_preserves_canonicalThreeForm x y z

theorem colorReflection_preserves_norm
    (x : StandardRationalSplitOctonion) :
    coordinateSplitNorm (colorReflection x) = coordinateSplitNorm x := by
  simp [coordinateSplitNorm, colorReflection, colorReflectionBasisEquiv,
    colorReflectionBasis, colorReflectionSign]
  ring

theorem colorReflection_preserves_inner
    (x y : StandardRationalSplitOctonion) :
    splitInner (colorReflection x) (colorReflection y) = splitInner x y := by
  unfold splitInner
  have hsum :
      colorReflection (x + y) = colorReflection x + colorReflection y :=
    colorReflection.map_add x y
  rw [← hsum, colorReflection_preserves_norm (x + y),
    colorReflection_preserves_norm x, colorReflection_preserves_norm y]

theorem colorReflection_preserves_canonicalSplitG2ThreeForm
    (x y z : imaginarySplitOctonion) :
    canonicalSplitG2ThreeFormValue
        (colorReflectionImaginary x)
        (colorReflectionImaginary y)
        (colorReflectionImaginary z) =
      canonicalSplitG2ThreeFormValue x y z := by
  unfold canonicalSplitG2ThreeFormValue canonicalThreeForm
  change splitInner
      (splitOctonionMulQ (colorReflection x.1) (colorReflection y.1))
      (colorReflection z.1) =
    splitInner (splitOctonionMulQ x.1 y.1) z.1
  rw [← colorReflection_map_mul]
  exact colorReflection_preserves_inner (splitOctonionMulQ x.1 y.1) z.1

end InfoGeometry.Canonical
