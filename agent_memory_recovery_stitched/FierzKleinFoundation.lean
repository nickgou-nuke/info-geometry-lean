    (N : FierzNormalization F) :
    FierzKleinCoordinates where
  scalarPhase := normalizedScalarPhase F N
  plucker := chiralPlucker F

/-- The normalized scalar-phase and chiral Pluecker coordinates satisfy the FK constraints. -/
@[rep_depth operator]
theorem fierzKleinCoordinates_holds
    (F : FierzBilinears)
    (N : FierzNormalization F) :
    IsOnFierzKleinVariety
      (fierzKleinCoordinates F N) := by
  constructor
  · exact normalizedScalarPhase_on_quadric F N
  · exact chiralPlucker_on_klein F

/-! ## 6. Area defects and residual bookkeeping -/

/--
Klein area defect.

This is the Pluecker decomposability obstruction `Q_K(P)`.  It vanishes in
the strict Klein sector.  It should not be identified with the scalar-phase
Drazin area defect below.
-/
@[rep_depth operator]
def kleinAreaDefect (P : Bivector4) : ℝ :=
  kleinForm P

/-- A bivector on the Klein quadric has zero Klein area defect. -/
@[rep_depth operator]
theorem kleinAreaDefect_eq_zero_of_on_klein
    (P : Bivector4)
    (hP : IsOnKleinQuadric P) :
    kleinAreaDefect P = 0 := by
  exact hP

/-- The chiral Pluecker bivector has zero Klein area defect. -/
@[rep_depth operator]
theorem kleinAreaDefect_chiralPlucker_eq_zero
    (F : FierzBilinears) :
    kleinAreaDefect (chiralPlucker F) = 0 :=
  kleinAreaDefect_eq_zero_of_on_klein
    (chiralPlucker F)
    (chiralPlucker_on_klein F)

/--
Drazin/scalar-phase area defect.

This measures failure of the normalized scalar-phase equation before enforcing
the strict Fierz normalization:

`â_D = (1 - ŝ² - ω̂²) / 4`.

It is a residual bookkeeping defect, not the Klein form.
-/
@[rep_depth operator]
def drazinScalarPhaseAreaDefect (X : ScalarPhaseFierz) : ℝ :=
  (1 - X.s_hat ^ 2 - X.omega_hat ^ 2) / 4

/--
Deformed scalar-phase Fierz residual:

`1 - ŝ² - ω̂² - 4 â`.
-/
@[rep_depth operator]
def scalarPhaseAreaResidual
    (X : ScalarPhaseFierz)
    (aHat : ℝ) : ℝ :=
  1 - X.s_hat ^ 2 - X.omega_hat ^ 2 - 4 * aHat

/-- The Drazin/scalar-phase area defect is exactly the residual-closing value. -/
@[rep_depth operator]
theorem scalarPhaseAreaResidual_drazinDefect_eq_zero
    (X : ScalarPhaseFierz) :
    scalarPhaseAreaResidual X (drazinScalarPhaseAreaDefect X) = 0 := by
  unfold scalarPhaseAreaResidual drazinScalarPhaseAreaDefect
  ring

/-- On the strict scalar-phase Fierz quadric, the Drazin area defect vanishes. -/
@[rep_depth operator]
theorem drazinScalarPhaseAreaDefect_eq_zero_of_on_quadric
    (X : ScalarPhaseFierz)
    (hX : IsOnScalarPhaseFierzQuadric X) :
    drazinScalarPhaseAreaDefect X = 0 := by
  unfold drazinScalarPhaseAreaDefect IsOnScalarPhaseFierzQuadric at *
  have hnum : 1 - X.s_hat ^ 2 - X.omega_hat ^ 2 = 0 := by
    nlinarith [hX]
  rw [hnum]
  norm_num

/-- Normalized scalar-phase Fierz coordinates have zero Drazin area defect. -/
@[rep_depth operator]
theorem normalizedScalarPhase_drazinAreaDefect_eq_zero
    (F : FierzBilinears)
    (N : FierzNormalization F) :
    drazinScalarPhaseAreaDefect (normalizedScalarPhase F N) = 0 :=
  drazinScalarPhaseAreaDefect_eq_zero_of_on_quadric
    (normalizedScalarPhase F N)
    (normalizedScalarPhase_on_quadric F N)

/-! ## 7. Expectation-only Drazin-horizon readout -/

/-- Real-valued expectation/readout channel. -/
@[rep_depth operator]
abbrev RealChannel (Obs : Type*) :=
  Obs → ℝ

/--
Channel map extracting Fierz bilinears from a Drazin-stabilized observable.

The `area` channel is recorded as a bivector readout.  The vector and axial
channels are real coordinate readouts.
-/
@[rep_depth operator]
structure FierzReadoutChannels (Obs : Type*) where
  scalar : RealChannel Obs
  phase : RealChannel Obs
  vector : I4 → RealChannel Obs
  axial : I4 → RealChannel Obs
  area : Bivector4

/-- Expectation-derived Fierz bilinears from the Drazin-stabilized inverse `Aᴰ`. -/
@[rep_depth operator]
def horizonFierzBilinears
    {Obs : Type*}
    [Ring Obs] [Star Obs]
    (C : FierzReadoutChannels Obs)
    (D : DrazinSupportData Obs) :
    FierzBilinears where
  sigma := C.scalar D.AD
  omega := C.phase D.AD
  J := fun μ => C.vector μ D.AD
  K := fun μ => C.axial μ D.AD
  S := C.area

/--
Drazin-horizon channels are Fierz-admissible when their readout satisfies the
FPK identities and admits a nonzero scalar-phase normalization.
-/
@[rep_depth operator]
structure HorizonFierzAdmissible
    {Obs : Type*}
    [Ring Obs] [Star Obs]
    (C : FierzReadoutChannels Obs)
    (D : DrazinSupportData Obs) where
  fpk :
    FPKIdentities (horizonFierzBilinears C D)
  normalization :
    FierzNormalization (horizonFierzBilinears C D)

/--
Admissible Drazin-horizon Fierz channels produce valid Fierz--Klein
coordinates.

This theorem is compatibility-derived through `HorizonFierzAdmissible`; it does
not assert that arbitrary expectation channels satisfy FPK identities.
-/
@[rep_depth operator]
theorem horizon_fierz_klein_holds
    {Obs : Type*}
    [Ring Obs] [Star Obs]
    (C : FierzReadoutChannels Obs)
    (D : DrazinSupportData Obs)
    (h : HorizonFierzAdmissible C D) :
    IsOnFierzKleinVariety
      (fierzKleinCoordinates
        (horizonFierzBilinears C D)
        h.normalization) :=
  fierzKleinCoordinates_holds
    (horizonFierzBilinears C D)
    h.normalization

end InfoGeometry.Canonical.FierzKleinFoundation
