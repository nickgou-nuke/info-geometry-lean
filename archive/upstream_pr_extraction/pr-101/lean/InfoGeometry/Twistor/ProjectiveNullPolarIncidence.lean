import InfoGeometry.Twistor.NullProjective

/-!
# Polar incidence on projective null geometry

This owner descends the zero locus of the polar form of a native Mathlib
`QuadraticForm` to projective rays.  Restricting it to `TwistorSpace Q` gives
the intrinsic polar-incidence relation on projective null rays.
-/

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Twistor.ProjectiveNullPolarIncidence

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Two projective rays are polar-incident when the polar form of any pair of
nonzero representatives vanishes. -/
def PolarIncident (Q : QuadraticForm K V) : ℙ K V → ℙ K V → Prop :=
  Projectivization.lift
    (f := fun X : {X : V // X ≠ 0} =>
      Projectivization.lift
        (f := fun Y : {Y : V // Y ≠ 0} =>
          QuadraticMap.polar Q X Y = 0)
        (hf := by
          intro Y Z c hYZ
          apply propext
          have hc : c ≠ 0 := by
            intro hc
            have : (Y : V) = 0 := by simpa [hc] using hYZ
            exact Y.2 this
          have hscaled :
              QuadraticMap.polar Q X Y =
                c * QuadraticMap.polar Q X Z := by
            calc
              QuadraticMap.polar Q X Y =
                  QuadraticMap.polar Q X (c • (Z : V)) :=
                congrArg (fun W : V => QuadraticMap.polar Q X W) hYZ
              _ = c * QuadraticMap.polar Q X Z := by
                simp [QuadraticMap.polar_smul_right, smul_eq_mul]
          constructor
          · intro hY
            change QuadraticMap.polar Q X Y = 0 at hY
            have : c * QuadraticMap.polar Q X Z = 0 := by
              rw [← hscaled, hY]
            exact (mul_eq_zero.mp this).resolve_left hc
          · intro hZ
            change QuadraticMap.polar Q X Z = 0 at hZ
            change QuadraticMap.polar Q X Y = 0
            rw [hscaled, hZ, mul_zero]))
    (hf := by
      intro X Y c hXY
      funext p
      apply propext
      refine Projectivization.ind (p := p) ?_
      intro Z hZ
      simp only [Projectivization.lift_mk]
      have hc : c ≠ 0 := by
        intro hc
        have : (X : V) = 0 := by simpa [hc] using hXY
        exact X.2 this
      have hscaled :
          QuadraticMap.polar Q X Z = c * QuadraticMap.polar Q Y Z := by
        calc
          QuadraticMap.polar Q X Z =
              QuadraticMap.polar Q (c • (Y : V)) Z :=
            congrArg (fun W : V => QuadraticMap.polar Q W Z) hXY
          _ = c * QuadraticMap.polar Q Y Z := by
            simp [QuadraticMap.polar_smul_left, smul_eq_mul]
      constructor
      · intro hX
        have : c * QuadraticMap.polar Q Y Z = 0 := by
          rw [← hscaled, hX]
        exact (mul_eq_zero.mp this).resolve_left hc
      · intro hY
        rw [hscaled, hY, mul_zero])

@[simp] theorem polarIncident_mk_iff
    (Q : QuadraticForm K V) (X Y : V) (hX : X ≠ 0) (hY : Y ≠ 0) :
    PolarIncident Q (Projectivization.mk K X hX)
        (Projectivization.mk K Y hY) ↔
      QuadraticMap.polar Q X Y = 0 := by
  simp [PolarIncident, Projectivization.lift_mk]

/-- Polar incidence restricted to the projective null locus. -/
def NullPolarIncident (Q : QuadraticForm K V)
    (p q : TwistorSpace Q) : Prop :=
  PolarIncident Q p.1 q.1

end InfoGeometry.Twistor.ProjectiveNullPolarIncidence
