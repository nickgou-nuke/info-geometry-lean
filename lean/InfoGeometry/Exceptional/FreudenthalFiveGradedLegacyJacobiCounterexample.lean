import InfoGeometry.Exceptional.FreudenthalFiveGradedJacobiClosure
import InfoGeometry.Exceptional.FreudenthalSymplecticMixedTripleCounterexample

/-!
# A false homogeneous Jacobi cell for the legacy five-graded operation

The missing global Jacobi proof for `fiveGradedBracket` cannot be completed:
one of its extreme/charge cells is false.  This is independent of the Jordan
product and cubic norm.

With the legacy signs

```
[Eplus,Eminus] = H,
[H,yplus] = yplus,
[Eminus,yplus] = yminus,
[Eplus,yminus] = -yplus,
```

the cyclic Jacobiator is `-2*yplus`.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-- Exact value of the false `(2,-2,1)` homogeneous Jacobi cell. -/
theorem legacy_extreme_extreme_plus_jacobiator
    (y : FreudenthalCharge J) :
    fiveJacobiator D (genEplus D 1) (genEminus D 1)
        (injChargePlus D y) =
      injChargePlus D ((-2 : ℝ) • y) := by
  apply FiveGradedCarrier.ext <;>
    simp [fiveJacobiator, fiveGradedBracket, genEplus, genEminus,
      genHscale, injChargePlus]

/-- Concrete nonzero witness using the scalar alpha charge. -/
theorem legacy_fiveGradedBracket_not_jacobi :
    fiveJacobiator D (genEplus D 1) (genEminus D 1)
        (injChargePlus D (alphaCharge (J := J))) ≠ 0 := by
  rw [legacy_extreme_extreme_plus_jacobiator]
  intro h
  have hplus := congrArg
    (fun u : FiveGradedCarrier D => u.plus1.alpha) h
  norm_num [injChargePlus, alphaCharge] at hplus

/-- Consequently no native Lie-ring structure can have
`fiveGradedBracket D` as its bracket. -/
theorem no_LieRing_with_legacy_fiveGradedBracket :
    ¬ (∃ _inst : LieRing (FiveGradedCarrier D),
      ∀ u v : FiveGradedCarrier D,
        @Bracket.bracket _ _ _ _inst.toBracket u v =
          fiveGradedBracket D u v) := by
  rintro ⟨inst, hbracket⟩
  letI : LieRing (FiveGradedCarrier D) := inst
  have hJ := lie_jacobi
    (genEplus D 1) (genEminus D 1)
    (injChargePlus D (alphaCharge (J := J)))
  have hcyclic :
      fiveJacobiator D (genEplus D 1) (genEminus D 1)
          (injChargePlus D (alphaCharge (J := J))) = 0 := by
    unfold fiveJacobiator
    rw [← hbracket, ← hbracket, ← hbracket,
      ← hbracket, ← hbracket, ← hbracket]
    simpa [lie_skew] using hJ
  exact legacy_fiveGradedBracket_not_jacobi D hcyclic

end InfoGeometry.Exceptional.Freudenthal
