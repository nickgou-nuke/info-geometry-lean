import InfoGeometry.Exceptional.FreudenthalFiveGradedJacobiClosure
import InfoGeometry.Exceptional.FreudenthalSymplecticMixedTripleCounterexample

/-!
# A false homogeneous Jacobi cell for the legacy five-graded operation

The missing global Jacobi proof for `fiveGradedBracket` cannot be completed:
one of its extreme/charge cells is false. This is independent of the Jordan
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

variable {J : Type*} [AddCommGroup J] [Module ℝ J] [Nontrivial J]
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
  module

/-- Concrete nonzero witness using the scalar alpha charge. This rules out
Jacobi for the legacy operation itself. -/
theorem legacy_fiveGradedBracket_not_jacobi :
    fiveJacobiator D (genEplus D 1) (genEminus D 1)
        (injChargePlus D (alphaCharge (J := J))) ≠ 0 := by
  rw [legacy_extreme_extreme_plus_jacobiator]
  intro h
  have hplus := congrArg
    (fun u : FiveGradedCarrier D => u.plus1.alpha) h
  have htwo : (2 : ℝ) • (1 : J) = 0 := by
    simpa [injChargePlus, alphaCharge, two_smul] using hplus
  rcases smul_eq_zero.mp htwo with htwo | hone
  · norm_num at htwo
  · exact one_ne_zero hone

end InfoGeometry.Exceptional.Freudenthal
