import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

namespace TwelveFoldCyclotomicArithmetic
open Polynomial

example : cyclotomic 12 ℤ = X ^ 4 - X ^ 2 + 1 := by
  norm_num [cyclotomic]

end TwelveFoldCyclotomicArithmetic
