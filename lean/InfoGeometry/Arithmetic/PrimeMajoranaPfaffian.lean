import InfoGeometry.Arithmetic.SplitMajoranaPrimon


noncomputable section

namespace InfoGeometry.Arithmetic.PrimeMajoranaPfaffian

open scoped BigOperators

def blockPfaffian
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (q : ℕ → ℝ) : ℝ :=
  InfoGeometry.Arithmetic.SplitMajoranaPrimon.finiteEulerProduct P q

theorem blockPfaffian_eq_finiteEulerProduct
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (q : ℕ → ℝ) :
    blockPfaffian P q =
      InfoGeometry.Arithmetic.SplitMajoranaPrimon.finiteEulerProduct P q := by
  rfl

end InfoGeometry.Arithmetic.PrimeMajoranaPfaffian
