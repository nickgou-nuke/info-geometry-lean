import Mathlib
import InfoGeometry.Arithmetic.PrimeMajoranaPfaffian

/-!
# InfoGeometry.Canonical.PrimeMajoranaPfaffianCalibration

Canonical wrapper for the finite block-Pfaffian owner.

This file adds no analytic content. It only re-exports the finite Pfaffian
identification under a canonical owner-facing namespace.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeMajoranaPfaffianCalibration

open InfoGeometry.Arithmetic.PrimeMajoranaPfaffian

/-- Canonical re-export of the finite block-Pfaffian / Euler-product theorem. -/
theorem canonicalBlockPfaffian_eq_finiteEulerProduct
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) (q : ℕ → ℝ) :
    blockPfaffian P q = InfoGeometry.Arithmetic.SplitMajoranaPrimon.finiteEulerProduct P q :=
  blockPfaffian_eq_finiteEulerProduct P q

/-- Canonical owner target for the finite block-Pfaffian surface. -/
def CanonicalPrimeMajoranaPfaffianOwnerTarget : Prop :=
  ∀ (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) (q : ℕ → ℝ),
    blockPfaffian P q = InfoGeometry.Arithmetic.SplitMajoranaPrimon.finiteEulerProduct P q

/-- The canonical owner target is proved. -/
theorem canonicalPrimeMajoranaPfaffianOwnerTarget :
    CanonicalPrimeMajoranaPfaffianOwnerTarget := by
  intro P q
  exact canonicalBlockPfaffian_eq_finiteEulerProduct P q

end InfoGeometry.Canonical.PrimeMajoranaPfaffianCalibration
