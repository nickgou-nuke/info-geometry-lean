import InfoGeometry.Algebra.KleinSpinorOrbit
import InfoGeometry.Algebra.KleinSpinorOrbitSocketClosure
import Mathlib.Tactic

/-!
# Orbit completeness: every non-zero Cs² spinor reaches (1,0) or (E,0) under SL(2,Cs)

This file states the orbit completeness theorem. The SymPy property at
`tools/sympy/orbit_completeness.py` provides the constructive verification.

The proof strategy uses the E/Ē decomposition `Cs ≅ ℚ·E ⊕ ℚ·Ē` under which
`SL(2,Cs) ≅ SL(2,ℚ) × SL(2,ℚ)`. The SL(2,ℚ) transitivity on ℚ²\{0}
gives the construction via `SpecialLinearGroup`.  See `stabilizes_generic_iff`
and `KleinSpinorOrbitSocketClosure` for the stabilizer closure.
-/

open InfoGeometry.Algebra.KleinSpinorOrbit
open InfoGeometry.Algebra.KleinSpinorOrbitSocketClosure

namespace InfoGeometry.Algebra.KleinSpinorOrbitCompleteness

/-- The zero split-complex spinor. -/
def zeroSpinor : CsSpinor :=
  ⟨Cs.zero, Cs.zero⟩

/-- A spinor reaches one of the two finite representatives used in this file. -/
def ReachesRepresentative (ψ : CsSpinor) : Prop :=
  (∃ g : CsSL2, CsSL2.action g ψ = genericRep) ∨
    (∃ g : CsSL2, CsSL2.action g ψ = nullRep)

/--
The still-open full completeness claim, stated as an explicit proposition rather
than as an unproved theorem: every non-zero `C_s²` spinor reaches `(1,0)` or
`(E,0)` under a determinant-one split-complex matrix.
-/
def OrbitCompletenessClaim : Prop :=
  ∀ ψ : CsSpinor, ψ ≠ zeroSpinor → ReachesRepresentative ψ

/-- The generic representative is non-zero. -/
theorem genericRep_ne_zeroSpinor : genericRep ≠ zeroSpinor := by
  intro h
  have hplus := congrArg CsSpinor.plus h
  have hre := congrArg InfoGeometry.Clifford.Arxiv160309063.SplitC.re hplus
  norm_num [genericRep, zeroSpinor, Cs.one, Cs.zero,
    InfoGeometry.Clifford.Arxiv160309063.SplitC.one,
    InfoGeometry.Clifford.Arxiv160309063.SplitC.scalar] at hre

/-- The null representative is non-zero. -/
theorem nullRep_ne_zeroSpinor : nullRep ≠ zeroSpinor := by
  intro h
  have hplus := congrArg CsSpinor.plus h
  have hre := congrArg InfoGeometry.Clifford.Arxiv160309063.SplitC.re hplus
  norm_num [nullRep, zeroSpinor, Cs.E, Cs.zero,
    InfoGeometry.Clifford.Arxiv160309063.SplitC.E] at hre

/-- The generic representative reaches itself by the identity element. -/
theorem genericRep_reachesRepresentative : ReachesRepresentative genericRep := by
  left
  exact ⟨CsSL2.identity, CsSL2.identity_action genericRep⟩

/-- The null representative reaches itself by the identity element. -/
theorem nullRep_reachesRepresentative : ReachesRepresentative nullRep := by
  right
  exact ⟨CsSL2.identity, CsSL2.identity_action nullRep⟩

end InfoGeometry.Algebra.KleinSpinorOrbitCompleteness
