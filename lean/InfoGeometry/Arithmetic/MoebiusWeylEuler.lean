import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.PNat.Basic
import InfoGeometry.Arithmetic.BostConnesSystem
import InfoGeometry.Arithmetic.PrimonGasPartition
import InfoGeometry.Arithmetic.UResRepresentations

/-!
# Möbius/Weyl finite-sign notes

This file currently defines only a Liouville-style sign readout `weylSign` and
keeps explanatory notes.  It does not prove that the Möbius function is a Weyl
sign character, does not prove an Euler product or zeta inverse identity, and
does not construct `U_res` or an infinite Weyl denominator formula.
-/

open Complex

namespace InfoGeometry.Arithmetic.MoebiusWeylEuler

open BostConnesSystem
open PrimonGasPartition
open UResRepresentations

/- ##The Möbius Function as Weyl Sign -/

/--
A Liouville-style sign readout on positive naturals.  Despite the historical
name, this definition is not a proof of a Weyl-group or Möbius-function
identification.
-/
noncomputable def weylSign (n : ℕ+) : ℂ :=
  liouville n
  -- For squarefree n: λ(n) = (-1)^k = μ(n) (they agree)
  -- For non-squarefree n with a squared factor p²|n:
  --   λ(n) = (-1)^{Ω(n)} ≠ 0 (Liouville counts multiplicity)
  --   μ(n) = 0 (Möbius requires squarefree)
  -- The Möbius function is the restriction of the Liouville
  -- function to the squarefree integers, zero otherwise.
  -- The Weyl sign ε(w_n) is only defined for permutations,
  -- which correspond to squarefree n (no double occupancies).

theorem weylSign_one : weylSign 1 = 1 := by
  simp [weylSign]

theorem weylSign_mul (m n : ℕ+) :
    weylSign (m * n) = weylSign m * weylSign n := by
  have hmul :
      BostConnesSystem.liouville ((m : ℕ) * (n : ℕ)) =
        BostConnesSystem.liouville (m : ℕ) *
          BostConnesSystem.liouville (n : ℕ) := by
    exact BostConnesSystem.liouville_mul
      (m := (m : ℕ)) (n := (n : ℕ))
      (Nat.one_le_iff_ne_zero.mpr m.ne_zero)
      (Nat.one_le_iff_ne_zero.mpr n.ne_zero)
      m.ne_zero n.ne_zero
  simpa [weylSign] using congrArg (fun z : ℤ => (z : ℂ)) hmul

/- ## The Möbius Inversion = Weyl Denominator Formula -/

/-
Möbius inversion, Boolean denominator formulas, and any `U_res` Weyl
denominator theorem must be proved in owner files; they are not proved here.
-/

/- ## The Euler Product Decoupling at β → ∞ -/

/-
No limiting Euler-product, partition-function, supersymmetry, or Fredholm
determinant theorem is proved in this file.
-/

/- ##The Critical Line as Geometric Symmetry Axis -/

/-
No zeta functional-equation, particle-hole duality, or Fredholm-reflection
theorem is proved in this file.
-/

/- ##The Dikin Deformation Paths — From β = ∞ Back to the Critical Strip -/

/-
Any Dikin/Bregman, critical-line, or zero-location interpretation belongs in a
separate owner file with explicit hypotheses.
-/

/- ##Summary: The Complete Geometric Picture -/

/-
Summary: only `weylSign` is defined here.  Broader arithmetic/geometric
interpretations are owner obligations.
-/

end InfoGeometry.Arithmetic.MoebiusWeylEuler
