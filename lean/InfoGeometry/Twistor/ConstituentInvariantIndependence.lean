/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Twistor.ConstituentWittGram
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Algebraic independence of the two real squared readouts

The functions use the existing pair-mass normalization and the squared Witt
cross-pairing on the same two-packet. Joint realization covers the whole
nonnegative quadrant. Polynomial extensionality on that infinite box proves
actual algebraic independence in the native algebra of real-valued functions.
-/

noncomputable section

namespace InfoGeometry.Twistor.ConstituentInvariantIndependence

open PenroseIncidence PerjesConventions TwistorConstituentKinematics
open ConstituentWittGram

/-- Native mass determinant and squared conformal cross-pairing. -/
def invariants (i : Fin 2) (Z : Packet (Fin 2)) : ℝ :=
  ![pairMassSq (Z 0) (Z 1), Complex.normSq (wittPair (Z 0) (Z 1))] i

/-- Every nonnegative pair is attained on two individually Witt-null columns. -/
theorem realize_nonnegative (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ Z : Packet (Fin 2),
      invariants 0 Z = a ∧ invariants 1 Z = b ∧
      wittPair (Z 0) (Z 0) = 0 ∧ wittPair (Z 1) (Z 1) = 0 := by
  let t : ℂ := Real.sqrt a
  let z : ℂ := Real.sqrt b
  refine ⟨![realizationFirst, realizationSecond t z], ?_, ?_, ?_, ?_⟩
  · simp only [invariants, Matrix.cons_val_zero, Matrix.cons_val_one,
      realization_mass]
    simpa [t, Complex.normSq_apply, pow_two] using Real.sq_sqrt ha
  · simp only [invariants, Matrix.cons_val_zero, Matrix.cons_val_one,
      realization_witt]
    simpa [z, Complex.normSq_apply, pow_two] using Real.sq_sqrt hb
  · simp [realizationFirst, wittPair]
  · simp [realizationSecond, wittPair, Fin.sum_univ_two]

/-- No nonzero real polynomial vanishes on these two functions. -/
theorem invariants_algebraicIndependent :
    AlgebraicIndependent ℝ invariants := by
  rw [algebraicIndependent_iff]
  intro p hp
  apply MvPolynomial.funext_set (fun _ : Fin 2 => Set.Ici (0 : ℝ))
    (fun _ => Set.Ici_infinite 0)
  intro x hx
  obtain ⟨Z, h0, h1, _, _⟩ :=
    realize_nonnegative (x 0) (x 1) (hx 0 (Set.mem_univ 0)) (hx 1 (Set.mem_univ 1))
  have hvalues : (fun i => invariants i Z) = x := by
    funext i
    fin_cases i
    · exact h0
    · exact h1
  have heval := MvPolynomial.comp_aeval_apply
    (f := invariants) (Pi.evalAlgHom ℝ (fun _ : Packet (Fin 2) => ℝ) Z) p
  have hzero : MvPolynomial.aeval (fun i => invariants i Z) p = 0 := by
    simpa [hp] using heval.symm
  rw [hvalues] at hzero
  simpa only [MvPolynomial.aeval_eq_eval, map_zero] using hzero

end InfoGeometry.Twistor.ConstituentInvariantIndependence
