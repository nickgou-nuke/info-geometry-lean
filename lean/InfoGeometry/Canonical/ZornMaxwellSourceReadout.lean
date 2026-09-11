import InfoGeometry.Canonical.ZornMaxwellComponentReadout
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Source-aware Maxwell readout

This owner separates an externally supplied source `(rho, current)` from the
field components.  It is the non-tautological interface for coupling a Zorn
field readout to source equations; the differential bridge may still choose
induced sources as a separate construction.
-/

namespace InfoGeometry.Canonical.ZornMaxwellSourceReadout

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVec3
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Canonical.ZornMaxwellComponentReadout

abbrev Vec3 := ZornVec3 ℝ
abbrev ZM := ZornVectorMatrix ℝ

structure MaxwellSource where
  rho : ℝ
  current : Vec3

def sourceReadout (S : MaxwellSource) : ZM :=
  ⟨S.rho, S.current, fun i => -S.current i, S.rho⟩

def sourceMaxwellLaws (P : MaxwellComponents) (S : MaxwellSource) : Prop :=
  P.divE = S.rho ∧
    P.divB = 0 ∧
    (∀ i, faradayResidual P i = 0) ∧
    (∀ i, ampereResidual P i = S.current i)

theorem sourceReadout_injective : Function.Injective sourceReadout := by
  intro S T h
  cases S with
  | mk rhoS currentS =>
    cases T with
    | mk rhoT currentT =>
      have hρ : rhoS = rhoT := congrArg (fun X : ZM => X.a) h
      have hj : currentS = currentT := by
        funext i
        exact congrArg (fun X : ZM => X.v i) h
      simp [hρ, hj]

theorem sourceReadout_eq_iff {S T : MaxwellSource} :
    sourceReadout S = sourceReadout T ↔ S = T := by
  exact sourceReadout_injective.eq_iff

theorem derivativeReadout_eq_sourceReadout_iff
    (P : MaxwellComponents) (S : MaxwellSource) :
    derivativeReadout P = sourceReadout S ↔ sourceMaxwellLaws P S := by
  constructor
  · intro h
    have ha : P.divE - P.divB = S.rho := by
      exact congrArg (fun X : ZM => X.a) h
    have hb : P.divE + P.divB = S.rho := by
      exact congrArg (fun X : ZM => X.b) h
    have hdivE : P.divE = S.rho := by linarith
    have hdivB : P.divB = 0 := by linarith
    have huv (i : Fin 3) :
        ampereResidual P i + faradayResidual P i = S.current i := by
      exact congrArg (fun X : ZM => X.v i) h
    have hw (i : Fin 3) :
        faradayResidual P i - ampereResidual P i = -S.current i := by
      exact congrArg (fun X : ZM => X.w i) h
    refine ⟨hdivE, hdivB, ?_, ?_⟩
    · intro i
      linarith [huv i, hw i]
    · intro i
      linarith [huv i, hw i]
  · rintro ⟨hdivE, hdivB, hfaraday, hampere⟩
    apply ZornVectorMatrix.ext
    · simp [derivativeReadout, sourceReadout, hdivE, hdivB]
    · funext i
      have hF := hfaraday i
      have hA := hampere i
      simp only [faradayResidual] at hF
      simp only [ampereResidual] at hA
      change (P.curlB i - P.dtE i) + (P.curlE i + P.dtB i) = S.current i
      linarith
    · funext i
      have hF := hfaraday i
      have hA := hampere i
      simp only [faradayResidual] at hF
      simp only [ampereResidual] at hA
      change (P.curlE i + P.dtB i) - (P.curlB i - P.dtE i) = -S.current i
      linarith
    · simp [derivativeReadout, sourceReadout, hdivE, hdivB]

end InfoGeometry.Canonical.ZornMaxwellSourceReadout
