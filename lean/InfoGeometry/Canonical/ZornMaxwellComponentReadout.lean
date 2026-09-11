import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Component Maxwell readout for the corrected Zorn signs

This owner is a finite component theorem.  It packages the two independent
vector residuals (Ampère and Faraday) into the two off-diagonal Zorn channels,
and the two scalar residuals into the diagonal channels.  It does not assert
that these components arise from a differential operator; that requires the
separate derivative-calculus owner.
-/

namespace InfoGeometry.Canonical.ZornMaxwellComponentReadout

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVec3
open InfoGeometry.Algebra.ZornVectorMatrix

abbrev Vec3 := ZornVec3 ℝ
abbrev ZM := ZornVectorMatrix ℝ

structure MaxwellComponents where
  rho : ℝ
  current : Vec3
  divE : ℝ
  divB : ℝ
  dtE : Vec3
  dtB : Vec3
  curlE : Vec3
  curlB : Vec3

def ampereResidual (P : MaxwellComponents) : Vec3 :=
  fun i => P.curlB i - P.dtE i

def faradayResidual (P : MaxwellComponents) : Vec3 :=
  fun i => P.curlE i + P.dtB i

def derivativeReadout (P : MaxwellComponents) : ZM :=
  ⟨P.divE - P.divB,
    fun i => ampereResidual P i + faradayResidual P i,
    fun i => faradayResidual P i - ampereResidual P i,
    P.divE + P.divB⟩

def currentReadout (P : MaxwellComponents) : ZM :=
  ⟨P.rho, P.current, fun i => -P.current i, P.rho⟩

def MaxwellLaws (P : MaxwellComponents) : Prop :=
  P.divE = P.rho ∧
    P.divB = 0 ∧
    (∀ i, faradayResidual P i = 0) ∧
    (∀ i, ampereResidual P i = P.current i)

theorem derivativeReadout_eq_current_iff
    (P : MaxwellComponents) :
    derivativeReadout P = currentReadout P ↔ MaxwellLaws P := by
  constructor
  · intro h
    have ha : P.divE - P.divB = P.rho := by
      exact congrArg (fun X : ZM => X.a) h
    have hb : P.divE + P.divB = P.rho := by
      exact congrArg (fun X : ZM => X.b) h
    have hdivE : P.divE = P.rho := by linarith
    have hdivB : P.divB = 0 := by linarith
    have huv (i : Fin 3) :
        ampereResidual P i + faradayResidual P i = P.current i := by
      exact congrArg (fun X : ZM => X.v i) h
    have hw (i : Fin 3) :
        faradayResidual P i - ampereResidual P i = -P.current i := by
      exact congrArg (fun X : ZM => X.w i) h
    refine ⟨hdivE, hdivB, ?_, ?_⟩
    · intro i
      linarith [huv i, hw i]
    · intro i
      linarith [huv i, hw i]
  · rintro ⟨hdivE, hdivB, hfaraday, hampere⟩
    apply ZornVectorMatrix.ext
    · simp [derivativeReadout, currentReadout, hdivE, hdivB]
    · funext i
      have hF := hfaraday i
      have hA := hampere i
      simp only [faradayResidual] at hF
      simp only [ampereResidual] at hA
      change (P.curlB i - P.dtE i) + (P.curlE i + P.dtB i) = P.current i
      linarith
    · funext i
      have hF := hfaraday i
      have hA := hampere i
      simp only [faradayResidual] at hF
      simp only [ampereResidual] at hA
      change (P.curlE i + P.dtB i) - (P.curlB i - P.dtE i) = -P.current i
      linarith
    · simp [derivativeReadout, currentReadout, hdivE, hdivB]

end InfoGeometry.Canonical.ZornMaxwellComponentReadout
