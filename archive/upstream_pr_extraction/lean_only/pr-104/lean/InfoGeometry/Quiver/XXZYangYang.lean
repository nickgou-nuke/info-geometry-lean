import InfoGeometry.Quiver.BetheAnsatzXXZ
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The local XXZ Yang--Yang potential

The former `YangYangFunction` structure stored a complex number together with
an unrelated proposition saying that criticality gives the Bethe equations.
This file replaces that wrapper by an actual holomorphic potential and a
kernel-checked derivative theorem.

For `L(z) = z log z - z`, one has `L'(z) = log z` away from zero.  Applying
this primitive to every numerator and denominator in the multiplicative XXZ
Bethe equation gives a local Yang--Yang potential for one root, with all other
roots held fixed.

Because the complex logarithm has branches, derivative zero gives the
*additive logarithmic Bethe equation*.  Recovering a biconditional with the
multiplicative equation requires explicit branch/integrality data and is not
silently asserted here.
-/

noncomputable section

namespace KoroteevZeitlin.Bethe.XXZYangYang

open Complex BigOperators Finset

/-- Standard holomorphic primitive of the complex logarithm. -/
def logPrimitive (z : ℂ) : ℂ :=
  z * Complex.log z - z

/-- Away from the logarithmic divisor, `z log z - z` has derivative `log z`. -/
theorem hasDerivAt_logPrimitive {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt logPrimitive (Complex.log z) z := by
  have h :=
    ((hasDerivAt_id z).mul (Complex.hasDerivAt_log hz)).sub
      (hasDerivAt_id z)
  convert h using 1 <;> simp [logPrimitive, Complex.slitPlane_ne_zero hz]

/--
Normalized affine logarithmic primitive.  The factor `q⁻¹` cancels the
derivative of the affine argument `q*x-c`.
-/
def normalizedAffineLogPrimitive (q c x : ℂ) : ℂ :=
  q⁻¹ * logPrimitive (q * x - c)

theorem hasDerivAt_normalizedAffineLogPrimitive
    {q c x : ℂ} (hq : q ≠ 0) (hx : q * x - c ∈ Complex.slitPlane) :
    HasDerivAt (normalizedAffineLogPrimitive q c)
      (Complex.log (q * x - c)) x := by
  have harg : HasDerivAt (fun y : ℂ => q * y - c) q x := by
    simpa using ((hasDerivAt_id x).const_mul q).sub_const c
  have hcomp :
      HasDerivAt (fun y : ℂ => logPrimitive (q * y - c))
        (Complex.log (q * x - c) * q) x :=
    by
      simpa only [Function.comp_apply] using
        (hasDerivAt_logPrimitive hx).comp x harg
  have hscaled := hcomp.const_mul q⁻¹
  simpa [normalizedAffineLogPrimitive, hq, mul_assoc, mul_left_comm,
    mul_comm] using hscaled

/-- Unnormalized affine primitive with unit slope. -/
def translatedLogPrimitive (c x : ℂ) : ℂ :=
  logPrimitive (x - c)

theorem hasDerivAt_translatedLogPrimitive
    {c x : ℂ} (hx : x - c ∈ Complex.slitPlane) :
    HasDerivAt (translatedLogPrimitive c)
      (Complex.log (x - c)) x := by
  have harg : HasDerivAt (fun y : ℂ => y - c) 1 x :=
    (hasDerivAt_id x).sub_const c
  simpa [translatedLogPrimitive, Function.comp_def] using
    (hasDerivAt_logPrimitive hx).comp x harg

variable {r : ℕ}

/--
Local Yang--Yang potential for the root `(a,j)`, viewed as a function of a
replacement coordinate `x`.  The `erase j` interaction term exactly matches
the omission of the self-factor in `BetheEquation`.
-/
def localPotential
    (B : XXZBetheData r)
    (s : BetheRoots B)
    (sites : SiteParams B)
    (a : Fin r) (j : Fin (B.dimVec a))
    (x : ℂ) : ℂ :=
  (∑ i ∈ (Finset.univ : Finset (Fin (B.dimVec a))).erase j,
      (normalizedAffineLogPrimitive B.hbar (s a i) x -
        translatedLogPrimitive (B.hbar * s a i) x)) +
    (∑ m : Fin B.numSites,
      (translatedLogPrimitive (sites m) x -
        normalizedAffineLogPrimitive B.hbar (sites m) x)) -
    x * Complex.log (B.kahler a)

/--
The historical `YangYangFunction` name, now denoting an actual complex
function rather than a record containing an unrelated proposition.
-/
abbrev YangYangFunction := ℂ → ℂ

/-- The genuine local Yang--Yang function attached to a chosen Bethe root. -/
def yangYangFunction
    (B : XXZBetheData r)
    (s : BetheRoots B)
    (sites : SiteParams B)
    (a : Fin r) (j : Fin (B.dimVec a)) :
    YangYangFunction :=
  localPotential B s sites a j

@[simp]
theorem yangYangFunction_apply
    (B : XXZBetheData r)
    (s : BetheRoots B)
    (sites : SiteParams B)
    (a : Fin r) (j : Fin (B.dimVec a))
    (x : ℂ) :
    yangYangFunction B s sites a j x =
      localPotential B s sites a j x :=
  rfl

/-- Additive logarithmic residual of the `(a,j)` XXZ Bethe equation. -/
def logarithmicResidual
    (B : XXZBetheData r)
    (s : BetheRoots B)
    (sites : SiteParams B)
    (a : Fin r) (j : Fin (B.dimVec a))
    (x : ℂ) : ℂ :=
  (∑ i ∈ (Finset.univ : Finset (Fin (B.dimVec a))).erase j,
      (Complex.log (B.hbar * x - s a i) -
        Complex.log (x - B.hbar * s a i))) +
    (∑ m : Fin B.numSites,
      (Complex.log (x - sites m) -
        Complex.log (B.hbar * x - sites m))) -
    Complex.log (B.kahler a)

/--
The local Yang--Yang potential differentiates to the additive logarithmic
Bethe residual.  All hypotheses are precisely the avoided logarithmic
divisors; no analytic regularity is stored in a wrapper.
-/
theorem hasDerivAt_localPotential
    (B : XXZBetheData r)
    (s : BetheRoots B)
    (sites : SiteParams B)
    (a : Fin r) (j : Fin (B.dimVec a))
    (x : ℂ)
    (hSameNum : ∀ i, i ∈
        (Finset.univ : Finset (Fin (B.dimVec a))).erase j →
      B.hbar * x - s a i ∈ Complex.slitPlane)
    (hSameDen : ∀ i, i ∈
        (Finset.univ : Finset (Fin (B.dimVec a))).erase j →
      x - B.hbar * s a i ∈ Complex.slitPlane)
    (hSiteNum : ∀ m : Fin B.numSites, x - sites m ∈ Complex.slitPlane)
    (hSiteDen : ∀ m : Fin B.numSites, B.hbar * x - sites m ∈ Complex.slitPlane) :
    HasDerivAt (localPotential B s sites a j)
      (logarithmicResidual B s sites a j x) x := by
  have hSame :
      HasDerivAt
        (fun y : ℂ =>
          ∑ i ∈ (Finset.univ : Finset (Fin (B.dimVec a))).erase j,
            (normalizedAffineLogPrimitive B.hbar (s a i) y -
              translatedLogPrimitive (B.hbar * s a i) y))
        (∑ i ∈ (Finset.univ : Finset (Fin (B.dimVec a))).erase j,
          (Complex.log (B.hbar * x - s a i) -
            Complex.log (x - B.hbar * s a i))) x := by
    refine HasDerivAt.fun_sum (u :=
      (Finset.univ : Finset (Fin (B.dimVec a))).erase j) ?_
    intro i hi
    exact (hasDerivAt_normalizedAffineLogPrimitive B.hbar_ne_zero
      (hSameNum i hi)).sub
        (hasDerivAt_translatedLogPrimitive (hSameDen i hi))
  have hSites :
      HasDerivAt
        (fun y : ℂ =>
          ∑ m : Fin B.numSites,
            (translatedLogPrimitive (sites m) y -
              normalizedAffineLogPrimitive B.hbar (sites m) y))
        (∑ m : Fin B.numSites,
          (Complex.log (x - sites m) -
            Complex.log (B.hbar * x - sites m))) x := by
    refine HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin B.numSites))) ?_
    intro m hm
    exact (hasDerivAt_translatedLogPrimitive (hSiteNum m)).sub
      (hasDerivAt_normalizedAffineLogPrimitive B.hbar_ne_zero (hSiteDen m))
  have hTwist :
      HasDerivAt (fun y : ℂ => y * Complex.log (B.kahler a))
        (Complex.log (B.kahler a)) x :=
    by simpa using (hasDerivAt_id x).mul_const (Complex.log (B.kahler a))
  unfold localPotential logarithmicResidual
  exact (hSame.add hSites).sub hTwist

/-- A root is Yang--Yang critical exactly when its native complex derivative vanishes. -/
def IsLocalCriticalPoint
    (B : XXZBetheData r)
    (s : BetheRoots B)
    (sites : SiteParams B)
    (a : Fin r) (j : Fin (B.dimVec a)) : Prop :=
  HasDerivAt (localPotential B s sites a j) 0 (s a j)

/--
Under the divisor hypotheses, local criticality is equivalent to vanishing of
the additive logarithmic Bethe residual.
-/
theorem isLocalCriticalPoint_iff_logarithmicResidual_eq_zero
    (B : XXZBetheData r)
    (s : BetheRoots B)
    (sites : SiteParams B)
    (a : Fin r) (j : Fin (B.dimVec a))
    (hSameNum : ∀ i, i ∈
        (Finset.univ : Finset (Fin (B.dimVec a))).erase j →
      B.hbar * s a j - s a i ∈ Complex.slitPlane)
    (hSameDen : ∀ i, i ∈
        (Finset.univ : Finset (Fin (B.dimVec a))).erase j →
      s a j - B.hbar * s a i ∈ Complex.slitPlane)
    (hSiteNum : ∀ m : Fin B.numSites, s a j - sites m ∈ Complex.slitPlane)
    (hSiteDen : ∀ m : Fin B.numSites, B.hbar * s a j - sites m ∈ Complex.slitPlane) :
    IsLocalCriticalPoint B s sites a j ↔
      logarithmicResidual B s sites a j (s a j) = 0 := by
  have hderiv := hasDerivAt_localPotential B s sites a j (s a j)
    hSameNum hSameDen hSiteNum hSiteDen
  constructor
  · intro hcrit
    exact hderiv.unique hcrit
  · intro hzero
    rw [hzero] at hderiv
    exact hderiv

/--
Multiplicative XXZ residual in the erased-self-factor presentation naturally
produced by exponentiating the Yang--Yang derivative.
-/
def multiplicativeResidual
    (B : XXZBetheData r)
    (s : BetheRoots B)
    (sites : SiteParams B)
    (a : Fin r) (j : Fin (B.dimVec a))
    (x : ℂ) : ℂ :=
  (∏ i ∈ (Finset.univ : Finset (Fin (B.dimVec a))).erase j,
      (B.hbar * x - s a i) / (x - B.hbar * s a i)) *
    (∏ m : Fin B.numSites,
      (x - sites m) / (B.hbar * x - sites m))

/--
Exponentiating the logarithmic residual gives the multiplicative residual
divided by the twist.  This direction is branch-independent.
-/
theorem exp_logarithmicResidual
    (B : XXZBetheData r)
    (s : BetheRoots B)
    (sites : SiteParams B)
    (a : Fin r) (j : Fin (B.dimVec a))
    (x : ℂ)
    (hSameNum : ∀ i, i ∈
        (Finset.univ : Finset (Fin (B.dimVec a))).erase j →
      B.hbar * x - s a i ∈ Complex.slitPlane)
    (hSameDen : ∀ i, i ∈
        (Finset.univ : Finset (Fin (B.dimVec a))).erase j →
      x - B.hbar * s a i ∈ Complex.slitPlane)
    (hSiteNum : ∀ m : Fin B.numSites, x - sites m ∈ Complex.slitPlane)
    (hSiteDen : ∀ m : Fin B.numSites, B.hbar * x - sites m ∈ Complex.slitPlane)
    (hTwist : B.kahler a ≠ 0) :
    Complex.exp (logarithmicResidual B s sites a j x) =
      multiplicativeResidual B s sites a j x / B.kahler a := by
  have hSameExp :
      Complex.exp
          (∑ i ∈ (Finset.univ : Finset (Fin (B.dimVec a))).erase j,
            (Complex.log (B.hbar * x - s a i) -
              Complex.log (x - B.hbar * s a i))) =
        ∏ i ∈ (Finset.univ : Finset (Fin (B.dimVec a))).erase j,
          (B.hbar * x - s a i) / (x - B.hbar * s a i) := by
    rw [Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Complex.exp_sub,
      Complex.exp_log (Complex.slitPlane_ne_zero (hSameNum i hi)),
      Complex.exp_log (Complex.slitPlane_ne_zero (hSameDen i hi))]
  have hSiteExp :
      Complex.exp
          (∑ m : Fin B.numSites,
            (Complex.log (x - sites m) -
              Complex.log (B.hbar * x - sites m))) =
        ∏ m : Fin B.numSites,
          (x - sites m) / (B.hbar * x - sites m) := by
    rw [Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro m hm
    rw [Complex.exp_sub,
      Complex.exp_log (Complex.slitPlane_ne_zero (hSiteNum m)),
      Complex.exp_log (Complex.slitPlane_ne_zero (hSiteDen m))]
  rw [logarithmicResidual, Complex.exp_sub, Complex.exp_add,
    hSameExp, hSiteExp, Complex.exp_log hTwist]
  rfl

/--
Every local Yang--Yang critical point satisfies the multiplicative XXZ Bethe
equation in erased-self-factor form.

The converse needs a choice of logarithmic branch, since exponentiation has
kernel `2*pi*I*Z`.
-/
theorem multiplicativeResidual_eq_kahler_of_isLocalCriticalPoint
    (B : XXZBetheData r)
    (s : BetheRoots B)
    (sites : SiteParams B)
    (a : Fin r) (j : Fin (B.dimVec a))
    (hSameNum : ∀ i, i ∈
        (Finset.univ : Finset (Fin (B.dimVec a))).erase j →
      B.hbar * s a j - s a i ∈ Complex.slitPlane)
    (hSameDen : ∀ i, i ∈
        (Finset.univ : Finset (Fin (B.dimVec a))).erase j →
      s a j - B.hbar * s a i ∈ Complex.slitPlane)
    (hSiteNum : ∀ m : Fin B.numSites, s a j - sites m ∈ Complex.slitPlane)
    (hSiteDen : ∀ m : Fin B.numSites, B.hbar * s a j - sites m ∈ Complex.slitPlane)
    (hTwist : B.kahler a ≠ 0)
    (hCritical : IsLocalCriticalPoint B s sites a j) :
    multiplicativeResidual B s sites a j (s a j) = B.kahler a := by
  have hLog :
      logarithmicResidual B s sites a j (s a j) = 0 :=
    (isLocalCriticalPoint_iff_logarithmicResidual_eq_zero
      B s sites a j hSameNum hSameDen hSiteNum hSiteDen).1 hCritical
  have hExp := exp_logarithmicResidual B s sites a j (s a j)
    hSameNum hSameDen hSiteNum hSiteDen hTwist
  rw [hLog, Complex.exp_zero] at hExp
  exact (div_eq_one_iff_eq hTwist).1 hExp.symm

/--
Historical `critical_is_bethe` functionality, now a theorem about the genuine
Yang--Yang derivative.  Criticality implies the multiplicative XXZ equation
under exactly the logarithmic-divisor and nonzero-twist hypotheses.
-/
theorem critical_is_bethe
    (B : XXZBetheData r)
    (s : BetheRoots B)
    (sites : SiteParams B)
    (a : Fin r) (j : Fin (B.dimVec a))
    (hSameNum : ∀ i, i ∈
        (Finset.univ : Finset (Fin (B.dimVec a))).erase j →
      B.hbar * s a j - s a i ∈ Complex.slitPlane)
    (hSameDen : ∀ i, i ∈
        (Finset.univ : Finset (Fin (B.dimVec a))).erase j →
      s a j - B.hbar * s a i ∈ Complex.slitPlane)
    (hSiteNum : ∀ m : Fin B.numSites, s a j - sites m ∈ Complex.slitPlane)
    (hSiteDen : ∀ m : Fin B.numSites, B.hbar * s a j - sites m ∈ Complex.slitPlane)
    (hTwist : B.kahler a ≠ 0)
    (hCritical :
      HasDerivAt (yangYangFunction B s sites a j) 0 (s a j)) :
    multiplicativeResidual B s sites a j (s a j) =
      B.kahler a :=
  multiplicativeResidual_eq_kahler_of_isLocalCriticalPoint
    B s sites a j hSameNum hSameDen hSiteNum hSiteDen hTwist hCritical

end KoroteevZeitlin.Bethe.XXZYangYang
