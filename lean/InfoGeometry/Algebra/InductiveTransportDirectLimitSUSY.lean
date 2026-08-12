import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
import InfoGeometry.Canonical.ChiralSuperderivationColimit

/-!
# Inductive transport of SUSY superbrackets to a direct limit

This file is a thin, named facade over the finite and direct-limit
superclosure owner lemmas.

It packages the common SUSY use case:

* a one-step chain of semirings;
* coherent finite-stage data `Q`, `R`, `H`, and `Z`;
* a stage-zero odd-odd relation `{Q₀,R₀}=H₀+Z₀`;
* optional square-zero data `Q₀²=0`;
* canonical images in the algebraic direct limit.

The direct limit itself and its universal property are supplied by
`DirectLimitSuperClosureLemmas`.  No analytic completion, topology, or
physics-specific structure is asserted here.
-/

noncomputable section

namespace InfoGeometry.Algebra.InductiveTransportDirectLimitSUSY

open InfoGeometry.Algebra.InductiveSuperClosureLemmas
open DirectLimitSuperClosureLemmas
open InfoGeometry.Canonical.ChiralSuperderivationColimit

universe u

variable {Stage : Nat → Type u} [∀ n : Nat, Semiring (Stage n)]

/-- The algebraic direct limit of a one-step semiring chain. -/
abbrev Limit
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1)) : Type u :=
  DirectLimitSuperClosure bond

/-- Canonical image of stage `n` in the algebraic direct limit. -/
abbrev limitOf
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (n : Nat) : Stage n →+* Limit bond :=
  directLimitOf bond n

/--
Finite-stage transport of a square-zero supercharge.

The step hypotheses use the source-facing orientation
`Q (n+1) = bond n (Q n)`.
-/
theorem nilpotent_transport_induction
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (Q : ∀ n : Nat, Stage n)
    (hQ0 : Q 0 * Q 0 = 0)
    (hQstep : ∀ n : Nat, Q (n + 1) = bond n (Q n)) :
    ∀ n : Nat, Q n * Q n = 0 :=
  squareZero_all bond Q hQ0 (fun n => (hQstep n).symm)

/--
Finite-stage transport of the mixed odd-odd SUSY relation
`{Q,R}=H+Z`.
-/
theorem superbracket_transport_induction
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (Q R H Z : ∀ n : Nat, Stage n)
    (hinit : anticommutator (Q 0) (R 0) = H 0 + Z 0)
    (hQstep : ∀ n : Nat, Q (n + 1) = bond n (Q n))
    (hRstep : ∀ n : Nat, R (n + 1) = bond n (R n))
    (hHstep : ∀ n : Nat, H (n + 1) = bond n (H n))
    (hZstep : ∀ n : Nat, Z (n + 1) = bond n (Z n)) :
    ∀ n : Nat, anticommutator (Q n) (R n) = H n + Z n :=
  mixedSuperClosure_all bond Q R H Z hinit
    (fun n => (hQstep n).symm)
    (fun n => (hRstep n).symm)
    (fun n => (hHstep n).symm)
    (fun n => (hZstep n).symm)

/--
Coherent finite-stage data have a stage-independent canonical image in the
direct limit.
-/
theorem limit_image_eq_initial
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (F : ∀ n : Nat, Stage n)
    (hFstep : ∀ n : Nat, F (n + 1) = bond n (F n)) :
    ∀ n : Nat, limitOf bond n (F n) = limitOf bond 0 (F 0) :=
  directLimitOf_eq_zero_stage bond F (fun n => (hFstep n).symm)

/--
Square-zero transport on every canonical image in the algebraic direct limit.
-/
theorem nilpotent_preserved_at_directLimit_all
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (Q : ∀ n : Nat, Stage n)
    (hQ0 : Q 0 * Q 0 = 0)
    (hQstep : ∀ n : Nat, Q (n + 1) = bond n (Q n)) :
    ∀ n : Nat, limitOf bond n (Q n) * limitOf bond n (Q n) = 0 :=
  directLimit_squareZero_all bond Q hQ0 (fun n => (hQstep n).symm)

/--
The mixed odd-odd SUSY relation holds on every canonical finite-stage image
inside the algebraic direct limit.
-/
theorem superbracket_preserved_at_directLimit_all
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (Q R H Z : ∀ n : Nat, Stage n)
    (hinit : anticommutator (Q 0) (R 0) = H 0 + Z 0)
    (hQstep : ∀ n : Nat, Q (n + 1) = bond n (Q n))
    (hRstep : ∀ n : Nat, R (n + 1) = bond n (R n))
    (hHstep : ∀ n : Nat, H (n + 1) = bond n (H n))
    (hZstep : ∀ n : Nat, Z (n + 1) = bond n (Z n)) :
    ∀ n : Nat,
      anticommutator (limitOf bond n (Q n)) (limitOf bond n (R n)) =
        limitOf bond n (H n) + limitOf bond n (Z n) :=
  directLimit_mixedSuperClosure_all bond Q R H Z hinit
    (fun n => (hQstep n).symm)
    (fun n => (hRstep n).symm)
    (fun n => (hHstep n).symm)
    (fun n => (hZstep n).symm)

/--
The mixed odd-odd SUSY relation in the direct limit, read against the
stage-zero representatives.
-/
theorem superbracket_preserved_at_limit
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (Q R H Z : ∀ n : Nat, Stage n)
    (hinit : anticommutator (Q 0) (R 0) = H 0 + Z 0)
    (hQstep : ∀ n : Nat, Q (n + 1) = bond n (Q n))
    (hRstep : ∀ n : Nat, R (n + 1) = bond n (R n))
    (hHstep : ∀ n : Nat, H (n + 1) = bond n (H n))
    (hZstep : ∀ n : Nat, Z (n + 1) = bond n (Z n)) :
    anticommutator (limitOf bond 0 (Q 0)) (limitOf bond 0 (R 0)) =
      limitOf bond 0 (H 0) + limitOf bond 0 (Z 0) :=
  directLimit_mixedSuperClosure_zeroStage bond Q R H Z hinit
    (fun n => (hQstep n).symm)
    (fun n => (hRstep n).symm)
    (fun n => (hHstep n).symm)
    (fun n => (hZstep n).symm)
    0

/--
Uniqueness of a compatible semiring-hom lift out of the direct limit.

This exposes the universal-property theorem under the SUSY transport module so
users do not need to import the lower-level direct-limit owner file directly.
-/
theorem directLimit_lift_unique
    {Target : Type u} [Semiring Target]
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (toTarget : ∀ n : Nat, Stage n →+* Target)
    (hcone : CompatibleCone bond toTarget)
    (g : Limit bond →+* Target)
    (hg : ∀ n : Nat, g.comp (limitOf bond n) = toTarget n) :
    g = directLimitLift bond toTarget hcone :=
  directLimitLift_unique bond toTarget hcone g hg

/-! ## Colimit-level inner translation derivations -/

section InnerDerivation

variable {RingStage : Nat → Type u} [∀ n : Nat, Ring (RingStage n)]

abbrev RingLimit
    (bond : ∀ n : Nat, RingStage n →+* RingStage (n + 1)) : Type u :=
  DirectLimitSuperClosure bond

/-- The inner derivation generated by the compatible colimit image of a
stagewise even translation generator. -/
def limitInnerDerivation
    (bond : ∀ n : Nat, RingStage n →+* RingStage (n + 1))
    (P : ∀ n : Nat, RingStage n)
    (hP : ∀ n, P (n + 1) = bond n (P n))
    (X : RingLimit bond) : RingLimit bond :=
  directLimitOf bond 0 (P 0) * X - X * directLimitOf bond 0 (P 0)

theorem limitInnerDerivation_leibniz
    (bond : ∀ n : Nat, RingStage n →+* RingStage (n + 1))
    (P : ∀ n : Nat, RingStage n)
    (hP : ∀ n, P (n + 1) = bond n (P n))
    (X Y : RingLimit bond) :
    limitInnerDerivation bond P hP (X * Y) =
      limitInnerDerivation bond P hP X * Y +
        X * limitInnerDerivation bond P hP Y := by
  unfold limitInnerDerivation
  noncomm_ring

theorem limitInnerDerivation_of
    (bond : ∀ n : Nat, RingStage n →+* RingStage (n + 1))
    (P : ∀ n : Nat, RingStage n)
    (hP : ∀ n, P (n + 1) = bond n (P n))
    (n : Nat) (X : RingStage n) :
    limitInnerDerivation bond P hP (directLimitOf bond n X) =
      directLimitOf bond n (P n * X - X * P n) := by
  have hPimage :
      directLimitOf bond 0 (P 0) = directLimitOf bond n (P n) := by
    exact (limit_image_eq_initial bond P hP n).symm
  unfold limitInnerDerivation
  rw [hPimage]
  simp only [map_mul, map_sub]

/-- The odd--odd superderivation bracket descends on every compatible stage
image to the inner derivation generated by the compatible even element. -/
theorem limitOddSuperAnticommutator_of
    (bond : ∀ n : Nat, RingStage n →+* RingStage (n + 1))
    (Qplus Qminus P : ∀ n : Nat, RingStage n)
    (hP : ∀ n, P (n + 1) = bond n (P n))
    (hclosure : ∀ n, Qplus n * Qminus n + Qminus n * Qplus n = P n)
    (n : Nat) (X : RingStage n) (p : Bool) :
    oddSuperAnticommutator
        (limitOf bond n (Qplus n)) (limitOf bond n (Qminus n))
        (limitOf bond n X) p =
      limitInnerDerivation bond P hP (limitOf bond n X) := by
  rw [← map_oddSuperAnticommutator (limitOf bond n)
    (Qplus n) (Qminus n) X p]
  rw [oddSuperAnticommutator_eq_innerDerivation]
  rw [hclosure n, map_innerDerivation]
  rw [limitInnerDerivation_of bond P hP n X]
  simp only [innerDerivation]
  rw [← (directLimitOf bond n).map_mul, ← (directLimitOf bond n).map_mul,
    ← (directLimitOf bond n).map_sub]

def limitTranslationSum
    (bond : ∀ n : Nat, RingStage n →+* RingStage (n + 1))
    (Pplus Pminus : ∀ n : Nat, RingStage n)
    (hplus : ∀ n, Pplus (n + 1) = bond n (Pplus n))
    (hminus : ∀ n, Pminus (n + 1) = bond n (Pminus n))
    (X : RingLimit bond) : RingLimit bond :=
  limitInnerDerivation bond Pplus hplus X +
    limitInnerDerivation bond Pminus hminus X

def limitTranslationDifference
    (bond : ∀ n : Nat, RingStage n →+* RingStage (n + 1))
    (Pplus Pminus : ∀ n : Nat, RingStage n)
    (hplus : ∀ n, Pplus (n + 1) = bond n (Pplus n))
    (hminus : ∀ n, Pminus (n + 1) = bond n (Pminus n))
    (X : RingLimit bond) : RingLimit bond :=
  limitInnerDerivation bond Pplus hplus X -
    limitInnerDerivation bond Pminus hminus X

theorem limitTranslationSum_leibniz
    (bond : ∀ n : Nat, RingStage n →+* RingStage (n + 1))
    (Pplus Pminus : ∀ n : Nat, RingStage n)
    (hplus : ∀ n, Pplus (n + 1) = bond n (Pplus n))
    (hminus : ∀ n, Pminus (n + 1) = bond n (Pminus n))
    (X Y : RingLimit bond) :
    limitTranslationSum bond Pplus Pminus hplus hminus (X * Y) =
      limitTranslationSum bond Pplus Pminus hplus hminus X * Y +
        X * limitTranslationSum bond Pplus Pminus hplus hminus Y := by
  calc
    limitTranslationSum bond Pplus Pminus hplus hminus (X * Y) =
        limitInnerDerivation bond Pplus hplus (X * Y) +
          limitInnerDerivation bond Pminus hminus (X * Y) := rfl
    _ = (limitInnerDerivation bond Pplus hplus X * Y +
          X * limitInnerDerivation bond Pplus hplus Y) +
        (limitInnerDerivation bond Pminus hminus X * Y +
          X * limitInnerDerivation bond Pminus hminus Y) := by
      rw [limitInnerDerivation_leibniz bond Pplus hplus,
        limitInnerDerivation_leibniz bond Pminus hminus]
    _ = limitTranslationSum bond Pplus Pminus hplus hminus X * Y +
        X * limitTranslationSum bond Pplus Pminus hplus hminus Y := by
      simp only [limitTranslationSum, add_mul, mul_add]
      ac_rfl

theorem limitTranslationDifference_leibniz
    (bond : ∀ n : Nat, RingStage n →+* RingStage (n + 1))
    (Pplus Pminus : ∀ n : Nat, RingStage n)
    (hplus : ∀ n, Pplus (n + 1) = bond n (Pplus n))
    (hminus : ∀ n, Pminus (n + 1) = bond n (Pminus n))
    (X Y : RingLimit bond) :
    limitTranslationDifference bond Pplus Pminus hplus hminus (X * Y) =
      limitTranslationDifference bond Pplus Pminus hplus hminus X * Y +
        X * limitTranslationDifference bond Pplus Pminus hplus hminus Y := by
  rw [limitTranslationDifference,
    limitInnerDerivation_leibniz bond Pplus hplus,
    limitInnerDerivation_leibniz bond Pminus hminus]
  unfold limitTranslationDifference
  noncomm_ring

theorem limitTranslationSum_of
    (bond : ∀ n : Nat, RingStage n →+* RingStage (n + 1))
    (Pplus Pminus : ∀ n : Nat, RingStage n)
    (hplus : ∀ n, Pplus (n + 1) = bond n (Pplus n))
    (hminus : ∀ n, Pminus (n + 1) = bond n (Pminus n))
    (n : Nat) (X : RingStage n) :
    limitTranslationSum bond Pplus Pminus hplus hminus (directLimitOf bond n X) =
      directLimitOf bond n
        ((Pplus n * X - X * Pplus n) + (Pminus n * X - X * Pminus n)) := by
  rw [limitTranslationSum, limitInnerDerivation_of,
    limitInnerDerivation_of]
  simp only [map_add]

theorem limitTranslationDifference_of
    (bond : ∀ n : Nat, RingStage n →+* RingStage (n + 1))
    (Pplus Pminus : ∀ n : Nat, RingStage n)
    (hplus : ∀ n, Pplus (n + 1) = bond n (Pplus n))
    (hminus : ∀ n, Pminus (n + 1) = bond n (Pminus n))
    (n : Nat) (X : RingStage n) :
    limitTranslationDifference bond Pplus Pminus hplus hminus
        (directLimitOf bond n X) =
      directLimitOf bond n
        ((Pplus n * X - X * Pplus n) - (Pminus n * X - X * Pminus n)) := by
  rw [limitTranslationDifference, limitInnerDerivation_of,
    limitInnerDerivation_of]
  simp only [map_sub]

end InnerDerivation

end InfoGeometry.Algebra.InductiveTransportDirectLimitSUSY
