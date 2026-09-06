import InfoGeometry.Twistor.ProjectiveNullConfigurationFundamentalGroup

/-!
# Based loop classes on unordered projective-null configurations

This owner records the native Mathlib passage from an actual based path in
unordered projective-null configuration space to its fundamental-group class.
It also translates a path homotopy of the two Artin triple concatenations into
the adjacent Artin relation between their loop classes.

No particular exchange path is selected here.
-/

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullConfigurationExchangeLoop

open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The fundamental-group class represented by one actual based loop in the
unordered projective-null configuration space. -/
def configurationLoopClass
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) (p : Unordered Q n)
    (gamma : @Path (Unordered Q n) (unorderedConfigurationTopology Q n) p p) :
    @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) p := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  exact Path.Homotopic.Quotient.mk gamma

/-- The constant based loop represents the identity element. -/
@[simp] theorem configurationLoopClass_refl
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) (p : Unordered Q n) :
    let _ := unorderedConfigurationTopology Q n
    configurationLoopClass Q n p
        (@Path.refl (Unordered Q n) (unorderedConfigurationTopology Q n) p) =
      (1 : @FundamentalGroup (Unordered Q n)
        (unorderedConfigurationTopology Q n) p) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  rfl

/-- Reversal is read out by the native fundamental-groupoid path quotient. -/
theorem configurationLoopClass_symm_quotient
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) (p : Unordered Q n)
    (gamma : @Path (Unordered Q n) (unorderedConfigurationTopology Q n) p p) :
    let _ := unorderedConfigurationTopology Q n
    configurationLoopClass Q n p gamma.symm =
      (Path.Homotopic.Quotient.mk gamma).symm := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  rfl

/-- Mathlib's endomorphism-group multiplication is categorical composition,
so its path-level readout concatenates the right loop before the left loop. -/
theorem configurationLoopClass_mul
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) (p : Unordered Q n)
    (gamma delta :
      @Path (Unordered Q n) (unorderedConfigurationTopology Q n) p p) :
    configurationLoopClass Q n p gamma * configurationLoopClass Q n p delta =
      configurationLoopClass Q n p
        (@Path.trans (Unordered Q n) (unorderedConfigurationTopology Q n)
          p p p delta gamma) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  change (Path.Homotopic.Quotient.mk delta).trans
      (Path.Homotopic.Quotient.mk gamma) = _
  rw [← Path.Homotopic.Quotient.mk_trans]
  rfl

/-- A loop followed by its reverse contracts to the identity class. -/
theorem configurationLoopClass_mul_symm
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) (p : Unordered Q n)
    (gamma : @Path (Unordered Q n) (unorderedConfigurationTopology Q n) p p) :
    let _ := unorderedConfigurationTopology Q n
    configurationLoopClass Q n p gamma *
        configurationLoopClass Q n p gamma.symm =
      (1 : @FundamentalGroup (Unordered Q n)
        (unorderedConfigurationTopology Q n) p) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  rw [configurationLoopClass_mul]
  change Path.Homotopic.Quotient.mk
      (@Path.trans (Unordered Q n) (unorderedConfigurationTopology Q n)
        p p p gamma.symm gamma) =
    (1 : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) p)
  exact Quotient.sound (Path.Homotopic.symm_trans gamma)

/-- The reverse loop followed by the original loop also contracts. -/
theorem configurationLoopClass_symm_mul
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) (p : Unordered Q n)
    (gamma : @Path (Unordered Q n) (unorderedConfigurationTopology Q n) p p) :
    let _ := unorderedConfigurationTopology Q n
    configurationLoopClass Q n p gamma.symm *
        configurationLoopClass Q n p gamma =
      (1 : @FundamentalGroup (Unordered Q n)
        (unorderedConfigurationTopology Q n) p) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  rw [configurationLoopClass_mul]
  change Path.Homotopic.Quotient.mk
      (@Path.trans (Unordered Q n) (unorderedConfigurationTopology Q n)
        p p p gamma gamma.symm) =
    (1 : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) p)
  exact Quotient.sound (Path.Homotopic.trans_symm gamma)

/-- Path-level adjacent Artin datum for two based loops.  The explicit
concatenation order matches Mathlib's fundamental-group multiplication. -/
def ConfigurationLoopArtin
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) (p : Unordered Q n)
    (gamma0 gamma1 :
      @Path (Unordered Q n) (unorderedConfigurationTopology Q n) p p) : Prop :=
  @Path.Homotopic (Unordered Q n) (unorderedConfigurationTopology Q n)
    p p
    (@Path.trans (Unordered Q n) (unorderedConfigurationTopology Q n)
      p p p gamma0
      (@Path.trans (Unordered Q n) (unorderedConfigurationTopology Q n)
        p p p gamma1 gamma0))
    (@Path.trans (Unordered Q n) (unorderedConfigurationTopology Q n)
      p p p gamma1
      (@Path.trans (Unordered Q n) (unorderedConfigurationTopology Q n)
        p p p gamma0 gamma1))

/-- A homotopy between the two triple loop concatenations supplies the
adjacent Artin relation in the based fundamental group. -/
theorem configurationLoopClasses_artin
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) (p : Unordered Q n)
    (gamma0 gamma1 :
      @Path (Unordered Q n) (unorderedConfigurationTopology Q n) p p)
    (hArtin : ConfigurationLoopArtin Q n p gamma0 gamma1) :
    let _ := unorderedConfigurationTopology Q n
    configurationLoopClass Q n p gamma0 *
          configurationLoopClass Q n p gamma1 *
        configurationLoopClass Q n p gamma0 =
      configurationLoopClass Q n p gamma1 *
          configurationLoopClass Q n p gamma0 *
        configurationLoopClass Q n p gamma1 := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  unfold ConfigurationLoopArtin at hArtin
  rw [configurationLoopClass_mul, configurationLoopClass_mul,
    configurationLoopClass_mul, configurationLoopClass_mul]
  exact Quotient.sound hArtin

/-- Path-level far-commutativity datum for two based loops. -/
def ConfigurationLoopCommute
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) (p : Unordered Q n)
    (gamma0 gamma1 :
      @Path (Unordered Q n) (unorderedConfigurationTopology Q n) p p) : Prop :=
  @Path.Homotopic (Unordered Q n) (unorderedConfigurationTopology Q n)
    p p
    (@Path.trans (Unordered Q n) (unorderedConfigurationTopology Q n)
      p p p gamma1 gamma0)
    (@Path.trans (Unordered Q n) (unorderedConfigurationTopology Q n)
      p p p gamma0 gamma1)

/-- A homotopy between the two concatenations supplies far commutativity in
the based fundamental group. -/
theorem configurationLoopClasses_commute
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) (p : Unordered Q n)
    (gamma0 gamma1 :
      @Path (Unordered Q n) (unorderedConfigurationTopology Q n) p p)
    (hComm : ConfigurationLoopCommute Q n p gamma0 gamma1) :
    let _ := unorderedConfigurationTopology Q n
    configurationLoopClass Q n p gamma0 *
          configurationLoopClass Q n p gamma1 =
      configurationLoopClass Q n p gamma1 *
          configurationLoopClass Q n p gamma0 := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  unfold ConfigurationLoopCommute at hComm
  rw [configurationLoopClass_mul, configurationLoopClass_mul]
  exact Quotient.sound hComm

end InfoGeometry.Twistor.ProjectiveNullConfigurationExchangeLoop
