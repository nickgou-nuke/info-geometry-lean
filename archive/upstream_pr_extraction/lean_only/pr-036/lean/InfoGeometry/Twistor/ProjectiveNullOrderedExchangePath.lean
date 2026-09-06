import InfoGeometry.Twistor.ProjectiveNullConfigurationExchangeLoop

/-!
# Ordered exchange paths descend to unordered based loops

An exchange path on ordered configurations need not be a loop: its endpoint
may be a finite reindexing of its start.  After projection to the unordered
orbit quotient, the two endpoints agree.  This owner implements that standard
ordered-to-unordered passage using Mathlib's native `Path.map` and the already
proved continuity of the quotient projection.

No concrete coordinate exchange path is selected here.
-/

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullOrderedExchangePath

open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationExchangeLoop
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- An ordered path ending at a reindexing of its initial configuration
descends to a based loop in unordered configuration space. -/
def orderedExchangeLoop
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) (p : Ordered Q n)
    (sigma : Equiv.Perm (Fin n))
    (gamma : @Path (Ordered Q n) (orderedConfigurationTopology Q n)
      p (permute Q n sigma p)) :
    @Path (Unordered Q n) (unorderedConfigurationTopology Q n)
      (Quotient.mk' p) (Quotient.mk' p) := by
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  let projected := gamma.map (unorderedProjection_continuous Q n)
  have hend : (Quotient.mk' p : Unordered Q n) =
      Quotient.mk' (permute Q n sigma p) := by
    apply Quotient.sound
    exact ⟨sigma, rfl⟩
  exact projected.cast rfl hend

@[simp] theorem orderedExchangeLoop_apply
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) (p : Ordered Q n)
    (sigma : Equiv.Perm (Fin n))
    (gamma : @Path (Ordered Q n) (orderedConfigurationTopology Q n)
      p (permute Q n sigma p)) (t : unitInterval) :
    orderedExchangeLoop Q n p sigma gamma t = Quotient.mk' (gamma t) := by
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  rfl

/-- The fundamental-group class of an ordered exchange path after descent to
the unordered projective-null configuration space. -/
def orderedExchangeLoopClass
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) (p : Ordered Q n)
    (sigma : Equiv.Perm (Fin n))
    (gamma : @Path (Ordered Q n) (orderedConfigurationTopology Q n)
      p (permute Q n sigma p)) :
    @FundamentalGroup (Unordered Q n) (unorderedConfigurationTopology Q n)
      (Quotient.mk' p) :=
  configurationLoopClass Q n (Quotient.mk' p)
    (orderedExchangeLoop Q n p sigma gamma)

/-- The identity reindexing and constant ordered path descend to the constant
unordered loop. -/
@[simp] theorem orderedExchangeLoop_refl
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) (p : Ordered Q n) :
    let _inst : TopologicalSpace (Ordered Q n) :=
      orderedConfigurationTopology Q n
    let _inst' : TopologicalSpace (Unordered Q n) :=
      unorderedConfigurationTopology Q n
    orderedExchangeLoop Q n p (Equiv.refl (Fin n))
        (@Path.refl (Ordered Q n) (orderedConfigurationTopology Q n) p) =
      @Path.refl (Unordered Q n) (unorderedConfigurationTopology Q n)
        (Quotient.mk' p) := by
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  apply (Path.ext_iff).2
  exact funext fun t => by
    rw [orderedExchangeLoop_apply]
    rfl

/-- The identity ordered exchange represents the identity element of the
unordered fundamental group. -/
@[simp] theorem orderedExchangeLoopClass_refl
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) (p : Ordered Q n) :
    let _inst : TopologicalSpace (Ordered Q n) :=
      orderedConfigurationTopology Q n
    let _inst' : TopologicalSpace (Unordered Q n) :=
      unorderedConfigurationTopology Q n
    orderedExchangeLoopClass Q n p (Equiv.refl (Fin n))
        (@Path.refl (Ordered Q n) (orderedConfigurationTopology Q n) p) =
      (1 : @FundamentalGroup (Unordered Q n)
        (unorderedConfigurationTopology Q n) (Quotient.mk' p)) := by
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  rw [orderedExchangeLoopClass, orderedExchangeLoop_refl]
  exact configurationLoopClass_refl Q n (Quotient.mk' p)

/-- Multiplication of two descended ordered paths is the native concatenation
of their unordered loop images. -/
theorem orderedExchangeLoopClass_mul
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) (p : Ordered Q n)
    (sigma tau : Equiv.Perm (Fin n))
    (gamma : @Path (Ordered Q n) (orderedConfigurationTopology Q n)
      p (permute Q n sigma p))
    (delta : @Path (Ordered Q n) (orderedConfigurationTopology Q n)
      p (permute Q n tau p)) :
    let _inst : TopologicalSpace (Ordered Q n) :=
      orderedConfigurationTopology Q n
    let _inst' : TopologicalSpace (Unordered Q n) :=
      unorderedConfigurationTopology Q n
    orderedExchangeLoopClass Q n p sigma gamma *
          orderedExchangeLoopClass Q n p tau delta =
      configurationLoopClass Q n (Quotient.mk' p)
        (@Path.trans (Unordered Q n) (unorderedConfigurationTopology Q n)
          (Quotient.mk' p) (Quotient.mk' p) (Quotient.mk' p)
          (orderedExchangeLoop Q n p tau delta)
          (orderedExchangeLoop Q n p sigma gamma)) := by
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  unfold orderedExchangeLoopClass
  exact configurationLoopClass_mul Q n (Quotient.mk' p)
    (orderedExchangeLoop Q n p sigma gamma)
    (orderedExchangeLoop Q n p tau delta)

/-- Homotopic descended paths represent the same ordered-exchange class. -/
theorem orderedExchangeLoopClass_eq_of_homotopic
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) (p : Ordered Q n)
    (sigma tau : Equiv.Perm (Fin n))
    (gamma : @Path (Ordered Q n) (orderedConfigurationTopology Q n)
      p (permute Q n sigma p))
    (delta : @Path (Ordered Q n) (orderedConfigurationTopology Q n)
      p (permute Q n tau p))
    (h : @Path.Homotopic (Unordered Q n)
      (unorderedConfigurationTopology Q n)
      (Quotient.mk' p) (Quotient.mk' p)
      (orderedExchangeLoop Q n p sigma gamma)
      (orderedExchangeLoop Q n p tau delta)) :
    let _inst : TopologicalSpace (Ordered Q n) :=
      orderedConfigurationTopology Q n
    let _inst' : TopologicalSpace (Unordered Q n) :=
      unorderedConfigurationTopology Q n
    orderedExchangeLoopClass Q n p sigma gamma =
      orderedExchangeLoopClass Q n p tau delta := by
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  unfold orderedExchangeLoopClass configurationLoopClass
  exact Quotient.sound h

end InfoGeometry.Twistor.ProjectiveNullOrderedExchangePath
