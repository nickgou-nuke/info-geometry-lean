import InfoGeometry.Twistor.ProjectiveNullConfigurationCovering
import InfoGeometry.Twistor.ProjectiveNullConfigurationFiberEquiv
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Deck-permutation monodromy of projective-null configurations

The finite permutation quotient of ordered projective-null configurations is
already known to be a covering under explicit local compactness and Hausdorff
hypotheses.  This owner applies Mathlib's homotopy-invariant covering
monodromy to a based loop class and reads the lifted endpoint as the unique
permutation of the chosen ordered base configuration.

This is genuine covering-space deck monodromy.  It does not identify the
fundamental group with an Artin or spherical braid group, select elementary
exchange loops, construct conformal-block monodromy, or assert an anyon
interpretation.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullConfigurationDeckMonodromy

open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationCovering
open InfoGeometry.Twistor.ProjectiveNullConfigurationFiberEquiv
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-! ## Generic covering-monodromy calculus -/

/-- Covering monodromy respects path concatenation: lifting the concatenated
class is the same as lifting the first class and then lifting the second from
the resulting point. -/
theorem coveringMonodromy_trans_apply
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} (cov : IsCoveringMap f) {x y z : X}
    (gamma : Path.Homotopic.Quotient x y)
    (delta : Path.Homotopic.Quotient y z)
    (e : {q : E // f q = x}) :
    cov.monodromy (gamma.trans delta) e =
      cov.monodromy delta (cov.monodromy gamma e) := by
  refine Quotient.inductionOn gamma ?_
  intro gamma
  refine Quotient.inductionOn delta ?_
  intro delta
  apply Subtype.ext
  change (cov.liftPath (↑(gamma.trans delta)) e _) 1 = _
  rw [cov.liftPath_trans e.property.symm gamma delta]
  simp only [IsCoveringMap.monodromy, Quotient.lift_mk]
  simp

/-- A based loop class acts invertibly on the fiber of a covering map. -/
noncomputable def coveringMonodromyEquiv
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} (cov : IsCoveringMap f) {x : X}
    (gamma : FundamentalGroup X x) :
    {q : E // f q = x} ≃ {q : E // f q = x} where
  toFun := cov.monodromy gamma
  invFun := cov.monodromy gamma.symm
  left_inv e := by
    rw [← coveringMonodromy_trans_apply cov gamma gamma.symm e,
      Path.Homotopic.Quotient.trans_symm, cov.monodromy_refl]
    rfl
  right_inv e := by
    rw [← coveringMonodromy_trans_apply cov gamma.symm gamma e,
      Path.Homotopic.Quotient.symm_trans, cov.monodromy_refl]
    rfl

/-- Native covering monodromy as a permutation representation of the based
fundamental group on the covering fiber.  The proof follows Mathlib's
categorical multiplication convention: the right loop is traversed first. -/
noncomputable def coveringMonodromyRepresentation
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} (cov : IsCoveringMap f) (x : X) :
    FundamentalGroup X x →* Equiv.Perm {q : E // f q = x} where
  toFun := coveringMonodromyEquiv cov
  map_one' := by
    apply Equiv.ext
    intro e
    change cov.monodromy (Path.Homotopic.Quotient.refl x) e = e
    exact congrFun cov.monodromy_refl e
  map_mul' gamma delta := by
    refine Quotient.inductionOn gamma ?_
    intro gamma
    refine Quotient.inductionOn delta ?_
    intro delta
    apply Equiv.ext
    intro e
    change cov.monodromy
        ((Path.Homotopic.Quotient.mk delta).trans
          (Path.Homotopic.Quotient.mk gamma)) e =
      cov.monodromy (Path.Homotopic.Quotient.mk gamma)
        (cov.monodromy (Path.Homotopic.Quotient.mk delta) e)
    exact coveringMonodromy_trans_apply cov
      (Path.Homotopic.Quotient.mk delta)
      (Path.Homotopic.Quotient.mk gamma) e

/-! ## Projective-null configuration readout -/

/-- The quotient covering supplies a literal permutation representation of
the based fundamental group on its finite ordered-configuration fiber. -/
noncomputable def unorderedConfigurationFiberMonodromy
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n) :
    @FundamentalGroup (Unordered Q n)
        (unorderedConfigurationTopology Q n) (Quotient.mk' p) →*
      Equiv.Perm
        {q : Ordered Q n //
          Quotient.mk' q = (Quotient.mk' p : Unordered Q n)} := by
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  exact coveringMonodromyRepresentation
    (unorderedProjection_isQuotientCoveringMap Q n hLC hT2).isCoveringMap
    (Quotient.mk' p)

@[simp] theorem unorderedConfigurationFiberMonodromy_apply
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n)
    (gamma : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) (Quotient.mk' p))
    (q : {r : Ordered Q n //
      Quotient.mk' r = (Quotient.mk' p : Unordered Q n)}) :
    let _ := orderedConfigurationTopology Q n
    let _ := unorderedConfigurationTopology Q n
    unorderedConfigurationFiberMonodromy Q n hLC hT2 p gamma q =
      (unorderedProjection_isQuotientCoveringMap Q n hLC hT2).isCoveringMap.monodromy
        gamma q := by
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  rfl

/-- The finite deck group acts on the ordered fiber over the selected
unordered basepoint. -/
noncomputable def unorderedConfigurationFiberDeckAction
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) (p : Ordered Q n)
    (sigma : Equiv.Perm (Fin n))
    (q : {r : Ordered Q n //
      Quotient.mk' r = (Quotient.mk' p : Unordered Q n)}) :
    {r : Ordered Q n //
      Quotient.mk' r = (Quotient.mk' p : Unordered Q n)} := by
  refine ⟨sigma • q.1, ?_⟩
  calc
    Quotient.mk' (sigma • q.1) = Quotient.mk' q.1 := by
      apply Quotient.sound
      refine ⟨sigma, ?_⟩
      change q.1 = permute Q n sigma (permute Q n sigma.symm q.1)
      rw [permute_comp]
      simp
    _ = Quotient.mk' p := q.2

/-- Covering monodromy commutes with every finite deck reindexing of the
ordered configuration fiber.  This is proved by uniqueness of path lifts,
not postulated as an abstract deck-action field. -/
theorem unorderedConfigurationFiberMonodromy_deck_equivariant
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n)
    (gamma : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) (Quotient.mk' p))
    (sigma : Equiv.Perm (Fin n))
    (q : {r : Ordered Q n //
      Quotient.mk' r = (Quotient.mk' p : Unordered Q n)}) :
    unorderedConfigurationFiberMonodromy Q n hLC hT2 p gamma
        (unorderedConfigurationFiberDeckAction Q n p sigma q) =
      unorderedConfigurationFiberDeckAction Q n p sigma
        (unorderedConfigurationFiberMonodromy Q n hLC hT2 p gamma q) := by
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  let hquot := unorderedProjection_isQuotientCoveringMap Q n hLC hT2
  let cov := hquot.isCoveringMap
  refine Quotient.inductionOn gamma ?_
  intro gamma
  apply Subtype.ext
  have hq0 : (↑gamma : C(unitInterval, Unordered Q n)) 0 = Quotient.mk' q.1 :=
    gamma.source.trans q.2.symm
  have hsproj : Quotient.mk' (sigma • q.1) = (Quotient.mk' p : Unordered Q n) :=
    (unorderedConfigurationFiberDeckAction Q n p sigma q).2
  have hs0 : (↑gamma : C(unitInterval, Unordered Q n)) 0 =
      Quotient.mk' (sigma • q.1) := gamma.source.trans hsproj.symm
  change (cov.liftPath ↑gamma (sigma • q.1) hs0) 1 =
    sigma • (cov.liftPath ↑gamma q.1 hq0) 1
  let deck : @ContinuousMap (Ordered Q n) (Ordered Q n)
      (orderedConfigurationTopology Q n) (orderedConfigurationTopology Q n) :=
    ⟨fun r => sigma • r,
      (orderedPermutationHomeomorph Q n sigma.symm).continuous⟩
  have hlift : deck.comp (cov.liftPath ↑gamma q.1 hq0) =
      cov.liftPath ↑gamma (sigma • q.1) hs0 := by
    apply (cov.eq_liftPath_iff' hs0).2
    constructor
    · funext t
      change Quotient.mk' (sigma • (cov.liftPath ↑gamma q.1 hq0) t) = gamma t
      calc
        Quotient.mk' (sigma • (cov.liftPath ↑gamma q.1 hq0) t) =
            Quotient.mk' ((cov.liftPath ↑gamma q.1 hq0) t) := by
          apply Quotient.sound
          refine ⟨sigma, ?_⟩
          change (cov.liftPath ↑gamma q.1 hq0) t =
            permute Q n sigma
              (permute Q n sigma.symm (cov.liftPath ↑gamma q.1 hq0 t))
          rw [permute_comp]
          simp
        _ = gamma t := congrFun (cov.liftPath_lifts ↑gamma q.1 hq0) t
    · change sigma • (cov.liftPath ↑gamma q.1 hq0) 0 = sigma • q.1
      rw [cov.liftPath_zero]
  exact congrArg (fun f => f 1) hlift.symm

/-- The endpoint in the ordered fiber obtained by lifting a based loop class
in unordered configuration space from the selected ordered basepoint. -/
noncomputable def unorderedCoveringMonodromyEndpoint
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n)
    (gamma : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) (Quotient.mk' p)) : Ordered Q n := by
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  let hquot := unorderedProjection_isQuotientCoveringMap Q n hLC hT2
  let cov := hquot.isCoveringMap
  let base : {q : Ordered Q n // Quotient.mk' q = (Quotient.mk' p : Unordered Q n)} :=
    ⟨p, rfl⟩
  exact (cov.monodromy gamma base).1

/-- The lifted endpoint lies in the permutation orbit of the ordered
basepoint. -/
theorem unorderedCoveringMonodromyEndpoint_mem_orbit
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n)
    (gamma : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) (Quotient.mk' p)) :
    unorderedCoveringMonodromyEndpoint Q n hLC hT2 p gamma ∈
      MulAction.orbit (Equiv.Perm (Fin n)) p := by
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  let hquot := unorderedProjection_isQuotientCoveringMap Q n hLC hT2
  let cov := hquot.isCoveringMap
  let base : {q : Ordered Q n // Quotient.mk' q = (Quotient.mk' p : Unordered Q n)} :=
    ⟨p, rfl⟩
  have hend : Quotient.mk' (unorderedCoveringMonodromyEndpoint Q n hLC hT2 p gamma) =
      (Quotient.mk' p : Unordered Q n) := by
    exact (cov.monodromy gamma base).2
  exact hquot.apply_eq_iff_mem_orbit.mp hend

/-- The unique deck permutation read from the lifted endpoint of a based loop
class.  Homotopy invariance is inherited from Mathlib's covering monodromy,
whose input is already a path-homotopy quotient. -/
noncomputable def unorderedCoveringDeckPermutation
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n)
    (gamma : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) (Quotient.mk' p)) : Equiv.Perm (Fin n) :=
  Classical.choose (MulAction.mem_orbit_iff.mp
    (unorderedCoveringMonodromyEndpoint_mem_orbit Q n hLC hT2 p gamma))

/-- The selected deck permutation sends the ordered basepoint to the lifted
endpoint. -/
theorem unorderedCoveringDeckPermutation_smul
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n)
    (gamma : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) (Quotient.mk' p)) :
    unorderedCoveringDeckPermutation Q n hLC hT2 p gamma • p =
      unorderedCoveringMonodromyEndpoint Q n hLC hT2 p gamma := by
  exact Classical.choose_spec (MulAction.mem_orbit_iff.mp
    (unorderedCoveringMonodromyEndpoint_mem_orbit Q n hLC hT2 p gamma))

/-- Freeness of the permutation action makes the deck readout uniquely
determined by its endpoint action. -/
theorem unorderedCoveringDeckPermutation_unique
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n)
    (gamma : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) (Quotient.mk' p))
    (sigma : Equiv.Perm (Fin n))
    (hsigma : sigma • p =
      unorderedCoveringMonodromyEndpoint Q n hLC hT2 p gamma) :
    sigma = unorderedCoveringDeckPermutation Q n hLC hT2 p gamma := by
  exact IsCancelSMul.right_cancel sigma
    (unorderedCoveringDeckPermutation Q n hLC hT2 p gamma) p
    (hsigma.trans
      (unorderedCoveringDeckPermutation_smul Q n hLC hT2 p gamma).symm)

/-- The constant based loop has trivial deck-permutation readout. -/
theorem unorderedCoveringDeckPermutation_one
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n) :
    unorderedCoveringDeckPermutation Q n hLC hT2 p 1 = 1 := by
  symm
  apply unorderedCoveringDeckPermutation_unique Q n hLC hT2 p 1 1
  change p = unorderedCoveringMonodromyEndpoint Q n hLC hT2 p 1
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  change p =
    ((unorderedProjection_isQuotientCoveringMap Q n hLC hT2).isCoveringMap.monodromy
      (Path.Homotopic.Quotient.refl (Quotient.mk' p))
      ⟨p, rfl⟩).1
  rw [(unorderedProjection_isQuotientCoveringMap Q n hLC hT2).isCoveringMap.monodromy_refl]
  rfl

/-- With Mathlib's fundamental-group multiplication convention, the deck
permutation readout is anti-multiplicative: the right loop is traversed first. -/
theorem unorderedCoveringDeckPermutation_mul
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n)
    (gamma delta : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) (Quotient.mk' p)) :
    unorderedCoveringDeckPermutation Q n hLC hT2 p (gamma * delta) =
      unorderedCoveringDeckPermutation Q n hLC hT2 p delta *
        unorderedCoveringDeckPermutation Q n hLC hT2 p gamma := by
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  symm
  apply unorderedCoveringDeckPermutation_unique Q n hLC hT2 p (gamma * delta)
  let base : {q : Ordered Q n //
      Quotient.mk' q = (Quotient.mk' p : Unordered Q n)} := ⟨p, rfl⟩
  have hmul := DFunLike.congr_fun
    (map_mul (unorderedConfigurationFiberMonodromy Q n hLC hT2 p) gamma delta) base
  have hequiv := unorderedConfigurationFiberMonodromy_deck_equivariant
    Q n hLC hT2 p gamma
    (unorderedCoveringDeckPermutation Q n hLC hT2 p delta) base
  have hdelta :
      unorderedConfigurationFiberDeckAction Q n p
          (unorderedCoveringDeckPermutation Q n hLC hT2 p delta) base =
        unorderedConfigurationFiberMonodromy Q n hLC hT2 p delta base := by
    apply Subtype.ext
    exact unorderedCoveringDeckPermutation_smul Q n hLC hT2 p delta
  change
    (unorderedCoveringDeckPermutation Q n hLC hT2 p delta *
        unorderedCoveringDeckPermutation Q n hLC hT2 p gamma) • p =
      unorderedCoveringMonodromyEndpoint Q n hLC hT2 p (gamma * delta)
  rw [mul_smul,
    unorderedCoveringDeckPermutation_smul Q n hLC hT2 p gamma]
  change
    (unorderedConfigurationFiberDeckAction Q n p
      (unorderedCoveringDeckPermutation Q n hLC hT2 p delta)
      (unorderedConfigurationFiberMonodromy Q n hLC hT2 p gamma base)).1 = _
  rw [← hequiv]
  rw [hdelta]
  exact congrArg Subtype.val hmul.symm

/-- Deck-permutation monodromy as an honest representation into the opposite
symmetric group.  The opposite target records the native path-composition
convention rather than hiding it behind an inverse or a renamed product. -/
noncomputable def unorderedCoveringDeckMonodromy
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n) :
    @FundamentalGroup (Unordered Q n)
        (unorderedConfigurationTopology Q n) (Quotient.mk' p) →*
      (Equiv.Perm (Fin n))ᵐᵒᵖ where
  toFun gamma := MulOpposite.op
    (unorderedCoveringDeckPermutation Q n hLC hT2 p gamma)
  map_one' := congrArg MulOpposite.op
    (unorderedCoveringDeckPermutation_one Q n hLC hT2 p)
  map_mul' gamma delta := by
    apply MulOpposite.unop_injective
    exact unorderedCoveringDeckPermutation_mul Q n hLC hT2 p gamma delta

end InfoGeometry.Twistor.ProjectiveNullConfigurationDeckMonodromy
