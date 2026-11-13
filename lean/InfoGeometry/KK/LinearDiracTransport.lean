/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.KK.RealSplitKreinLinearResolventBridge

/-!
# Transport of linear operators with a genuine domain

For a linear operator `D : S →ₗ[ℝ] H` and a continuous linear equivalence `e`,
this file constructs its operator on `e(S)`. Density, closedness of the graph,
signed intertwining relations, and a compact linear resolvent are transported
by proved maps. No target regularity or target resolvent equation is assumed.

The carrier can be infinite dimensional. The statements concern conjugation
of a given operator; they do not construct a geometric Dirac operator or an
analytic family index. A represented Pin element can supply `e` through an
actual representation into continuous linear equivalences.
-/

noncomputable section

namespace InfoGeometry.KK.LinearDiracTransport

open InfoGeometry.KK.RealSplitKreinLinearResolventBridge

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The transported linear domain. -/
def domain (e : H ≃L[ℝ] H) (S : Submodule ℝ H) : Submodule ℝ H :=
  S.map e.toLinearEquiv.toLinearMap

/-- The actual equivalence from the source domain onto its image. -/
def domainEquiv (e : H ≃L[ℝ] H) (S : Submodule ℝ H) :
    S ≃ₗ[ℝ] domain e S :=
  e.toLinearEquiv.submoduleMap S

@[simp] theorem domainEquiv_coe (e : H ≃L[ℝ] H) (S : Submodule ℝ H) (x : S) :
    (domainEquiv e S x : H) = e x := rfl

@[simp] theorem domainEquiv_symm_coe
    (e : H ≃L[ℝ] H) (S : Submodule ℝ H) (x : domain e S) :
    ((domainEquiv e S).symm x : H) = e.symm x := by
  apply e.injective
  calc
    e ((domainEquiv e S).symm x : H) = (x : H) :=
      congrArg (fun y : domain e S => (y : H))
        ((domainEquiv e S).apply_symm_apply x)
    _ = e (e.symm x) := (e.apply_symm_apply x).symm

@[simp] theorem mem_domain_iff
    (e : H ≃L[ℝ] H) (S : Submodule ℝ H) (x : H) :
    x ∈ domain e S ↔ e.symm x ∈ S := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    simpa [← hxy] using hy
  · intro hx
    exact ⟨e.symm x, hx, e.apply_symm_apply x⟩

theorem domain_coe (e : H ≃L[ℝ] H) (S : Submodule ℝ H) :
    (domain e S : Set H) = e '' (S : Set H) := rfl

/-- Multiplication applies the right frame first, as required for operator actions. -/
theorem domain_mul (e f : H ≃L[ℝ] H) (S : Submodule ℝ H) :
    domain (e * f) S = domain e (domain f S) := by
  ext x
  simp only [mem_domain_iff]
  rfl

/-- Domain transport respects an actual group representation, including a Pin pullback. -/
theorem domain_representation_mul
    {G : Type*} [Group G] (ρ : G →* H ≃L[ℝ] H) (S : Submodule ℝ H) (g h : G) :
    domain (ρ (g * h)) S = domain (ρ g) (domain (ρ h) S) := by
  rw [map_mul, domain_mul]

/-- Conjugation of an operator whose domain is the submodule `S`. -/
def operator (e : H ≃L[ℝ] H) {S : Submodule ℝ H} (D : S →ₗ[ℝ] H) :
    domain e S →ₗ[ℝ] H :=
  e.toLinearEquiv.toLinearMap.comp (D.comp (domainEquiv e S).symm.toLinearMap)

@[simp] theorem operator_domainEquiv
    (e : H ≃L[ℝ] H) {S : Submodule ℝ H} (D : S →ₗ[ℝ] H) (x : S) :
    operator e D (domainEquiv e S x) = e (D x) := by
  simp [operator]

/-- The transported operator obeys the same noncommutative composition order. -/
theorem operator_mul_on_domain
    (e f : H ≃L[ℝ] H) {S : Submodule ℝ H} (D : S →ₗ[ℝ] H) (x : S) :
    operator (e * f) D (domainEquiv (e * f) S x) =
      operator e (operator f D) (domainEquiv e (domain f S) (domainEquiv f S x)) := by
  simp only [operator_domainEquiv]
  rfl

/-- Graph in the ambient product; the unbounded operator is linear on `S`. -/
def graph {S : Submodule ℝ H} (D : S →ₗ[ℝ] H) : Set (H × H) :=
  Set.range (fun x : S => ((x : H), D x))

theorem graph_operator_eq_image
    (e : H ≃L[ℝ] H) {S : Submodule ℝ H} (D : S →ₗ[ℝ] H) :
    graph (operator e D) =
      (fun p : H × H => (e p.1, e p.2)) '' graph D := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(((domainEquiv e S).symm x : H), D ((domainEquiv e S).symm x)),
      ⟨(domainEquiv e S).symm x, rfl⟩, ?_⟩
    simp [operator]
  · rintro ⟨p, ⟨x, rfl⟩, rfl⟩
    exact ⟨domainEquiv e S x, by simp⟩

theorem graph_operator_eq_preimage
    (e : H ≃L[ℝ] H) {S : Submodule ℝ H} (D : S →ₗ[ℝ] H) :
    graph (operator e D) =
      (fun p : H × H => (e.symm p.1, e.symm p.2)) ⁻¹' graph D := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(domainEquiv e S).symm x, by simp [operator]⟩
  · rintro ⟨x, hx⟩
    refine ⟨domainEquiv e S x, ?_⟩
    apply Prod.ext
    · simpa using congrArg e (congrArg Prod.fst hx)
    · simpa using congrArg e (congrArg Prod.snd hx)

/-- Domain density survives every continuous linear change of coordinates. -/
theorem dense_domain (e : H ≃L[ℝ] H) (S : Submodule ℝ H)
    (hS : Dense (S : Set H)) : Dense (domain e S : Set H) := by
  rw [dense_iff_closure_eq, domain_coe, ← e.image_closure, hS.closure_eq]
  rw [Set.image_univ, Set.range_eq_univ.mpr e.surjective]

/-- Closedness is proved by the explicit inverse coordinate map on the graph. -/
theorem closed_graph (e : H ≃L[ℝ] H) {S : Submodule ℝ H}
    (D : S →ₗ[ℝ] H) (hD : IsClosed (graph D)) :
    IsClosed (graph (operator e D)) := by
  rw [graph_operator_eq_preimage]
  exact hD.preimage
    ((e.symm.continuous.comp continuous_fst).prodMk
      (e.symm.continuous.comp continuous_snd))

/-- Every bounded domain-preserving operator transports with the domain. -/
theorem boundedConjugate_preserves_domain
    (e : H ≃L[ℝ] H) {S : Submodule ℝ H} (A : H →L[ℝ] H)
    (hA : ∀ x : S, A x ∈ S) (x : domain e S) :
    ContinuousLinearEquiv.conjContinuousAlgEquiv e A x ∈ domain e S := by
  rw [mem_domain_iff]
  simpa [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply] using hA ((domainEquiv e S).symm x)

/--
An actual signed operator equation on a linear domain transports. Taking
`c = -1` gives grading anticommutation; `c = 1` gives ordinary intertwining.
The same statement applies separately to any represented Clifford operator.
-/
theorem operator_signed_intertwining
    (e : H ≃L[ℝ] H) {S : Submodule ℝ H} (D : S →ₗ[ℝ] H)
    (A : H →L[ℝ] H) (hA : ∀ x : S, A x ∈ S) (c : ℝ)
    (hD : ∀ x : S, D ⟨A x, hA x⟩ = c • A (D x))
    (x : domain e S) :
    operator e D
        ⟨ContinuousLinearEquiv.conjContinuousAlgEquiv e A x, boundedConjugate_preserves_domain e A hA x⟩ =
      c • ContinuousLinearEquiv.conjContinuousAlgEquiv e A (operator e D x) := by
  obtain ⟨y, rfl⟩ := (domainEquiv e S).surjective x
  have hdomain :
      (⟨ContinuousLinearEquiv.conjContinuousAlgEquiv e A (domainEquiv e S y),
        boundedConjugate_preserves_domain e A hA (domainEquiv e S y)⟩ : domain e S) =
      domainEquiv e S ⟨A y, hA y⟩ := by
    apply Subtype.ext
    simp
  rw [hdomain, operator_domainEquiv, operator_domainEquiv]
  simpa using congrArg e (hD y)

/-- A bounded commutator is transported by the same native conjugation map. -/
theorem operator_bounded_commutator
    (e : H ≃L[ℝ] H) {S : Submodule ℝ H} (D : S →ₗ[ℝ] H)
    (A C : H →L[ℝ] H) (hA : ∀ x : S, A x ∈ S)
    (hD : ∀ x : S, D ⟨A x, hA x⟩ - A (D x) = C x)
    (x : domain e S) :
    operator e D
        ⟨e.conjContinuousAlgEquiv A x, boundedConjugate_preserves_domain e A hA x⟩ -
        e.conjContinuousAlgEquiv A (operator e D x) =
      e.conjContinuousAlgEquiv C x := by
  obtain ⟨y, rfl⟩ := (domainEquiv e S).surjective x
  have hdomain :
      (⟨e.conjContinuousAlgEquiv A (domainEquiv e S y),
        boundedConjugate_preserves_domain e A hA (domainEquiv e S y)⟩ : domain e S) =
      domainEquiv e S ⟨A y, hA y⟩ := by
    apply Subtype.ext
    simp
  rw [hdomain, operator_domainEquiv, operator_domainEquiv]
  simpa using congrArg e (hD y)

/-- Ambient zero modes of a domain-valued linear operator. -/
def zeroModes {S : Submodule ℝ H} (D : S →ₗ[ℝ] H) : Submodule ℝ H :=
  (LinearMap.ker D).map S.subtype

theorem zeroModes_operator
    (e : H ≃L[ℝ] H) {S : Submodule ℝ H} (D : S →ₗ[ℝ] H) :
    zeroModes (operator e D) = (zeroModes D).map e.toLinearEquiv.toLinearMap := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    let z : S := (domainEquiv e S).symm y
    have hz : D z = 0 := by
      apply e.injective
      simpa [operator, z] using hy
    refine ⟨(z : H), ⟨z, hz, rfl⟩, ?_⟩
    simp [z]
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨domainEquiv e S z, ?_, rfl⟩
    change operator e D (domainEquiv e S z) = 0
    change D z = 0 at hz
    simp only [operator_domainEquiv, hz, map_zero]

theorem range_boundedConjugate
    (e : H ≃L[ℝ] H) (A : H →L[ℝ] H) :
    LinearMap.range (ContinuousLinearEquiv.conjContinuousAlgEquiv e A).toLinearMap =
      (LinearMap.range A.toLinearMap).map e.toLinearEquiv.toLinearMap := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨A (e.symm y), ⟨e.symm y, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨e z, by simp⟩

/-- Zero modes in the range of a bounded operator. For a chiral projector
this is its chiral kernel sector; idempotence is not needed for transport. -/
def kernelSector {S : Submodule ℝ H} (D : S →ₗ[ℝ] H) (P : H →L[ℝ] H) :
    Submodule ℝ H :=
  zeroModes D ⊓ LinearMap.range P.toLinearMap

theorem kernelSector_operator
    (e : H ≃L[ℝ] H) {S : Submodule ℝ H} (D : S →ₗ[ℝ] H)
    (P : H →L[ℝ] H) :
    kernelSector (operator e D) (ContinuousLinearEquiv.conjContinuousAlgEquiv e P) =
      (kernelSector D P).map e.toLinearEquiv.toLinearMap := by
  unfold kernelSector
  rw [zeroModes_operator, range_boundedConjugate]
  exact (Submodule.map_inf (f := e.toLinearEquiv.toLinearMap)
    (p := zeroModes D) (q := LinearMap.range P.toLinearMap) e.injective).symm

/-- Transport preserves each zero-mode range sector. In particular, both
chiral projectors can move with a frame which need not be even. -/
def kernelSectorEquiv
    (e : H ≃L[ℝ] H) {S : Submodule ℝ H} (D : S →ₗ[ℝ] H)
    (P : H →L[ℝ] H) :
    kernelSector D P ≃ₗ[ℝ] kernelSector (operator e D) (ContinuousLinearEquiv.conjContinuousAlgEquiv e P) :=
  (e.toLinearEquiv.submoduleMap (kernelSector D P)).trans
      (LinearEquiv.ofEq _ _ (kernelSector_operator e D P).symm)

theorem finrank_kernelSector
    (e : H ≃L[ℝ] H) {S : Submodule ℝ H} (D : S →ₗ[ℝ] H)
    (P : H →L[ℝ] H) :
    Module.finrank ℝ (kernelSector (operator e D) (ContinuousLinearEquiv.conjContinuousAlgEquiv e P)) =
      Module.finrank ℝ (kernelSector D P) :=
  (kernelSectorEquiv e D P).finrank_eq.symm

theorem finiteDimensional_kernelSector
    (e : H ≃L[ℝ] H) {S : Submodule ℝ H} (D : S →ₗ[ℝ] H)
    (P : H →L[ℝ] H) [FiniteDimensional ℝ (kernelSector D P)] :
    FiniteDimensional ℝ (kernelSector (operator e D) (ContinuousLinearEquiv.conjContinuousAlgEquiv e P)) :=
  FiniteDimensional.of_injective (kernelSectorEquiv e D P).symm.toLinearMap
    (kernelSectorEquiv e D P).symm.injective

/-- Equality of the native zero-mode dimension differences along a frame
family. Instantiating `P` and `Q` with chiral projectors gives the chiral
formula. Finite-dimensionality is transported by `finiteDimensional_kernelSector`
when these dimension differences are used as indices. No continuity of the
frame is needed for this pointwise conjugacy statement.
-/
theorem chiralKernelDifference_family
    {B : Type*} (e : B → H ≃L[ℝ] H) {S : Submodule ℝ H}
    (D : S →ₗ[ℝ] H) (P Q : H →L[ℝ] H) (s t : B) :
    (Module.finrank ℝ (kernelSector (operator (e s) D) (ContinuousLinearEquiv.conjContinuousAlgEquiv (e s) P)) : ℤ) -
        (Module.finrank ℝ (kernelSector (operator (e s) D) (ContinuousLinearEquiv.conjContinuousAlgEquiv (e s) Q)) : ℤ) =
      (Module.finrank ℝ (kernelSector (operator (e t) D) (ContinuousLinearEquiv.conjContinuousAlgEquiv (e t) P)) : ℤ) -
        (Module.finrank ℝ (kernelSector (operator (e t) D) (ContinuousLinearEquiv.conjContinuousAlgEquiv (e t) Q)) : ℤ) := by
  simp only [finrank_kernelSector]

section Resolvent

variable [CompleteSpace H]

/-- Compactness is preserved by continuous linear conjugation. -/
theorem isCompactOperator_boundedConjugate
    (e : H ≃L[ℝ] H) (A : H →L[ℝ] H) (hA : IsCompactOperator A) :
    IsCompactOperator (ContinuousLinearEquiv.conjContinuousAlgEquiv e A) := by
  exact (hA.comp_clm (e.symm : H →L[ℝ] H)).clm_comp (e : H →L[ℝ] H)

/-- Construct the compact linear resolvent of the transported operator. -/
def resolvent
    (e : H ≃L[ℝ] H) {S : Submodule ℝ H} {D : S →ₗ[ℝ] H}
    (R : RealSplitKreinLinearResolventData S D) :
    RealSplitKreinLinearResolventData (domain e S) (operator e D) where
  shift := R.shift
  resolvent := ContinuousLinearEquiv.conjContinuousAlgEquiv e R.resolvent
  resolvent_preserves_domain x := by
    change e (R.resolvent (e.symm x)) ∈ S.map e.toLinearEquiv.toLinearMap
    exact ⟨R.resolvent (e.symm x), R.resolvent_preserves_domain (e.symm x), rfl⟩
  left_resolvent x := by
    have hdomain :
        (⟨ContinuousLinearEquiv.conjContinuousAlgEquiv e R.resolvent x, by
          change e (R.resolvent (e.symm x)) ∈ S.map e.toLinearEquiv.toLinearMap
          exact ⟨R.resolvent (e.symm x), R.resolvent_preserves_domain (e.symm x), rfl⟩⟩ :
          domain e S) =
        domainEquiv e S
          ⟨R.resolvent (e.symm x), R.resolvent_preserves_domain (e.symm x)⟩ := by
      apply Subtype.ext
      rfl
    rw [hdomain, operator_domainEquiv]
    simpa [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply] using congrArg e (R.left_resolvent (e.symm x))
  compact := isCompactOperator_boundedConjugate e R.resolvent R.compact

@[simp] theorem resolvent_shift
    (e : H ≃L[ℝ] H) {S : Submodule ℝ H} {D : S →ₗ[ℝ] H}
    (R : RealSplitKreinLinearResolventData S D) :
    (resolvent e R).shift = R.shift := rfl

theorem shifted_resolvent_domainEquiv
    (e : H ≃L[ℝ] H) {S : Submodule ℝ H} {D : S →ₗ[ℝ] H}
    (R : RealSplitKreinLinearResolventData S D) (x : S) :
    shifted (resolvent e R) (domainEquiv e S x) = e (shifted R x) := by
  simp [shifted, resolvent]

theorem shifted_resolvent_injective
    (e : H ≃L[ℝ] H) {S : Submodule ℝ H} {D : S →ₗ[ℝ] H}
    (R : RealSplitKreinLinearResolventData S D)
    (hR : Function.Injective (shifted R)) :
    Function.Injective (shifted (resolvent e R)) := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := (domainEquiv e S).surjective x
  obtain ⟨y, rfl⟩ := (domainEquiv e S).surjective y
  apply congrArg (domainEquiv e S)
  apply hR
  apply e.injective
  simpa only [shifted_resolvent_domainEquiv] using hxy

/-- The right inverse is derived from the source injectivity and the constructed left inverse. -/
theorem resolvent_shifted
    (e : H ≃L[ℝ] H) {S : Submodule ℝ H} {D : S →ₗ[ℝ] H}
    (R : RealSplitKreinLinearResolventData S D)
    (hR : Function.Injective (shifted R)) (x : domain e S) :
    (resolvent e R).resolvent (shifted (resolvent e R) x) = x :=
  resolvent_shifted_apply (resolvent e R) (shifted_resolvent_injective e R hR) x

end Resolvent

end InfoGeometry.KK.LinearDiracTransport
