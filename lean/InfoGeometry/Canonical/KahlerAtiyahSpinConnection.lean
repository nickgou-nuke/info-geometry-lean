/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Contraction

import InfoGeometry.Canonical.KahlerAtiyahCartanForms

/-!
# Kähler--Atiyah bivectors and the spin Lie action

This module is the next theorem edge after the Cartan-form Clifford
representation on the exterior algebra.

For a symmetric metric `g`, write `c(v)` for the Kähler--Atiyah action
`ε(v) + ι(g(v,-))`.  The normalized Clifford bivector

`Σ(v,u) = (1/4) [c(v), c(u)]`

acts on generators by the orthogonal Lie algebra formula

`[Σ(v,u), c(w)] = g(u,w)c(v) - g(v,w)c(u)`.

Thus the degree-two Clifford commutators on literal exterior forms realize
the infinitesimal spin/orthogonal action, without introducing a matrix gamma
representation.
-/

noncomputable section

namespace InfoGeometry.Canonical.KahlerAtiyahSpinConnection

open InfoGeometry.Canonical.KahlerAtiyahCartanForms

universe u

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- Commutator in the endomorphism algebra of exterior forms. -/
def endCommutator
    (A B : FormEnd V) :
    FormEnd V :=
  A * B - B * A

private theorem commutator_jacobi {R : Type*} [Ring R] (A B C : R) :
    (A * B - B * A) * C - C * (A * B - B * A) =
      (A * (B * C - C * B) - (B * C - C * B) * A) -
        (B * (A * C - C * A) - (A * C - C * A) * B) := by
  noncomm_ring

@[simp] theorem endCommutator_self
    (A : FormEnd V) :
    endCommutator A A = 0 := by
  simp [endCommutator]

theorem endCommutator_skew
    (A B : FormEnd V) :
    endCommutator A B = -endCommutator B A := by
  dsimp [endCommutator]
  abel

theorem endCommutator_smul_left (r : ℝ) (A B : FormEnd V) :
    endCommutator (r • A) B = r • endCommutator A B := by
  ext α
  simp [endCommutator, Module.End.mul_apply, smul_sub]

theorem endCommutator_add_left (A₁ A₂ B : FormEnd V) :
    endCommutator (A₁ + A₂) B =
      endCommutator A₁ B + endCommutator A₂ B := by
  dsimp [endCommutator]
  noncomm_ring

/-- Normalized Clifford bivector generator
`Σ(v,u) = 1/4 [c(v),c(u)]`. -/
def spinBivector
    (g : LinearMap.BilinForm ℝ V)
    (v u : V) :
    FormEnd V :=
  (1 / 4 : ℝ) •
    endCommutator
      (cartanCliffordAction g v)
      (cartanCliffordAction g u)

theorem spinBivector_skew
    (g : LinearMap.BilinForm ℝ V)
    (v u : V) :
    spinBivector g v u = -spinBivector g u v := by
  unfold spinBivector
  rw [endCommutator_skew (cartanCliffordAction g v) (cartanCliffordAction g u),
    smul_neg]

theorem spinBivector_add_left
    (g : LinearMap.BilinForm ℝ V) (v₁ v₂ u : V) :
    spinBivector g (v₁ + v₂) u =
      spinBivector g v₁ u + spinBivector g v₂ u := by
  unfold spinBivector
  rw [show cartanCliffordAction g (v₁ + v₂) =
      cartanCliffordAction g v₁ + cartanCliffordAction g v₂ by
        exact map_add (cartanCliffordActionMap g) v₁ v₂]
  rw [endCommutator_add_left]
  rw [smul_add]

theorem spinBivector_smul_left
    (g : LinearMap.BilinForm ℝ V) (r : ℝ) (v u : V) :
    spinBivector g (r • v) u = r • spinBivector g v u := by
  unfold spinBivector
  rw [show cartanCliffordAction g (r • v) =
      r • cartanCliffordAction g v by
        exact map_smul (cartanCliffordActionMap g) r v]
  rw [endCommutator_smul_left]
  module

theorem spinBivector_add_right
    (g : LinearMap.BilinForm ℝ V) (v u₁ u₂ : V) :
    spinBivector g v (u₁ + u₂) =
      spinBivector g v u₁ + spinBivector g v u₂ := by
  calc
    spinBivector g v (u₁ + u₂) =
        -(spinBivector g (u₁ + u₂) v) := by rw [spinBivector_skew]
    _ = -(spinBivector g u₁ v + spinBivector g u₂ v) := by
      rw [spinBivector_add_left]
    _ = spinBivector g v u₁ + spinBivector g v u₂ := by
      rw [spinBivector_skew g v u₁, spinBivector_skew g v u₂]
      module

theorem spinBivector_smul_right
    (g : LinearMap.BilinForm ℝ V) (r : ℝ) (v u : V) :
    spinBivector g v (r • u) = r • spinBivector g v u := by
  calc
    spinBivector g v (r • u) =
        -(spinBivector g (r • u) v) := by rw [spinBivector_skew]
    _ = -(r • spinBivector g u v) := by rw [spinBivector_smul_left]
    _ = r • spinBivector g v u := by rw [spinBivector_skew]; module

@[simp] theorem spinBivector_self
    (g : LinearMap.BilinForm ℝ V)
    (v : V) :
    spinBivector g v v = 0 := by
  simp [spinBivector]

/--
Unnormalized commutator identity behind the spin action.

For three Clifford generators `A = c(v)`, `B = c(u)`, `C = c(w)`,
the double commutator satisfies

`[[A,B],C] = 4 g(u,w) A - 4 g(v,w) B`.
-/
theorem clifford_double_commutator
    (g : LinearMap.BilinForm ℝ V)
    (hg : ∀ x y, g x y = g y x)
    (v u w : V) :
    endCommutator
        (endCommutator
          (cartanCliffordAction g v)
          (cartanCliffordAction g u))
        (cartanCliffordAction g w) =
      (4 * g u w) • cartanCliffordAction g v -
        (4 * g v w) • cartanCliffordAction g u := by
  let A : FormEnd V := cartanCliffordAction g v
  let B : FormEnd V := cartanCliffordAction g u
  let C : FormEnd V := cartanCliffordAction g w

  have hBC :
      B * C + C * B =
        (2 * g u w) • (1 : FormEnd V) := by
    dsimp [B, C]
    exact cartanCliffordAction_anticommutator_of_symmetric g hg u w

  have hAC :
      A * C + C * A =
        (2 * g v w) • (1 : FormEnd V) := by
    dsimp [A, C]
    exact cartanCliffordAction_anticommutator_of_symmetric g hg v w

  have hrearrange :
      endCommutator (endCommutator A B) C =
        A * (B * C + C * B) -
          (A * C + C * A) * B -
          B * (A * C + C * A) +
          (B * C + C * B) * A := by
    dsimp [endCommutator]
    simp only [sub_mul, mul_sub, add_mul, mul_add, mul_assoc]
    abel

  rw [hrearrange, hBC, hAC]
  simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  apply LinearMap.ext
  intro α
  simp only [LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply]
  module

/--
The normalized Clifford bivector acts on Cartan generators by the defining
orthogonal Lie algebra representation:

`[Σ(v,u),c(w)] = g(u,w)c(v) - g(v,w)c(u)`.
-/
theorem spinBivector_comm_cartanCliffordAction
    (g : LinearMap.BilinForm ℝ V)
    (hg : ∀ x y, g x y = g y x)
    (v u w : V) :
    endCommutator
        (spinBivector g v u)
        (cartanCliffordAction g w) =
      (g u w) • cartanCliffordAction g v -
        (g v w) • cartanCliffordAction g u := by
  unfold spinBivector
  rw [endCommutator_smul_left]
  rw [clifford_double_commutator g hg v u w]
  apply LinearMap.ext
  intro α
  simp only [LinearMap.smul_apply, LinearMap.sub_apply]
  module

/--
Coframe specialization.  If `g(θ_a,θ_b)=η_ab`, the spin bivectors act on
the Cartan coframe generators by

`[Σ_ab,c(θ_c)] = η_bc c(θ_a) - η_ac c(θ_b)`.
-/
theorem coframe_spinBivector_action
    {ι : Type*}
    (g : LinearMap.BilinForm ℝ V)
    (hg : ∀ x y, g x y = g y x)
    (θ : ι → V)
    (η : ι → ι → ℝ)
    (hθ : ∀ a b, g (θ a) (θ b) = η a b)
    (a b c : ι) :
    endCommutator
        (spinBivector g (θ a) (θ b))
        (cartanCliffordAction g (θ c)) =
      (η b c) • cartanCliffordAction g (θ a) -
        (η a c) • cartanCliffordAction g (θ b) := by
  rw [spinBivector_comm_cartanCliffordAction g hg]
  rw [hθ, hθ]

/-! ### Metric-skew endomorphisms as Clifford bivector actions

The elementary bivectors above generate the orthogonal Lie algebra when the
metric is nondegenerate. The formula below is written using an explicit basis
and its metric-dual basis. The resulting operator is proved independent of
that basis; the theorem remains pointwise on one real Clifford module and does
not itself construct bundle transition functions or a global spinor bundle.
No complex scalar structure or orthonormal-frame assumption is introduced.
-/

/-- A Clifford bivector representative for a metric-skew endomorphism, written
using the supplied basis and its metric-dual basis. -/
noncomputable def metricSkewSpinLift
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (A : V →ₗ[ℝ] V) : FormEnd V :=
  (1 / 2 : ℝ) • ∑ i, spinBivector g (A (b i)) ((g.dualBasis hg b) i)

private def metricSkewSpinTensorMap
    (g : LinearMap.BilinForm ℝ V) (A : V →ₗ[ℝ] V) :
    TensorProduct ℝ V V →ₗ[ℝ] FormEnd V :=
  TensorProduct.lift (LinearMap.mk₂ ℝ
    (fun v u => spinBivector g (A v) u)
    (by
      intro v₁ v₂ u
      rw [map_add A, spinBivector_add_left])
    (by
      intro r v u
      rw [map_smul A, spinBivector_smul_left])
    (by
      intro v u₁ u₂
      exact spinBivector_add_right g (A v) u₁ u₂)
    (by
      intro r v u
      exact spinBivector_smul_right g r (A v) u))

private theorem dualTensorBasis_sum_eq
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (b : Module.Basis ι ℝ V) (c : Module.Basis κ ℝ V) :
    (∑ i, b.dualBasis i ⊗ₜ[ℝ] b i) =
      ∑ j, c.dualBasis j ⊗ₜ[ℝ] c j := by
  have hb : dualTensorHom ℝ V V
      (∑ i, b.dualBasis i ⊗ₜ[ℝ] b i) = LinearMap.id := by
    rw [map_sum]
    ext x
    rw [LinearMap.sum_apply]
    simp only [dualTensorHom_apply, Module.Basis.dualBasis_apply]
    exact b.sum_repr x
  have hc : dualTensorHom ℝ V V
      (∑ j, c.dualBasis j ⊗ₜ[ℝ] c j) = LinearMap.id := by
    rw [map_sum]
    ext x
    rw [LinearMap.sum_apply]
    simp only [dualTensorHom_apply, Module.Basis.dualBasis_apply]
    exact c.sum_repr x
  apply (dualTensorHomEquivOfBasis b).injective
  change dualTensorHom ℝ V V (∑ i, b.dualBasis i ⊗ₜ[ℝ] b i) =
    dualTensorHom ℝ V V (∑ j, c.dualBasis j ⊗ₜ[ℝ] c j)
  exact hb.trans hc.symm

/-- The tensor made from a basis and its metric-dual basis is independent of
the chosen finite basis. -/
theorem metricDualTensor_basis_independent
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [FiniteDimensional ℝ V]
    (b : Module.Basis ι ℝ V) (c : Module.Basis κ ℝ V)
    (g : LinearMap.BilinForm ℝ V) (hg : g.Nondegenerate) :
    (∑ i, b i ⊗ₜ[ℝ] (g.dualBasis hg b) i) =
      ∑ j, c j ⊗ₜ[ℝ] (g.dualBasis hg c) j := by
  have hcanonical := dualTensorBasis_sum_eq b c
  have htransport := congrArg
    (fun z => (g.toDual hg).symm.rTensor V z) hcanonical
  have hcomm := congrArg (TensorProduct.comm ℝ V V) htransport
  simpa [LinearEquiv.rTensor_tmul, LinearMap.BilinForm.dualBasis,
    Module.Basis.map_apply, TensorProduct.comm_tmul] using hcomm

/-- The metric-skew bivector operator itself is independent of the chosen
finite basis. The proof factors the basis sum through the basis-independent
metric-dual tensor, so this is operator equality and not only equality of its
action on Clifford generators. -/
theorem metricSkewSpinLift_basis_independent
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [FiniteDimensional ℝ V]
    (b : Module.Basis ι ℝ V) (c : Module.Basis κ ℝ V)
    (g : LinearMap.BilinForm ℝ V) (hg : g.Nondegenerate)
    (A : V →ₗ[ℝ] V) :
    metricSkewSpinLift b g hg A = metricSkewSpinLift c g hg A := by
  unfold metricSkewSpinLift
  have h := congrArg (metricSkewSpinTensorMap g A)
    (metricDualTensor_basis_independent b c g hg)
  have hsum :
      (∑ i, spinBivector g (A (b i)) ((g.dualBasis hg b) i)) =
        ∑ j, spinBivector g (A (c j)) ((g.dualBasis hg c) j) := by
    simpa [metricSkewSpinTensorMap, LinearMap.mk₂] using h
  exact congrArg (fun z : FormEnd V => (1 / 2 : ℝ) • z) hsum

/-- Additivity of the chosen-basis bivector representative in the
metric-skew endomorphism. This is the connection one-form linearity needed
when the covariant derivative of a field is assembled by addition. -/
theorem metricSkewSpinLift_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (A₁ A₂ : V →ₗ[ℝ] V) :
    metricSkewSpinLift b g hg (A₁ + A₂) =
      metricSkewSpinLift b g hg A₁ + metricSkewSpinLift b g hg A₂ := by
  unfold metricSkewSpinLift
  simp only [LinearMap.add_apply, spinBivector_add_left]
  rw [Finset.sum_add_distrib, smul_add]

/-- Scalar linearity of the chosen-basis bivector representative. -/
theorem metricSkewSpinLift_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (r : ℝ) (A : V →ₗ[ℝ] V) :
    metricSkewSpinLift b g hg (r • A) =
      r • metricSkewSpinLift b g hg A := by
  unfold metricSkewSpinLift
  simp only [LinearMap.smul_apply, spinBivector_smul_left]
  rw [← Finset.smul_sum]
  rw [smul_smul, smul_smul, mul_comm (1 / 2 : ℝ) r]

private theorem endCommutator_sum_left
    {ι : Type*} [Fintype ι]
    (F : ι → FormEnd V) (B : FormEnd V) :
    endCommutator (∑ i, F i) B = ∑ i, endCommutator (F i) B := by
  simp only [endCommutator, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_sub_distrib]

/-- A metric-skew endomorphism is realized on Clifford generators by the
commutator with the bivector representative constructed from the supplied
metric-dual basis. This proves the pointwise algebraic action identity needed
for a Kosmann lift; the basis-independent operator theorem above removes the
choice of basis, but this file does not construct bundle transition maps. -/
theorem metricSkewSpinLift_comm_cartanCliffordAction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate)
    (hgsymm : ∀ x y, g x y = g y x)
    (A : V →ₗ[ℝ] V)
    (hA : ∀ x y, g (A x) y + g x (A y) = 0)
    (w : V) :
    endCommutator
        (metricSkewSpinLift b g hg A)
        (cartanCliffordAction g w) =
      cartanCliffordAction g (A w) := by
  let bStar := g.dualBasis hg b
  have hpair (i : ι) : g (bStar i) w = b.repr w i := by
    rw [← b.sum_repr w]
    simp only [map_sum, map_smul]
    rw [Finset.sum_eq_single i]
    · rw [LinearMap.BilinForm.apply_dualBasis_left]
      simp
    · intro j hj hji
      rw [LinearMap.BilinForm.apply_dualBasis_left]
      simp [hji]
    · simp
  have hfirst :
      ∑ i, g (bStar i) w • cartanCliffordAction g (A (b i)) =
        cartanCliffordAction g (A w) := by
    simp_rw [hpair]
    let L := (cartanCliffordActionMap g).comp A
    change ∑ i, b.repr w i •
        L (b i) = L w
    simp_rw [← map_smul L]
    rw [← map_sum L (fun i => b.repr w i • b i) Finset.univ]
    rw [b.sum_repr w]
  have hskew (i : ι) : g (A (b i)) w = -g (b i) (A w) :=
    eq_neg_of_add_eq_zero_left (hA (b i) w)
  have hdualReconstruct :
      ∑ i, g (b i) (A w) • bStar i = A w := by
    calc
      ∑ i, g (b i) (A w) • bStar i =
          ∑ i, bStar.repr (A w) i • bStar i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [LinearMap.BilinForm.dualBasis_repr_apply, hgsymm]
      _ = A w := bStar.sum_repr (A w)
  have hsecond :
      ∑ i, g (A (b i)) w • cartanCliffordAction g (bStar i) =
        -cartanCliffordAction g (A w) := by
    calc
      ∑ i, g (A (b i)) w • cartanCliffordAction g (bStar i) =
          -∑ i, g (b i) (A w) • cartanCliffordAction g (bStar i) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            rw [hskew]
            module
      _ = -cartanCliffordAction g (A w) := by
            have hmap := congrArg (cartanCliffordActionMap g) hdualReconstruct
            simp only [map_sum, map_smul] at hmap
            exact congrArg Neg.neg hmap
  unfold metricSkewSpinLift
  rw [endCommutator_smul_left, endCommutator_sum_left]
  simp_rw [spinBivector_comm_cartanCliffordAction g hgsymm]
  rw [show (1 / 2 : ℝ) •
      (∑ i, (g (bStar i) w • cartanCliffordAction g (A (b i)) -
        g (A (b i)) w • cartanCliffordAction g (bStar i))) =
      (1 / 2 : ℝ) • (cartanCliffordAction g (A w) -
        -cartanCliffordAction g (A w)) by rw [Finset.sum_sub_distrib, hfirst, hsecond]]
  module

/-- The commutator of metric-skew endomorphisms is metric-skew. This is the
pointwise Lie-algebra closure needed to transport curvature through the spin
lift; no definiteness assumption on the symmetric form is used. -/
theorem metricSkewEnd_comm_metricSkew
    (g : LinearMap.BilinForm ℝ V)
    (A B : V →ₗ[ℝ] V)
    (hA : ∀ x y, g (A x) y + g x (A y) = 0)
    (hB : ∀ x y, g (B x) y + g x (B y) = 0)
    (x y : V) :
    g ((A.comp B - B.comp A) x) y +
        g x ((A.comp B - B.comp A) y) = 0 := by
  have hAB : g (A (B x)) y = g x (B (A y)) := by
    have h₁ := hA (B x) y
    have h₂ := hB x (A y)
    linarith
  have hBA : g (B (A x)) y = g x (A (B y)) := by
    have h₁ := hB (A x) y
    have h₂ := hA x (B y)
    linarith
  change g (A (B x) - B (A x)) y +
    g x (A (B y) - B (A y)) = 0
  simp only [LinearMap.sub_apply, map_sub]
  rw [hAB, hBA]
  abel

/-- The spin lift represents the Lie bracket on Clifford generators: the
commutator of two lifted metric-skew endomorphisms acts on every Clifford
generator exactly as the commutator of the original endomorphisms. This is
the pointwise Lie-algebra compatibility that a curved Kosmann construction
would need; no curved bundle or curvature tensor is defined here. -/
theorem metricSkewSpinLift_commutator_action
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate)
    (hgsymm : ∀ x y, g x y = g y x)
    (A B : V →ₗ[ℝ] V)
    (hA : ∀ x y, g (A x) y + g x (A y) = 0)
    (hB : ∀ x y, g (B x) y + g x (B y) = 0)
    (w : V) :
    endCommutator
        (endCommutator (metricSkewSpinLift b g hg A)
          (metricSkewSpinLift b g hg B))
        (cartanCliffordAction g w) =
      cartanCliffordAction g ((A.comp B - B.comp A) w) := by
  calc
    endCommutator
        (endCommutator (metricSkewSpinLift b g hg A)
          (metricSkewSpinLift b g hg B))
        (cartanCliffordAction g w) =
      endCommutator (metricSkewSpinLift b g hg A)
          (endCommutator (metricSkewSpinLift b g hg B)
            (cartanCliffordAction g w)) -
        endCommutator (metricSkewSpinLift b g hg B)
          (endCommutator (metricSkewSpinLift b g hg A)
            (cartanCliffordAction g w)) := by
          simpa only [endCommutator] using
            (commutator_jacobi
              (metricSkewSpinLift b g hg A)
              (metricSkewSpinLift b g hg B)
              (cartanCliffordAction g w))
    _ = cartanCliffordAction g (A (B w)) -
          cartanCliffordAction g (B (A w)) := by
          rw [metricSkewSpinLift_comm_cartanCliffordAction
                b g hg hgsymm B hB w,
              metricSkewSpinLift_comm_cartanCliffordAction
                b g hg hgsymm A hA w,
              metricSkewSpinLift_comm_cartanCliffordAction
                b g hg hgsymm A hA (B w),
              metricSkewSpinLift_comm_cartanCliffordAction
                b g hg hgsymm B hB (A w)]
    _ = cartanCliffordAction g ((A.comp B - B.comp A) w) := by
          change cartanCliffordActionMap g (A (B w)) -
            cartanCliffordActionMap g (B (A w)) = _
          rw [← map_sub]
          simp only [LinearMap.sub_apply, LinearMap.comp_apply]
          simp only [cartanCliffordActionMap_apply]

/-! ### Spin connection one-forms on a fixed real Clifford module

Given a linear family of metric-skew endomorphisms, the preceding basis
representative assembles into a linear one-form with values in the real
Kähler--Atiyah operator algebra. This is the algebraic, fixed-fiber
connection-lifting step; it does not supply a tangent/spinor bundle, local
trivializations, or a curved covariant derivative.
-/

/-- The spin-operator-valued one-form induced by a linear family of
endomorphisms of `V`. -/
def metricSkewSpinConnection
    {U : Type*} [AddCommGroup U] [Module ℝ U]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (A : U →ₗ[ℝ] V →ₗ[ℝ] V) :
    U →ₗ[ℝ] FormEnd V where
  toFun x := metricSkewSpinLift b g hg (A x)
  map_add' x y := by
    rw [map_add A x y]
    exact metricSkewSpinLift_add b g hg (A x) (A y)
  map_smul' r x := by
    rw [map_smul A r x]
    exact metricSkewSpinLift_smul b g hg r (A x)

/-- The spin-operator-valued connection one-form is independent of the basis
used to write its metric-dual contraction. The equality is in the linear-map
space of one-forms, not merely pointwise after acting on Clifford generators. -/
theorem metricSkewSpinConnection_basis_independent
    {U : Type*} [AddCommGroup U] [Module ℝ U]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [FiniteDimensional ℝ V]
    (b : Module.Basis ι ℝ V) (c : Module.Basis κ ℝ V)
    (g : LinearMap.BilinForm ℝ V) (hg : g.Nondegenerate)
    (A : U →ₗ[ℝ] V →ₗ[ℝ] V) :
    metricSkewSpinConnection b g hg A =
      metricSkewSpinConnection c g hg A := by
  apply LinearMap.ext
  intro x
  exact metricSkewSpinLift_basis_independent b c g hg (A x)

/-- The induced spin connection one-form acts on Clifford generators by the
original metric-skew endomorphism-valued one-form. -/
theorem metricSkewSpinConnection_comm_cartanCliffordAction
    {U : Type*} [AddCommGroup U] [Module ℝ U]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (hgsymm : ∀ x y, g x y = g y x)
    (A : U →ₗ[ℝ] V →ₗ[ℝ] V)
    (hA : ∀ x v w, g (A x v) w + g v (A x w) = 0)
    (x : U) (w : V) :
    endCommutator
        (metricSkewSpinConnection b g hg A x)
        (cartanCliffordAction g w) =
      cartanCliffordAction g (A x w) := by
  exact metricSkewSpinLift_comm_cartanCliffordAction b g hg hgsymm
    (A x) (hA x) w

/-- The curvature action of the induced real spin connection agrees on
Clifford generators with the curvature action of the underlying
metric-skew endomorphism connection.  The bracket term is kept explicit, so
this statement applies to a Lie-algebra connection once its base bracket is
instantiated; it does not assert the existence of a curved spinor bundle. -/
theorem metricSkewSpinConnection_curvature_action
    {U : Type*} [AddCommGroup U] [Module ℝ U]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (hgsymm : ∀ x y, g x y = g y x)
    (A : U →ₗ[ℝ] V →ₗ[ℝ] V)
    (hA : ∀ x v w, g (A x v) w + g v (A x w) = 0)
    (bracket : U → U → U) (x y : U) (w : V) :
    endCommutator
        (endCommutator (metricSkewSpinConnection b g hg A x)
          (metricSkewSpinConnection b g hg A y))
        (cartanCliffordAction g w) -
      endCommutator (metricSkewSpinConnection b g hg A (bracket x y))
        (cartanCliffordAction g w) =
      cartanCliffordAction g
        (A x (A y w) - A y (A x w) - A (bracket x y) w) := by
  change endCommutator
      (endCommutator (metricSkewSpinLift b g hg (A x))
        (metricSkewSpinLift b g hg (A y)))
      (cartanCliffordAction g w) -
    endCommutator (metricSkewSpinLift b g hg (A (bracket x y)))
      (cartanCliffordAction g w) = _
  rw [metricSkewSpinLift_commutator_action b g hg hgsymm
      (A x) (A y) (hA x) (hA y) w,
    metricSkewSpinLift_comm_cartanCliffordAction b g hg hgsymm
      (A (bracket x y)) (hA (bracket x y)) w]
  change cartanCliffordActionMap g
        (A x (A y w) - A y (A x w)) -
      cartanCliffordActionMap g (A (bracket x y) w) = _
  rw [← map_sub]
  simp only [cartanCliffordActionMap_apply]

/-- If the metric-skew connection on the vector module is a representation of
the supplied Lie bracket, its induced real spin connection has zero curvature
defect on every Clifford generator. This is the representation-compatibility
condition needed before transporting such a connection through a colimit. -/
theorem metricSkewSpinConnection_curvature_vanishes_on_generators
    {U : Type*} [AddCommGroup U] [Module ℝ U]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (hgsymm : ∀ x y, g x y = g y x)
    (A : U →ₗ[ℝ] V →ₗ[ℝ] V)
    (hA : ∀ x v w, g (A x v) w + g v (A x w) = 0)
    (bracket : U → U → U) (x y : U)
    (hcurv : ∀ w : V,
      A x (A y w) - A y (A x w) = A (bracket x y) w) :
    endCommutator
        (endCommutator (metricSkewSpinConnection b g hg A x)
          (metricSkewSpinConnection b g hg A y))
        (cartanCliffordAction g w) -
      endCommutator (metricSkewSpinConnection b g hg A (bracket x y))
        (cartanCliffordAction g w) = 0 := by
  rw [metricSkewSpinConnection_curvature_action b g hg hgsymm A hA
    bracket x y w]
  have h : A x (A y w) - A y (A x w) - A (bracket x y) w = 0 := by
    rw [hcurv w]
    simp
  rw [h]
  exact map_zero (cartanCliffordActionMap g)

end InfoGeometry.Canonical.KahlerAtiyahSpinConnection
