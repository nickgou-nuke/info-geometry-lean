/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealDualTwistor
import InfoGeometry.Geometry.DualFlatKreinLegendreGraph
import InfoGeometry.Quantum.DualFlatKreinGraph
import Mathlib.LinearAlgebra.Prod
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Cotangent operators, duality graphs, and the Hamiltonian tangent identity

The carrier is the existing `RealDualTwistor.Carrier V = V × Module.Dual ℝ V`.
A frame equivalence acts through the existing contragredient `frameAction`.
Its action on a duality graph is the explicit congruence
`H ↦ (g⁻¹).dualMap ∘ H ∘ g⁻¹`.

The infinitesimal action `A ↦ A ⊕ -A.dualMap` is a faithful native Lie
homomorphism. It preserves both evaluation forms infinitesimally and preserves
a graph exactly when `H ∘ A + A.dualMap ∘ H = 0`. Neither symmetry nor
positive definiteness of `H` is required for this equivalence.

The Hamiltonian identity is stated on the algebraic dual carrier as an exact
linear tangent coefficient, with an exact quadratic remainder formula. No
topology on the full algebraic dual, differentiable group action, integrated
flow, or quantization is inferred. The symplectic form has the Geometry sign;
the opposite Quantum convention is compared explicitly.
-/

noncomputable section

namespace InfoGeometry.Geometry.CotangentOperators

open InfoGeometry.Twistor.RealDualTwistor

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-! ## Contragredient transport of actual graph submodules -/

/-- The transformed duality, with both inverse factors in their proper order. -/
def transportDuality (g : V ≃ₗ[ℝ] W) (H : V →ₗ[ℝ] Module.Dual ℝ V) :
    W →ₗ[ℝ] Module.Dual ℝ W :=
  g.symm.toLinearMap.dualMap.comp (H.comp g.symm.toLinearMap)

@[simp] theorem transportDuality_apply (g : V ≃ₗ[ℝ] W)
    (H : V →ₗ[ℝ] Module.Dual ℝ V) (x y : W) :
    transportDuality g H x y = H (g.symm x) (g.symm y) := rfl

/-- The existing graph lift is equivariant under the actual frame action. -/
theorem frameAction_graphLift (g : V ≃ₗ[ℝ] W)
    (H : V →ₗ[ℝ] Module.Dual ℝ V) (x : V) :
    frameAction g (DualFlatKreinLegendreGraph.graphLift H x) =
      DualFlatKreinLegendreGraph.graphLift (transportDuality g H) (g x) := by
  apply Prod.ext
  · rfl
  · ext y
    change H x (g.symm y) = H (g.symm (g x)) (g.symm y)
    rw [g.symm_apply_apply]

/-- Contragredient transport sends the whole native graph to the transformed graph. -/
theorem map_graph_frameAction (g : V ≃ₗ[ℝ] W)
    (H : V →ₗ[ℝ] Module.Dual ℝ V) :
    H.graph.map (frameAction g).toLinearMap = (transportDuality g H).graph := by
  ext z
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hq' : q.2 = H q.1 := hq
    change q.2.comp g.symm.toLinearMap = transportDuality g H (g q.1)
    rw [hq']
    ext y
    change H q.1 (g.symm y) = H (g.symm (g q.1)) (g.symm y)
    rw [g.symm_apply_apply]
  · intro hz
    refine ⟨(g.symm z.1, H (g.symm z.1)), rfl, ?_⟩
    apply Prod.ext
    · exact g.apply_symm_apply z.1
    · change transportDuality g H z.1 = z.2
      exact hz.symm

theorem transportDuality_symmetric (g : V ≃ₗ[ℝ] W)
    (H : V →ₗ[ℝ] Module.Dual ℝ V)
    (hH : DualFlatKreinLegendreGraph.IsSymmetricDuality H) :
    DualFlatKreinLegendreGraph.IsSymmetricDuality (transportDuality g H) := by
  intro x y
  exact hH (g.symm x) (g.symm y)

/-- Alternating bilinear forms are transported on the same native carrier. -/
theorem transportDuality_alternating (g : V ≃ₗ[ℝ] W)
    (H : V →ₗ[ℝ] Module.Dual ℝ V) (hH : LinearMap.BilinForm.IsAlt H) :
    LinearMap.BilinForm.IsAlt (transportDuality g H) := by
  intro x
  exact hH (g.symm x)

/-! ## The native infinitesimal cotangent representation -/

/-- The negative dual is essential: this is a Lie lift, not a product lift. -/
def infinitesimalLift (A : Module.End ℝ V) : Module.End ℝ (Carrier V) :=
  A.prodMap (-A.dualMap)

@[simp] theorem infinitesimalLift_apply (A : Module.End ℝ V) (z : Carrier V) :
    infinitesimalLift A z = (A z.1, -z.2.comp A) := rfl

theorem infinitesimalLift_add (A B : Module.End ℝ V) :
    infinitesimalLift (A + B) = infinitesimalLift A + infinitesimalLift B := by
  apply LinearMap.ext
  intro z
  apply Prod.ext
  · rfl
  · ext v
    change -(z.2 (A v + B v)) = -(z.2 (A v)) + -(z.2 (B v))
    rw [map_add]
    abel

theorem infinitesimalLift_smul (r : ℝ) (A : Module.End ℝ V) :
    infinitesimalLift (r • A) = r • infinitesimalLift A := by
  apply LinearMap.ext
  intro z
  apply Prod.ext
  · rfl
  · ext v
    change -(z.2 (r • A v)) = r * (-(z.2 (A v)))
    simp only [map_smul, smul_eq_mul, mul_neg]

/-- Dual composition reverses order; its negative gives the correct Lie sign. -/
theorem infinitesimalLift_commutator (A B : Module.End ℝ V) :
    infinitesimalLift (A * B - B * A) =
      infinitesimalLift A * infinitesimalLift B -
        infinitesimalLift B * infinitesimalLift A := by
  apply LinearMap.ext
  intro z
  apply Prod.ext
  · rfl
  · ext v
    change -(z.2 (A (B v) - B (A v))) =
      -(-(z.2 (B (A v)))) - -(-(z.2 (A (B v))))
    rw [map_sub]
    abel

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- The cotangent action as a native real Lie-algebra homomorphism. -/
def infinitesimalLiftLieHom :
    Module.End ℝ V →ₗ⁅ℝ⁆ Module.End ℝ (Carrier V) where
  toFun := infinitesimalLift
  map_add' := infinitesimalLift_add
  map_smul' := infinitesimalLift_smul
  map_lie' := by
    intro A B
    exact infinitesimalLift_commutator A B

theorem infinitesimalLift_injective :
    Function.Injective (infinitesimalLift (V := V)) := by
  intro A B h
  apply LinearMap.ext
  intro v
  exact congrArg Prod.fst (LinearMap.congr_fun h (v, 0))

/-- The primal/dual grading commutes with every cotangent infinitesimal action. -/
theorem infinitesimalLift_para (A : Module.End ℝ V) :
    infinitesimalLift A * para = para * infinitesimalLift A := by
  apply LinearMap.ext
  intro z
  apply Prod.ext
  · rfl
  · ext v
    rfl

/-- The infinitesimal lift is equivariant for the already constructed frame action. -/
theorem infinitesimalLift_frameAction (g : V ≃ₗ[ℝ] W)
    (A : Module.End ℝ V) (z : Carrier V) :
    frameAction g (infinitesimalLift A z) =
      infinitesimalLift (g.toLinearMap.comp (A.comp g.symm.toLinearMap))
        (frameAction g z) := by
  apply Prod.ext
  · change g (A z.1) = g (A (g.symm (g z.1)))
    rw [g.symm_apply_apply]
  · ext w
    change -(z.2 (A (g.symm w))) = -(z.2 (g.symm (g (A (g.symm w)))))
    rw [g.symm_apply_apply]

theorem infinitesimalLift_neutralForm (A : Module.End ℝ V) (z w : Carrier V) :
    neutralForm (infinitesimalLift A z) w +
      neutralForm z (infinitesimalLift A w) = 0 := by
  change (-(z.2 (A w.1)) + w.2 (A z.1)) +
    (z.2 (A w.1) + -(w.2 (A z.1))) = 0
  abel

theorem infinitesimalLift_symplecticForm (A : Module.End ℝ V) (z w : Carrier V) :
    symplecticForm (infinitesimalLift A z) w +
      symplecticForm z (infinitesimalLift A w) = 0 := by
  change (w.2 (A z.1) - -(z.2 (A w.1))) +
    (-(w.2 (A z.1)) - z.2 (A w.1)) = 0
  abel

/-- Graph preservation is precisely skew-adjointness for the duality `H`.
The graph and the preservation condition are native submodule operations. -/
theorem infinitesimalLift_graph_le_iff (A : Module.End ℝ V)
    (H : V →ₗ[ℝ] Module.Dual ℝ V) :
    H.graph.map (infinitesimalLift A) ≤ H.graph ↔
      H.comp A + A.dualMap.comp H = 0 := by
  constructor
  · intro h
    ext v w
    have hm : infinitesimalLift A (v, H v) ∈ H.graph :=
      h ⟨(v, H v), rfl, rfl⟩
    have he : -(H v).comp A = H (A v) := hm
    have hew := LinearMap.congr_fun he w
    change -(H v (A w)) = H (A v) w at hew
    change H (A v) w + H v (A w) = 0
    linarith
  · intro h z hz
    obtain ⟨q, hq, rfl⟩ := hz
    have hq' : q.2 = H q.1 := hq
    change -(q.2.comp A) = H (A q.1)
    rw [hq']
    ext w
    have he := LinearMap.congr_fun (LinearMap.congr_fun h q.1) w
    change H (A q.1) w + H q.1 (A w) = 0 at he
    change -(H q.1 (A w)) = H (A q.1) w
    linarith

/-! ## Exact algebraic Hamiltonian tangent and the symplectic sign -/

/-- The canonical bilinear Hamiltonian associated to an endomorphism. -/
def hamiltonian (A : Module.End ℝ V) (z : Carrier V) : ℝ := z.2 (A z.1)

/-- The linear tangent coefficient of `hamiltonian A` at `z`.
The following expansion proves this interpretation on the algebraic carrier. -/
def hamiltonianTangent (A : Module.End ℝ V) (z : Carrier V) :
    Module.Dual ℝ (Carrier V) where
  toFun w := w.2 (A z.1) + z.2 (A w.1)
  map_add' w u := by
    change (w.2 + u.2) (A z.1) + z.2 (A (w.1 + u.1)) =
      (w.2 (A z.1) + z.2 (A w.1)) + (u.2 (A z.1) + z.2 (A u.1))
    simp only [LinearMap.add_apply, map_add]
    abel
  map_smul' r w := by
    change (r • w.2) (A z.1) + z.2 (A (r • w.1)) =
      r * (w.2 (A z.1) + z.2 (A w.1))
    simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
    rw [mul_add]

@[simp] theorem hamiltonianTangent_apply (A : Module.End ℝ V) (z w : Carrier V) :
    hamiltonianTangent A z w = w.2 (A z.1) + z.2 (A w.1) := rfl

/-- Full quadratic expansion; the tangent coefficient is not postulated. -/
theorem hamiltonian_add_smul (A : Module.End ℝ V) (z w : Carrier V) (t : ℝ) :
    hamiltonian A (z + t • w) = hamiltonian A z +
      t * hamiltonianTangent A z w + t ^ 2 * hamiltonian A w := by
  change (z.2 + t • w.2) (A (z.1 + t • w.1)) =
    z.2 (A z.1) + t * (w.2 (A z.1) + z.2 (A w.1)) +
      t ^ 2 * w.2 (A w.1)
  simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
    smul_eq_mul, pow_two, mul_add, mul_assoc]
  ac_rfl

/-- With the Geometry sign, the cotangent lift contracts to the Hamiltonian tangent. -/
theorem symplecticForm_infinitesimalLift_eq_hamiltonianTangent
    (A : Module.End ℝ V) (z w : Carrier V) :
    symplecticForm (infinitesimalLift A z) w = hamiltonianTangent A z w := by
  change w.2 (A z.1) - -(z.2 (A w.1)) = w.2 (A z.1) + z.2 (A w.1)
  exact sub_neg_eq_add _ _

/-- The ordered commutator measures the directional change of another charge. -/
theorem hamiltonianTangent_infinitesimalLift (A B : Module.End ℝ V) (z : Carrier V) :
    hamiltonianTangent B z (infinitesimalLift A z) =
      -hamiltonian (A * B - B * A) z := by
  change -(z.2 (A (B z.1))) + z.2 (B (A z.1)) =
    -(z.2 (A (B z.1) - B (A z.1)))
  rw [map_sub]
  abel

/-- An exact infinitesimal conservation criterion, without an assumed flow. -/
theorem hamiltonianTangent_zero_of_commute (A B : Module.End ℝ V)
    (hAB : Commute A B) (z : Carrier V) :
    hamiltonianTangent B z (infinitesimalLift A z) = 0 := by
  rw [hamiltonianTangent_infinitesimalLift, hAB.eq, sub_self]
  simp [hamiltonian]

theorem geometry_symplectic_eq (z w : Carrier V) :
    DualFlatKreinLegendreGraph.canonicalSymplectic z w = symplecticForm z w := rfl

/-- The separate Quantum owner uses the opposite sign on this same carrier. -/
theorem quantum_symplectic_eq_neg {n : ℕ}
    (z w : InfoGeometry.Quantum.DualFlatKreinGraph.Carrier n) :
    InfoGeometry.Quantum.DualFlatKreinGraph.symplecticPair z w =
      -symplecticForm z w := by
  change z.2 w.1 - w.2 z.1 = -(w.2 z.1 - z.2 w.1)
  ring

end InfoGeometry.Geometry.CotangentOperators
