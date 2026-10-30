/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
# The finite G₂(2) automorphism group as noncommutative operators

The split-octonion automorphism group acts on real-valued functions over its
actual algebra carrier. This turns each algebra automorphism into an
invertible endomorphism and transports the existing noncommuting root
generators faithfully.
-/
import InfoGeometry.Algebra.Zorn.G2TwoExplicitGenerators
import InfoGeometry.Algebra.Zorn.G2TwoFiniteChevalleyGroup

noncomputable section

namespace InfoGeometry.OperatorAlgebra.G2TwoOperatorRepresentation

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoFiniteChevalleyGroup
open InfoGeometry.Algebra.Zorn.G2Unipotent

/-- The operator induced by a split-octonion algebra automorphism on
real-valued functions over the octonion carrier. -/
def automorphismOperator (g : SplitOctF2Aut) :
    Module.End ℝ (SplitOctF2 → ℝ) where
  toFun f X := f (g.1 X)
  map_add' f h := by funext X; rfl
  map_smul' c f := by funext X; rfl

/-- The induced invertible endomorphism. -/
def automorphismOperatorUnit (g : SplitOctF2Aut) :
    (Module.End ℝ (SplitOctF2 → ℝ))ˣ where
  val := automorphismOperator g
  inv := automorphismOperator g⁻¹
  val_inv := by ext f X; simp [automorphismOperator]
  inv_val := by ext f X; simp [automorphismOperator]

/-- The faithful homomorphism from split-octonion automorphisms to operator
units. -/
def automorphismOperatorRep :
    SplitOctF2Aut →* (Module.End ℝ (SplitOctF2 → ℝ))ˣ where
  toFun := automorphismOperatorUnit
  map_one' := by apply Units.ext; ext f X; rfl
  map_mul' g h := by
    apply Units.ext
    apply LinearMap.ext
    intro f
    funext X
    change f ((g * h).1 X) = f (h.1 (g.1 X))
    rw [finiteChevalleyG2_mul_apply]

/-- Equality of operators recovers equality of the underlying algebra
automorphisms. -/
theorem automorphismOperatorRep_injective :
    Function.Injective automorphismOperatorRep := by
  classical
  intro g h hgh
  have hval : automorphismOperator g = automorphismOperator h :=
    congrArg (fun u : (Module.End ℝ (SplitOctF2 → ℝ))ˣ =>
      (u : Module.End ℝ (SplitOctF2 → ℝ))) hgh
  have hmap : g.1 = h.1 := by
    apply Equiv.ext
    intro X
    let δ : SplitOctF2 → ℝ := fun Y => if Y = g.1 X then 1 else 0
    have heval := congrArg
      (fun T : Module.End ℝ (SplitOctF2 → ℝ) => T δ X) hval
    have hpoint : h.1 X = g.1 X := by
      simpa [δ, automorphismOperator] using heval.symm
    exact hpoint.symm
  apply Subtype.ext
  exact hmap

/-- The operator-unit image of the finite split-octonion automorphism group. -/
def g2TwoOperatorGroup :
    Subgroup (Module.End ℝ (SplitOctF2 → ℝ))ˣ :=
  (⊤ : Subgroup SplitOctF2Aut).map automorphismOperatorRep

/-- The two local simple-root automorphisms remain noncommuting in the
faithful operator-unit representation. -/
theorem g2TwoOperatorGroup_has_noncommuting_pair :
    ∃ U V : (Module.End ℝ (SplitOctF2 → ℝ))ˣ,
      U ∈ g2TwoOperatorGroup ∧ V ∈ g2TwoOperatorGroup ∧ U * V ≠ V * U := by
  let g := unipotentShortAut true
  let h := unipotentLongAut true
  have hgh : g * h ≠ h * g := by
    simpa [g, h] using simple_root_generators_do_not_commute
  refine ⟨automorphismOperatorRep g, automorphismOperatorRep h, ?_, ?_, ?_⟩
  · rw [g2TwoOperatorGroup, Subgroup.mem_map]
    exact ⟨g, trivial, rfl⟩
  · rw [g2TwoOperatorGroup, Subgroup.mem_map]
    exact ⟨h, trivial, rfl⟩
  · intro hcomm
    apply hgh
    apply automorphismOperatorRep_injective
    simpa only [map_mul] using hcomm

end InfoGeometry.OperatorAlgebra.G2TwoOperatorRepresentation

end
