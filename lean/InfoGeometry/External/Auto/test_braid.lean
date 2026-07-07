import Mathlib

open scoped TensorProduct
open LinearMap

section Braid

universe u v
variable (k : Type u) [CommRing k]
variable (V : Type v) [AddCommGroup V] [Module k V]

/-- `R12` applies `R` to the first two tensor factors. -/
def R12 (R : Module.End k (V ⊗[k] V)) : Module.End k ((V ⊗[k] V) ⊗[k] V) :=
  TensorProduct.map R (LinearMap.id : V →ₗ[k] V)

/-- `R23` applies `R` to the second and third tensor factors. -/
def R23 (R : Module.End k (V ⊗[k] V)) : Module.End k (V ⊗[k] (V ⊗[k] V)) :=
  TensorProduct.map (LinearMap.id : V →ₗ[k] V) R

/-- The associator equivalence between `(V ⊗ V) ⊗ V` and `V ⊗ (V ⊗ V)`. -/
def assoc_equiv : ((V ⊗[k] V) ⊗[k] V) ≃ₗ[k] (V ⊗[k] (V ⊗[k] V)) :=
  TensorProduct.assoc k V V V

/-- Pulling back `R23` to act on `(V ⊗ V) ⊗ V` via the associator. -/
def R23_on_assoc (R : Module.End k (V ⊗[k] V)) : Module.End k ((V ⊗[k] V) ⊗[k] V) :=
  (assoc_equiv k V).symm.toLinearMap ∘ₗ (R23 k V R) ∘ₗ (assoc_equiv k V).toLinearMap

/--
A braid generator R is an endomorphism of V ⊗ V satisfying the 
Yang-Baxter equation.
-/
structure BraidGenerator where
  R : Module.End k (V ⊗[k] V)
  yang_baxter : 
    (R12 k V R) ∘ₗ (R23_on_assoc k V R) ∘ₗ (R12 k V R) =
    (R23_on_assoc k V R) ∘ₗ (R12 k V R) ∘ₗ (R23_on_assoc k V R)

end Braid

section BraidExample

variable (k : Type*) [CommRing k]
variable (V : Type*) [AddCommGroup V] [Module k V]

/-- The identity map on V ⊗ V -/
def id_tensor : Module.End k (V ⊗[k] V) := LinearMap.id

/-- R12 for the identity map is just the identity on (V ⊗ V) ⊗ V -/
lemma R12_id : R12 k V (id_tensor k V) = LinearMap.id := by
  sorry

/-- R23 for the identity map is just the identity on V ⊗ (V ⊗ V) -/
lemma R23_id : R23 k V (id_tensor k V) = LinearMap.id := by
  sorry

/-- R23_on_assoc for the identity map is the identity on (V ⊗ V) ⊗ V -/
lemma R23_on_assoc_id : R23_on_assoc k V (id_tensor k V) = LinearMap.id := by
  sorry

/-- The identity map satisfies the Yang-Baxter equation trivially. -/
lemma yang_baxter_id : 
  (R12 k V (id_tensor k V)) ∘ₗ (R23_on_assoc k V (id_tensor k V)) ∘ₗ (R12 k V (id_tensor k V)) =
  (R23_on_assoc k V (id_tensor k V)) ∘ₗ (R12 k V (id_tensor k V)) ∘ₗ (R23_on_assoc k V (id_tensor k V)) := by
  sorry

/-- Concrete instantiation of a BraidGenerator using the identity map. -/
def trivialBraidGenerator : BraidGenerator k V where
  R := id_tensor k V
  yang_baxter := yang_baxter_id k V

end BraidExample

section LiveContext

variable {F : Type*} [Field F] (A : F)
variable {A_alg : Type*} [Ring A_alg] [Algebra F A_alg]
variable (ei ej : A_alg)

-- Let's test if noncomm_ring can expand and simplify with scalar multiplication.
-- Wait, noncomm_ring doesn't handle algebraMap well sometimes.
-- We can just define elements directly.

end LiveContext
