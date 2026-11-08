/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceDissipatorTrinity

/-!
# Reflexive Peirce operators across injective noncommutative towers

This owner transports polynomial operator structure through an actual sequence
of injective ring homomorphisms. Injectivity is explicit because algebraic
relations survive every ring homomorphism, while nonzero mass support does not
survive a potentially noninjective quotient map.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceOperatorTower

/-- A sequential tower of associative operator rings with injective transition
maps. Star structure and topology are not needed for these polynomial laws. -/
structure NoncommutativeOperatorTower (A : ℕ → Type*) [∀ k, Ring (A k)] where
  stepHom : ∀ k, A k →+* A (k + 1)
  step_injective : ∀ k, Function.Injective (stepHom k)

namespace NoncommutativeOperatorTower

variable {A : ℕ → Type*} [∀ k, Ring (A k)]

/-- The composite embedding from the base operator algebra to stage `k`. -/
def embedFromBase (T : NoncommutativeOperatorTower A) :
    (k : ℕ) → A 0 →+* A k
  | 0 => RingHom.id (A 0)
  | k + 1 => (T.stepHom k).comp (embedFromBase T k)

/-- Every finite-stage map remains injective. -/
theorem embedFromBase_injective (T : NoncommutativeOperatorTower A) (k : ℕ) :
    Function.Injective (embedFromBase T k) := by
  induction k with
  | zero =>
      intro x y h
      change x = y at h
      exact h
  | succ k ih =>
      intro x y h
      change T.stepHom k (embedFromBase T k x) =
        T.stepHom k (embedFromBase T k y) at h
      have h' := T.step_injective k h
      exact ih h'

/-- At every stage, an injective operator tower preserves the nonzero
idempotent Jordan mass, Dirac support and involution, and the full `sl₂`
root-triad/Casimir identities of a reflexive square-zero pair. -/
theorem reflexive_pair_mass_and_root_persistence
    (T : NoncommutativeOperatorTower A) (k : ℕ)
    (u v : A 0)
    (hu : u * u = 0) (hv : v * v = 0)
    (huv : u * v * u = u) (hvu : v * u * v = v)
    (hMass : u * v + v * u ≠ 0) :
    let uk := embedFromBase T k u
    let vk := embedFromBase T k v
    let mass := uk * vk + vk * uk
    let dirac := uk + vk
    mass * mass = mass ∧ mass ≠ 0 ∧
      dirac * dirac = mass ∧ dirac * mass = dirac ∧ mass * dirac = dirac ∧
      ((1 - mass) + dirac) * ((1 - mass) + dirac) = 1 ∧
      (uk * vk - vk * uk) * uk - uk * (uk * vk - vk * uk) = (2 : ℕ) • uk ∧
      (uk * vk - vk * uk) * vk - vk * (uk * vk - vk * uk) = -((2 : ℕ) • vk) ∧
      (uk * vk - vk * uk) * (uk * vk - vk * uk) +
        (2 : ℕ) • mass = (3 : ℕ) • mass := by
  dsimp
  let f := embedFromBase T k
  have hMassIdem :=
    InfoGeometry.OperatorAlgebra.PeirceDissipatorTrinity.ringHom_preserves_reflexive_pair_mass_idempotent
      f u v hu hv huv hvu
  have hMassNe :=
    InfoGeometry.OperatorAlgebra.PeirceDissipatorTrinity.ringHom_preserves_nonzero_jordan_mass
      f (embedFromBase_injective T k) u v hMass
  have hDirac :=
    InfoGeometry.OperatorAlgebra.PeirceDissipatorTrinity.ringHom_preserves_reflexive_pair_dirac_support
      f u v hu hv huv hvu
  have hRoot :=
    InfoGeometry.OperatorAlgebra.PeirceDissipatorTrinity.ringHom_preserves_reflexive_pair_sl2
      f u v hu hv huv hvu
  exact ⟨hMassIdem, hMassNe, hDirac.1, hDirac.2.1, hDirac.2.2.1,
    hDirac.2.2.2, hRoot.1, hRoot.2.1, hRoot.2.2⟩

/-- A compatible, injective ring cocone from the operator tower to an apex.
This packages the algebraic data needed to transport operator identities to
an existing colimit carrier; it does not itself assert the cocone universal
property. -/
structure CompatibleOperatorCocone (T : NoncommutativeOperatorTower A)
    (Apex : Type*) [Ring Apex] where
  apexMap : ∀ k, A k →+* Apex
  apexMap_injective : ∀ k, Function.Injective (apexMap k)
  compatible : ∀ k x, apexMap (k + 1) (T.stepHom k x) = apexMap k x

/-- Every finite-stage image of a base operator agrees with its stage-zero
image in the compatible apex cocone. -/
theorem apexMap_embedFromBase_eq (T : NoncommutativeOperatorTower A)
    {Apex : Type*} [Ring Apex] (C : CompatibleOperatorCocone T Apex)
    (k : ℕ) (x : A 0) :
    C.apexMap k (embedFromBase T k x) = C.apexMap 0 x := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change C.apexMap (k + 1)
          (T.stepHom k (embedFromBase T k x)) = C.apexMap 0 x
      rw [C.compatible k]
      exact ih

/-- The compatible cocone apex inherits the nonzero idempotent mass, Dirac
support/involution, and `sl₂` relations at every finite stage. Supply the
actual colimit cocone from its categorical owner when the apex is a colimit. -/
theorem compatible_cocone_reflexive_pair_persistence
    (T : NoncommutativeOperatorTower A) {Apex : Type*} [Ring Apex]
    (C : CompatibleOperatorCocone T Apex) (k : ℕ)
    (u v : A 0)
    (hu : u * u = 0) (hv : v * v = 0)
    (huv : u * v * u = u) (hvu : v * u * v = v)
    (hMass : u * v + v * u ≠ 0) :
    let uk := C.apexMap k (embedFromBase T k u)
    let vk := C.apexMap k (embedFromBase T k v)
    let mass := uk * vk + vk * uk
    let dirac := uk + vk
    C.apexMap k (embedFromBase T k u) = C.apexMap 0 u ∧
      C.apexMap k (embedFromBase T k v) = C.apexMap 0 v ∧
      mass * mass = mass ∧ mass ≠ 0 ∧
      dirac * dirac = mass ∧ dirac * mass = dirac ∧ mass * dirac = dirac ∧
      ((1 - mass) + dirac) * ((1 - mass) + dirac) = 1 ∧
      (uk * vk - vk * uk) * uk - uk * (uk * vk - vk * uk) = (2 : ℕ) • uk ∧
      (uk * vk - vk * uk) * vk - vk * (uk * vk - vk * uk) = -((2 : ℕ) • vk) ∧
      (uk * vk - vk * uk) * (uk * vk - vk * uk) +
        (2 : ℕ) • mass = (3 : ℕ) • mass := by
  dsimp
  let f := (C.apexMap k).comp (embedFromBase T k)
  have hf : Function.Injective f :=
    (C.apexMap_injective k).comp (embedFromBase_injective T k)
  have hMassIdem :=
    InfoGeometry.OperatorAlgebra.PeirceDissipatorTrinity.ringHom_preserves_reflexive_pair_mass_idempotent
      f u v hu hv huv hvu
  have hMassNe :=
    InfoGeometry.OperatorAlgebra.PeirceDissipatorTrinity.ringHom_preserves_nonzero_jordan_mass
      f hf u v hMass
  have hDirac :=
    InfoGeometry.OperatorAlgebra.PeirceDissipatorTrinity.ringHom_preserves_reflexive_pair_dirac_support
      f u v hu hv huv hvu
  have hRoot :=
    InfoGeometry.OperatorAlgebra.PeirceDissipatorTrinity.ringHom_preserves_reflexive_pair_sl2
      f u v hu hv huv hvu
  exact ⟨apexMap_embedFromBase_eq T C k u,
    apexMap_embedFromBase_eq T C k v, hMassIdem, hMassNe,
    hDirac.1, hDirac.2.1, hDirac.2.2.1, hDirac.2.2.2,
    hRoot.1, hRoot.2.1, hRoot.2.2⟩

end NoncommutativeOperatorTower
end InfoGeometry.OperatorAlgebra.PeirceOperatorTower
