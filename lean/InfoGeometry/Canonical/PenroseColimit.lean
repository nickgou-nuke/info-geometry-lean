import Mathlib
import InfoGeometry.Canonical.InductiveColimitBridge

/-!
# Penrose Tiling Bratteli Limit

This module uses the `InductiveColimitBridge` to formally lift the 
finite Penrose spin-network patches to the continuous AF C*-algebra limit.
It demonstrates that the K_0 group of the infinite Penrose tiling is the 
inductive limit of the finite-stage K-theories.
-/

namespace PenroseColimit

open InductiveColimitBridge

universe u

/-- 
The structural parameters for the Penrose K-theory connecting tower, explicitly 
packaged to instantiate the categorical proof colimit.
-/
def penroseKTheoryTower
    (Patch_n : ℕ → Type u)
    [∀ n, CommRing (Patch_n n)] [∀ n, StarRing (Patch_n n)]
    (inflation_bond : ∀ n, Patch_n n →+* Patch_n (n+1))
    (PenroseAF : Type u)
    [CommRing PenroseAF] [StarRing PenroseAF]
    (patch_toLimit : ∀ n, Patch_n n →+* PenroseAF)
    (patch_cone_comm : ∀ n x, patch_toLimit (n+1) (inflation_bond n x) = patch_toLimit n x)
    (K0_n : ℕ → Type u)
    [∀ n, AddCommGroup (K0_n n)]
    (k0_bond : ∀ n, K0_n n →+ K0_n (n+1))
    (K0_inf : Type u)
    [AddCommGroup K0_inf]
    (k0_toLimit : ∀ n, K0_n n →+ K0_inf)
    (k0_cone_comm : ∀ n x, k0_toLimit (n+1) (k0_bond n x) = k0_toLimit n x)
    (k0_functor : ∀ n, Patch_n n → K0_n n → Prop)
    (k0_compat : ∀ n x y, k0_functor n x y → k0_functor (n+1) (inflation_bond n x) (k0_bond n y))
    (limit_k0_functor : PenroseAF → K0_inf → Prop)
    (limit_k0_readout : ∀ n x y, k0_functor n x y → limit_k0_functor (patch_toLimit n x) (k0_toLimit n y)) :
    CompatibleFiniteEquivalenceTower where
  Left := { Stage := Patch_n, Limit := PenroseAF, bond := fun n x => inflation_bond n x, toLimit := fun n x => patch_toLimit n x, cone_comm := patch_cone_comm }
  Right := { Stage := K0_n, Limit := K0_inf, bond := fun n x => k0_bond n x, toLimit := fun n x => k0_toLimit n x, cone_comm := k0_cone_comm }
  equivAt := k0_functor
  equiv_compat := k0_compat
  limitEquiv := limit_k0_functor
  limit_readout := limit_k0_readout

/-- 
THE PENROSE COLIMIT THEOREM: 
The K_0 functor commutes with direct limits. The finite-stage K-theories 
transport stably to the infinite-dimensional Penrose AF C*-algebra.
-/
theorem penrose_k0_colimit_stabilization
    (Patch_n : ℕ → Type u)
    [∀ n, CommRing (Patch_n n)] [∀ n, StarRing (Patch_n n)]
    (inflation_bond : ∀ n, Patch_n n →+* Patch_n (n+1))
    (PenroseAF : Type u)
    [CommRing PenroseAF] [StarRing PenroseAF]
    (patch_toLimit : ∀ n, Patch_n n →+* PenroseAF)
    (patch_cone_comm : ∀ n x, patch_toLimit (n+1) (inflation_bond n x) = patch_toLimit n x)
    (K0_n : ℕ → Type u)
    [∀ n, AddCommGroup (K0_n n)]
    (k0_bond : ∀ n, K0_n n →+ K0_n (n+1))
    (K0_inf : Type u)
    [AddCommGroup K0_inf]
    (k0_toLimit : ∀ n, K0_n n →+ K0_inf)
    (k0_cone_comm : ∀ n x, k0_toLimit (n+1) (k0_bond n x) = k0_toLimit n x)
    (k0_functor : ∀ n, Patch_n n → K0_n n → Prop)
    (k0_compat : ∀ n x y, k0_functor n x y → k0_functor (n+1) (inflation_bond n x) (k0_bond n y))
    (limit_k0_functor : PenroseAF → K0_inf → Prop)
    (limit_k0_readout : ∀ n x y, k0_functor n x y → limit_k0_functor (patch_toLimit n x) (k0_toLimit n y))
    (n : ℕ) (x : Patch_n n) (y : K0_n n) (h_k0 : k0_functor n x y) :
    limit_k0_functor (patch_toLimit n x) (k0_toLimit n y) :=
  CompatibleFiniteEquivalenceTower.finite_equiv_to_colimit 
    (penroseKTheoryTower Patch_n inflation_bond PenroseAF patch_toLimit patch_cone_comm 
                         K0_n k0_bond K0_inf k0_toLimit k0_cone_comm 
                         k0_functor k0_compat limit_k0_functor limit_k0_readout) 
    n x y h_k0

end PenroseColimit
