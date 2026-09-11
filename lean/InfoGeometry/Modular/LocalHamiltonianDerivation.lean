import Mathlib.Algebra.Algebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Order.Directed
import Mathlib.Tactic

/-!
# Local Modular Derivation as Inner Derivation ad_{𝒦_i}

Formalizes the identification of local infinitesimal modular generators
`δ_i : A_i →ₗ[R] A_i` with the inner commutator derivations induced by
the local modular Hamiltonians (surprisals) `𝒦_i ∈ A_i`:

  `δ_i(x) = ad_{𝒦_i}(x) = [𝒦_i, x] = 𝒦_i * x - x * 𝒦_i`

Mathematical components:
  1. `innerDeriv`: Construction of `ad_K : A →ₗ[R] A` for an associative R-algebra.
  2. `ModularHamiltonianSystem`: Family `{𝒦_i}_{i ∈ I}` satisfying the compatibility
     condition `f_{i,j}(𝒦_i) = 𝒦_j` along transition maps.
  3. `innerDeriv_intertwine`: Proof that `f_{i,j} ∘ ad_{𝒦_i} = ad_{𝒦_j} ∘ f_{i,j}`.
  4. `localModularDeriv`: Concrete realization of the local derivation family.

All proofs are complete with 0 `sorry`s, 0 custom axioms, and 0 placeholders.
-/

namespace InfoGeometry.Modular.LocalHamiltonianDerivation

variable {R : Type*} [CommRing R]

/-! =========================================================================
    1. The Inner Derivation ad_K = [K, ·]
    ========================================================================= -/

variable {A : Type*} [Ring A] [Algebra R A]

/-- The commutator bracket `[K, x] = K * x - x * K`. -/
def bracket (K x : A) : A :=
  K * x - x * K

@[simp]
theorem bracket_apply (K x : A) : bracket K x = K * x - x * K :=
  rfl

/-- Additivity: `[K, x + y] = [K, x] + [K, y]`. -/
theorem bracket_add (K x y : A) : bracket K (x + y) = bracket K x + bracket K y := by
  dsimp [bracket]
  rw [mul_add, add_mul]
  abel

/-- R-scalar compatibility: `[K, r • x] = r • [K, x]`. -/
theorem bracket_smul (K : A) (r : R) (x : A) : bracket K (r • x) = r • bracket K x := by
  dsimp [bracket]
  rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]

/--
Leibniz Product Rule:
  `[K, xy] = [K, x]y + x[K, y]`
-/
theorem bracket_leibniz (K x y : A) :
    bracket K (x * y) = bracket K x * y + x * bracket K y := by
  simp only [bracket]
  calc
    K * (x * y) - (x * y) * K
      = (K * x * y - x * K * y) + (x * K * y - x * y * K) := by
        simp only [mul_assoc]
        abel_nf
    _ = (K * x - x * K) * y + x * (K * y - y * K) := by
        simp only [sub_mul, mul_sub, mul_assoc]

/--
Inner derivation `ad_K` as an R-linear map `A →ₗ[R] A`.
-/
def innerDeriv (K : A) : A →ₗ[R] A where
  toFun := bracket K
  map_add' := bracket_add K
  map_smul' := bracket_smul K

@[simp]
theorem innerDeriv_apply (K x : A) : innerDeriv (R := R) K x = K * x - x * K :=
  rfl

/-- The inner derivation satisfies the Leibniz product rule. -/
theorem innerDeriv_leibniz (K : A) (x y : A) :
    innerDeriv (R := R) K (x * y) = innerDeriv (R := R) K x * y + x * innerDeriv (R := R) K y :=
  bracket_leibniz K x y

/-- The inner derivation annihilates the identity element: ad_K(1) = 0. -/
@[simp]
theorem innerDeriv_one (K : A) : innerDeriv (R := R) K 1 = 0 := by
  simp [innerDeriv_apply]

/-! =========================================================================
    2. Directed System of Associative R-Algebras
    ========================================================================= -/

/-- Directed system of associative R-algebras. -/
structure DirectedRingSystem (I : Type*) [Preorder I] (A : I → Type*)
    [∀ i, Ring (A i)] [∀ i, Algebra R (A i)] where
  map : ∀ {i j : I}, i ≤ j → (A i →ₐ[R] A j)
  map_self : ∀ (i : I) (x : A i), map (le_refl i) x = x
  map_trans : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : A i),
    map (le_trans hij hjk) x = map hjk (map hij x)

/-! =========================================================================
    3. Compatible Modular Hamiltonian System
    ========================================================================= -/

/--
A family of local modular Hamiltonians (surprisals) `{𝒦_i}_{i ∈ I}`
compatible with transition homomorphisms: `f_{i,j}(𝒦_i) = 𝒦_j`.
-/
structure ModularHamiltonianSystem (I : Type*) [Preorder I] (A : I → Type*)
    [∀ i, Ring (A i)] [∀ i, Algebra R (A i)] (sys : DirectedRingSystem (R := R) I A) where
  hamiltonian : ∀ (i : I), A i
  map_hamiltonian : ∀ {i j : I} (hij : i ≤ j), sys.map hij (hamiltonian i) = hamiltonian j

/-! =========================================================================
    4. Intertwining Theorem and Local Derivation System Instance
    ========================================================================= -/

variable {I : Type*} [Preorder I]
variable {A : I → Type*} [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]
variable (sys : DirectedRingSystem (R := R) I A)
variable (hamSys : ModularHamiltonianSystem (R := R) I A sys)

/--
MAIN THEOREM (Intertwining of Inner Modular Derivations):
If transition maps preserve the modular Hamiltonian `f_{i,j}(𝒦_i) = 𝒦_j`, then
  `f_{i,j} (ad_{𝒦_i}(x)) = ad_{𝒦_j} (f_{i,j}(x))`
-/
theorem innerDeriv_intertwine {i j : I} (hij : i ≤ j) (x : A i) :
    sys.map hij (innerDeriv (R := R) (hamSys.hamiltonian i) x) =
      innerDeriv (R := R) (hamSys.hamiltonian j) (sys.map hij x) := by
  simp only [innerDeriv_apply]
  rw [map_sub, map_mul, map_mul, hamSys.map_hamiltonian hij]

/--
Local derivation family generated by the modular Hamiltonians:
  `δ_i := ad_{𝒦_i}`
-/
def localModularDeriv (i : I) : A i →ₗ[R] A i :=
  innerDeriv (hamSys.hamiltonian i)

/--
COROLLARY:
The local modular derivation `δ_i(x)` expands explicitly to `𝒦_i * x - x * 𝒦_i`.
-/
theorem localModularDeriv_eq_commutator (i : I) (x : A i) :
    localModularDeriv (R := R) sys hamSys i x = hamSys.hamiltonian i * x - x * hamSys.hamiltonian i :=
  rfl

end InfoGeometry.Modular.LocalHamiltonianDerivation
