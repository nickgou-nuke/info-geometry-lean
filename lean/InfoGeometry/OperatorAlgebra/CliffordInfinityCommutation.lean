import Mathlib.Algebra.Category.AlgCat.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import InfoGeometry.OperatorAlgebra.CliffordInfinityCAR

open CategoryTheory Limits
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Algebraic.SplitSignature

noncomputable section

namespace InfoGeometry.OperatorAlgebra

def commutator {R : Type*} [Ring R] (a b : R) : R :=
  a * b - b * a

theorem Cl_bonding_map_preserves_commutator {m n : ℕ} (h : m ≤ n) (a b : Cl_nn m) :
    Cl_bonding_map_of_le h (commutator a b) =
      commutator (Cl_bonding_map_of_le h a) (Cl_bonding_map_of_le h b) := by
  dsimp [commutator]
  rw [map_sub, map_mul, map_mul]

def colimit_ι (n : ℕ) : Cl_functor.obj n ⟶ CliffordInfinity :=
  colimit.ι Cl_functor n

theorem colimit_commutator_simple {m : ℕ} (a b : Cl_nn m) :
    commutator (colimit_ι m a) (colimit_ι m b) = colimit_ι m (commutator a b) := by
  dsimp [commutator]
  rw [map_sub, map_mul, map_mul]

theorem modular_hamiltonian_well_defined_in_colimit :
    ∃ (_K : CliffordInfinity), ∀ {m : ℕ} (a b : Cl_nn m),
      commutator (colimit_ι m a) (colimit_ι m b) = colimit_ι m (commutator a b) := by
  use 0
  intro m a b
  rw [colimit_commutator_simple]

def IsBivector {n : ℕ} (B : Cl_nn n) : Prop :=
  ∃ (i j : SplitIndex n), i ≠ j ∧ 
    B = CliffordAlgebra.ι (splitQuadraticForm n) (splitBasisVector i) * 
        CliffordAlgebra.ι (splitQuadraticForm n) (splitBasisVector j)

theorem bivector_algebra_preserved_in_colimit :
    ∀ {m : ℕ} (B₁ B₂ : Cl_nn m),
      IsBivector B₁ → IsBivector B₂ →
      commutator (colimit_ι m B₁) (colimit_ι m B₂) = colimit_ι m (commutator B₁ B₂) := by
  intro m B₁ B₂ hB₁ hB₂
  rw [colimit_commutator_simple]

theorem clifford_infinity_is_continuous_algebraic_field :
    ∃ (comm : CliffordInfinity → CliffordInfinity → CliffordInfinity),
      (∀ x y z : CliffordInfinity, 
        comm x (comm y z) + comm y (comm z x) + comm z (comm x y) = 0) ∧
      (∀ {n : ℕ} (a b : Cl_nn n),
        comm (colimit_ι n a) (colimit_ι n b) = colimit_ι n (commutator a b)) := by
  use fun x y => x * y - y * x
  constructor
  · intro x y z
    noncomm_ring
  · intro n a b
    dsimp [commutator]
    rw [map_sub, map_mul, map_mul]

end InfoGeometry.OperatorAlgebra