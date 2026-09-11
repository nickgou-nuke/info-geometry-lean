import InfoGeometry.Quantum.GeneralizedPauli
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TensorTowerColimit
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Sylvester clock-shift colimit bridge

This module gives a native-mathlib integration spine for finite Sylvester
clock/shift systems and the repository's categorical direct-inductive-colimit
owner.

It proves only theorem-safe algebra:

* abstract finite Sylvester clock/shift data on a finite index type;
* the Weyl relation `Z X = q • (X Z)` from the clock-weight covariance law;
* packaging as the existing `FiniteWeylPair` abstraction;
* functorial transport of finite Weyl pairs by complex algebra homomorphisms;
* a direct inductive system of Weyl pairs whose algebra-hom bonding maps are
  also linear maps accepted by `TensorTowerColimit.iota_seq`;
* ambient-cone readouts showing the Weyl relation survives at every finite
  stage mapped into the cone.

It does not assert a full generic Sylvester basis theorem, Hilbert--Schmidt
orthogonality, a Fourier/Vandermonde diagonalization theorem, or a completed
analytic/thermodynamic colimit theorem.
-/

noncomputable section

open Matrix
open scoped BigOperators

namespace InfoGeometry.Quantum.SylvesterColimitBridge

open InfoGeometry.Physics.HestenesCuntzPhaseSpace

/-- Abstract finite Sylvester clock/shift data on a finite index type.

The finite type `ι` is the coordinate register, `shift` is the semantic cyclic
shift, `clockWeight` is the diagonal clock spectrum, and `phase` is the finite
Weyl scalar.  The field `clockWeight_shift` is the exact algebraic content
needed for the Weyl relation. -/
structure AbstractSylvesterData (N : ℕ) (ι : Type*) [Fintype ι] [DecidableEq ι] where
  shift : Equiv.Perm ι
  clockWeight : ι → ℂ
  phase : ℂ
  phase_pow_dim : phase ^ N = 1
  clockWeight_shift : ∀ i, clockWeight (shift i) = phase * clockWeight i

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Sylvester shift matrix associated to a semantic shift permutation. -/
def sylvesterShift (D : AbstractSylvesterData N ι) : Matrix ι ι ℂ :=
  Equiv.Perm.permMatrix ℂ D.shift.symm

/-- The Sylvester clock matrix associated to clock weights. -/
def sylvesterClock (D : AbstractSylvesterData N ι) : Matrix ι ι ℂ :=
  diagonal D.clockWeight

/-- The Weyl--Heisenberg word `X^k Z^j` associated to abstract Sylvester data. -/
def sylvesterWeylHeisenberg (D : AbstractSylvesterData N ι) (k j : ℕ) : Matrix ι ι ℂ :=
  sylvesterShift D ^ k * sylvesterClock D ^ j

/-- The abstract finite Sylvester clock and shift obey the Weyl relation. -/
theorem sylvester_clock_shift_weyl (D : AbstractSylvesterData N ι) :
    sylvesterClock D * sylvesterShift D =
      D.phase • (sylvesterShift D * sylvesterClock D) := by
  ext i j
  rw [sylvesterClock, sylvesterShift, Matrix.diagonal_mul]
  change D.clockWeight i * Equiv.Perm.permMatrix ℂ D.shift.symm i j =
    D.phase * ((Equiv.Perm.permMatrix ℂ D.shift.symm * Matrix.diagonal D.clockWeight) i j)
  rw [Matrix.mul_diagonal]
  by_cases h : D.shift.symm i = j
  · have hi : i = D.shift j := by
      rw [← h]
      simp
    subst i
    simp [Equiv.Perm.permMatrix, D.clockWeight_shift]
  · simp [Equiv.Perm.permMatrix, h]

/-- Abstract Sylvester data is a finite generalized-Pauli/Weyl pair. -/
def abstractSylvesterWeylPair (D : AbstractSylvesterData N ι) :
    FiniteWeylPair N (Matrix ι ι ℂ) where
  coordinate := sylvesterShift D
  momentum := sylvesterClock D
  q := D.phase
  q_pow_dim := D.phase_pow_dim
  weyl_relation := sylvester_clock_shift_weyl D

/-- Algebra homomorphisms transport finite Weyl pairs. -/
def finiteWeylPairMap {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    (W : FiniteWeylPair N A) (φ : A →ₐ[ℂ] B) : FiniteWeylPair N B where
  coordinate := φ W.coordinate
  momentum := φ W.momentum
  q := W.q
  q_pow_dim := W.q_pow_dim
  weyl_relation := by
    rw [← map_mul, W.weyl_relation]
    simp

@[simp] theorem finiteWeylPairMap_coordinate {A B : Type*}
    [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    (W : FiniteWeylPair N A) (φ : A →ₐ[ℂ] B) :
    (finiteWeylPairMap W φ).coordinate = φ W.coordinate := rfl

@[simp] theorem finiteWeylPairMap_momentum {A B : Type*}
    [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    (W : FiniteWeylPair N A) (φ : A →ₐ[ℂ] B) :
    (finiteWeylPairMap W φ).momentum = φ W.momentum := rfl

@[simp] theorem finiteWeylPairMap_q {A B : Type*}
    [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    (W : FiniteWeylPair N A) (φ : A →ₐ[ℂ] B) :
    (finiteWeylPairMap W φ).q = W.q := rfl

/-- A finite-Weyl-pair direct inductive system with algebra-hom bonding maps. -/
structure WeylInductiveSystem (N : ℕ) (A : ℕ → Type*)
    [∀ n, Ring (A n)] [∀ n, Algebra ℂ (A n)] where
  pair : ∀ n, FiniteWeylPair N (A n)
  bond : ∀ n, A n →ₐ[ℂ] A (n + 1)
  coordinate_compatible : ∀ n, bond n ((pair n).coordinate) = (pair (n + 1)).coordinate
  momentum_compatible : ∀ n, bond n ((pair n).momentum) = (pair (n + 1)).momentum
  phase_compatible : ∀ n, (pair (n + 1)).q = (pair n).q

namespace WeylInductiveSystem

variable {A : ℕ → Type*} [∀ n, Ring (A n)] [∀ n, Algebra ℂ (A n)]

/-- The algebra-hom bonding map as the linear map expected by the tensor-tower
colimit owner. -/
def bondLinear (S : WeylInductiveSystem N A) (n : ℕ) : A n →ₗ[ℂ] A (n + 1) :=
  (S.bond n).toLinearMap

/-- The successor bonding map carries the source Weyl relation to the target
Weyl relation. -/
theorem bond_preserves_weyl_relation (S : WeylInductiveSystem N A) (n : ℕ) :
    S.bond n ((S.pair n).momentum * (S.pair n).coordinate) =
      (S.pair (n + 1)).q •
        ((S.pair (n + 1)).coordinate * (S.pair (n + 1)).momentum) := by
  rw [(S.pair n).weyl_relation]
  rw [map_smul, map_mul]
  rw [S.coordinate_compatible n, S.momentum_compatible n, S.phase_compatible n]

/-- A cone from a Weyl inductive system to an ambient algebra. -/
structure Cone (S : WeylInductiveSystem N A) (B : Type*) [Ring B] [Algebra ℂ B] where
  map : ∀ n, A n →ₐ[ℂ] B
  comm : ∀ n, (map (n + 1)).comp (S.bond n) = map n

namespace Cone

variable {S : WeylInductiveSystem N A} {B : Type*} [Ring B] [Algebra ℂ B]

/-- The algebra cone as the linear cone used by `TensorTowerColimit`. -/
def mapLinear (C : Cone S B) (n : ℕ) : A n →ₗ[ℂ] B :=
  (C.map n).toLinearMap

/-- Algebra-cone commutativity in the linear-map form used by the categorical
`TensorTowerColimit` owner. -/
theorem mapLinear_comm (C : Cone S B) (n : ℕ) :
    (C.mapLinear (n + 1)).comp (S.bondLinear n) = C.mapLinear n := by
  ext x
  exact congrFun (congrArg DFunLike.coe (C.comm n)) x

/-- The existing tensor-tower colimit induction applies to the linear maps
underlying a Weyl algebra cone. -/
theorem mapLinear_comp_iota_seq (C : Cone S B) (n m : ℕ) :
    (C.mapLinear (n + m)).comp
        (iota_seq A S.bondLinear n m) = C.mapLinear n := by
  exact psi_comp_iota_seq A S.bondLinear B C.mapLinear C.mapLinear_comm n m

/-- Every finite stage has its Weyl relation after mapping into the ambient cone. -/
theorem stage_weyl_relation_in_cone (C : Cone S B) (n : ℕ) :
    C.map n ((S.pair n).momentum) * C.map n ((S.pair n).coordinate) =
      (S.pair n).q •
        (C.map n ((S.pair n).coordinate) * C.map n ((S.pair n).momentum)) := by
  rw [← map_mul, (S.pair n).weyl_relation]
  simp

/-- Consecutive stages have the same coordinate image in the cone. -/
theorem coordinate_image_succ (C : Cone S B) (n : ℕ) :
    C.map (n + 1) ((S.pair (n + 1)).coordinate) =
      C.map n ((S.pair n).coordinate) := by
  rw [← S.coordinate_compatible n]
  exact congrFun (congrArg DFunLike.coe (C.comm n)) ((S.pair n).coordinate)

/-- Consecutive stages have the same momentum image in the cone. -/
theorem momentum_image_succ (C : Cone S B) (n : ℕ) :
    C.map (n + 1) ((S.pair (n + 1)).momentum) =
      C.map n ((S.pair n).momentum) := by
  rw [← S.momentum_compatible n]
  exact congrFun (congrArg DFunLike.coe (C.comm n)) ((S.pair n).momentum)

end Cone
end WeylInductiveSystem

/-- Consolidated theorem-safe bridge: abstract Sylvester data gives a finite Weyl
pair, and finite Weyl pairs are functorial under algebra homomorphisms. -/
theorem sylvester_colimit_bridge_synthesis
    (D : AbstractSylvesterData N ι)
    {B : Type*} [Ring B] [Algebra ℂ B]
    (φ : Matrix ι ι ℂ →ₐ[ℂ] B) :
    (abstractSylvesterWeylPair D).momentum * (abstractSylvesterWeylPair D).coordinate =
        D.phase • ((abstractSylvesterWeylPair D).coordinate *
          (abstractSylvesterWeylPair D).momentum) ∧
      (finiteWeylPairMap (abstractSylvesterWeylPair D) φ).momentum *
          (finiteWeylPairMap (abstractSylvesterWeylPair D) φ).coordinate =
        D.phase • ((finiteWeylPairMap (abstractSylvesterWeylPair D) φ).coordinate *
          (finiteWeylPairMap (abstractSylvesterWeylPair D) φ).momentum) := by
  exact ⟨(abstractSylvesterWeylPair D).weyl_relation,
    (finiteWeylPairMap (abstractSylvesterWeylPair D) φ).weyl_relation⟩

end InfoGeometry.Quantum.SylvesterColimitBridge
