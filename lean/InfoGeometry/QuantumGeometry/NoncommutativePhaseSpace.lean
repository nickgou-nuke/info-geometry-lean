import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.QuantumGeometry.PhaseSpace

variable {A: Type*} [Ring A]

structure Derivation (A: Type*) [Ring A] where
  toFun : A → A
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  leibniz' : ∀ x y, toFun (x * y) = toFun x * y + x * toFun y

instance : CoeFun (Derivation A) (fun _ => A → A) where
  coe D := D.toFun

namespace Derivation

variable (D: Derivation A)

@[simp] theorem map_add (x y: A) : D (x + y) = D x + D y := D.map_add' x y
@[simp] theorem leibniz (x y: A) : D (x * y) = D x * y + x * D y := D.leibniz' x y

/-- The Lie Bracket of derivations: [D₁, D₂] = D₁ ∘ D₂ - D₂ ∘ D₁. -/
def bracket (D₁ D₂: Derivation A) (x: A) : A :=
  D₁ (D₂ x) - D₂ (D₁ x)

theorem bracket_leibniz (D₁ D₂: Derivation A) (x y: A) :
    bracket D₁ D₂ (x * y) = (bracket D₁ D₂ x) * y + x * (bracket D₁ D₂ y) := by
  dsimp [bracket]
  simp only [Derivation.leibniz, Derivation.map_add]
  simp only [mul_sub, sub_mul]
  abel

def commutator (D₁ D₂: Derivation A) : Derivation A where
  toFun := bracket D₁ D₂
  map_add' x y := by
    dsimp [bracket]
    rw [D₂.map_add, D₁.map_add, D₁.map_add, D₂.map_add]
    abel
  leibniz' := bracket_leibniz D₁ D₂

end Derivation

def opComm (T₁ T₂: A → A) (X: A) : A :=
  T₁ (T₂ X) - T₂ (T₁ X)

@[simp] theorem opComm_apply (T₁ T₂: A → A) (X: A) :
    opComm T₁ T₂ X = T₁ (T₂ X) - T₂ (T₁ X) := rfl

def opQ (K: A) (X: A) : A :=
  K * X

@[simp] theorem opQ_apply (K X: A) : opQ K X = K * X := rfl

def opP (D: Derivation A) (X: A) : A :=
  D X

@[simp] theorem opP_apply (D: Derivation A) (X: A) : opP D X = D X := rfl

theorem ccr_coordinate_coordinate (K₁ K₂ X: A) :
    opComm (opQ K₁) (opQ K₂) X = opQ (K₁ * K₂ - K₂ * K₁) X := by
  dsimp [opComm, opQ]
  simp only [mul_assoc, sub_mul]

theorem ccr_momentum_momentum (D₁ D₂: Derivation A) (X: A) :
    opComm (opP D₁) (opP D₂) X = opP (Derivation.commutator D₁ D₂) X := by
  dsimp [opComm, opP, Derivation.commutator, Derivation.bracket]

theorem ccr_momentum_coordinate (D: Derivation A) (K X: A) :
    opComm (opP D) (opQ K) X = opQ (D K) X := by
  dsimp [opComm, opP, opQ]
  rw [D.leibniz]
  abel

theorem ccr_heisenberg_canonical (D: Derivation A) (K: A) (hDK: D K = 1) (X: A) :
    opComm (opP D) (opQ K) X = X := by
  rw [ccr_momentum_coordinate D K X, hDK]
  dsimp [opQ]
  exact one_mul X

theorem ccr_adiabatic_commute (D: Derivation A) (K: A) (hDK: D K = 0) (X: A) :
    opComm (opP D) (opQ K) X = 0 := by
  rw [ccr_momentum_coordinate D K X, hDK]
  dsimp [opQ]
  exact zero_mul X

end InfoGeometry.QuantumGeometry.PhaseSpace

end noncomputable section
