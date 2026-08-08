import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Cl(1,1) → osp(1|2) superbracket boundary

This file owns the basic split `Cl(1,1)` generators and proves the local CAR
relations for the split-null fermionic ladder symbols.  The remaining
`osp(1|2)` supercharge relation still requires a genuine bosonic oscillator
surface; that full representation-level closure is kept as an explicit target
predicate rather than derived from insufficient Clifford data.
-/

open CliffordAlgebra
open QuadraticMap

noncomputable section

namespace InfoGeometry.Algebra.Cl11OSp12

/-! ## 1. Cl(1,1) generators -/

def q11 : QuadraticForm ℚ (Fin 2 → ℚ) := proj 0 0 - proj 1 1

def e₀ : CliffordAlgebra q11 := ι q11 (fun i => if i = 0 then 1 else 0)
def e₁ : CliffordAlgebra q11 := ι q11 (fun i => if i = 1 then 1 else 0)

theorem e₀_sq : e₀ * e₀ = 1 := by
  calc e₀ * e₀ = algebraMap ℚ (CliffordAlgebra q11) (q11 (fun i => if i = 0 then 1 else 0)) := ι_sq_scalar _ _
    _ = 1 := by simp [q11, proj_apply]

theorem e₁_sq : e₁ * e₁ = -1 := by
  calc e₁ * e₁ = algebraMap ℚ (CliffordAlgebra q11) (q11 (fun i => if i = 1 then 1 else 0)) := ι_sq_scalar _ _
    _ = -1 := by simp [q11, proj_apply]

theorem e₀_e₁_orth : q11.IsOrtho (fun i => if i = 0 then 1 else 0) (fun i => if i = 1 then 1 else 0) := by
  simp [q11, IsOrtho, proj_apply]

theorem anticomm : e₀ * e₁ + e₁ * e₀ = 0 := by
  have h := ι_mul_ι_add_swap_of_isOrtho e₀_e₁_orth
  simpa [e₀, e₁] using h

/-! ## 2. Fermionic oscillator symbols -/

def b : CliffordAlgebra q11 := (1/2 : ℚ) • (e₀ + e₁)
def bdag : CliffordAlgebra q11 := (1/2 : ℚ) • (e₀ - e₁)

/-- Central scalar `1/2`, used to normalize the split-null ladder symbols. -/
def a : CliffordAlgebra q11 := algebraMap ℚ (CliffordAlgebra q11) (1/2 : ℚ)

lemma a_comm (x : CliffordAlgebra q11) : a * x = x * a := by
  calc
    a * x = (algebraMap ℚ (CliffordAlgebra q11) (1/2 : ℚ)) * x := rfl
    _ = x * (algebraMap ℚ (CliffordAlgebra q11) (1/2 : ℚ)) := Algebra.commutes (1/2 : ℚ) x
    _ = x * a := rfl

lemma a_mul_mul (x y : CliffordAlgebra q11) : (a*x)*(a*y) = (a*a)*(x*y) := by
  calc
    (a*x)*(a*y) = (a*x)*a*y := by simp [mul_assoc]
    _ = a*(x*a)*y := by simp [mul_assoc]
    _ = a*(a*x)*y := by rw [a_comm x]
    _ = (a*a)*(x*y) := by simp [mul_assoc]

/-- The annihilation ladder is square-zero. -/
theorem b_sq : b * b = 0 := by
  have hb : b = a * (e₀ + e₁) := by simp [b, a, Algebra.smul_def]
  have h_expand : (e₀+e₁)*(e₀+e₁) = e₀*e₁ + e₁*e₀ := by
    calc
      (e₀+e₁)*(e₀+e₁) = e₀*e₀ + e₀*e₁ + e₁*e₀ + e₁*e₁ := by noncomm_ring
      _ = 1 + e₀*e₁ + e₁*e₀ + (-1) := by simp [e₀_sq, e₁_sq]
      _ = e₀*e₁ + e₁*e₀ := by abel
  calc
    b * b = (a * (e₀+e₁)) * (a * (e₀+e₁)) := by rw [hb]
    _ = (a*a)*((e₀+e₁)*(e₀+e₁)) := by simp [a_mul_mul]
    _ = (a*a)*(e₀*e₁ + e₁*e₀) := by rw [h_expand]
    _ = (a*a)*0 := by rw [anticomm]
    _ = 0 := by simp

/-- The creation ladder is square-zero. -/
theorem bdag_sq : bdag * bdag = 0 := by
  have hb : bdag = a * (e₀ - e₁) := by simp [bdag, a, Algebra.smul_def]
  have h_expand : (e₀-e₁)*(e₀-e₁) = -(e₀*e₁ + e₁*e₀) := by
    calc
      (e₀-e₁)*(e₀-e₁) = e₀*e₀ - e₀*e₁ - e₁*e₀ + e₁*e₁ := by noncomm_ring
      _ = 1 - e₀*e₁ - e₁*e₀ + (-1) := by simp [e₀_sq, e₁_sq]
      _ = -(e₀*e₁ + e₁*e₀) := by abel
  calc
    bdag * bdag = (a * (e₀-e₁)) * (a * (e₀-e₁)) := by rw [hb]
    _ = (a*a)*((e₀-e₁)*(e₀-e₁)) := by simp [a_mul_mul]
    _ = (a*a)*(-(e₀*e₁ + e₁*e₀)) := by rw [h_expand]
    _ = (a*a)*0 := by simp [anticomm]
    _ = 0 := by simp

/-- The split-null ladders satisfy the mixed CAR relation `{b,b†}=1`. -/
theorem anticomm_bbdag : b * bdag + bdag * b = 1 := by
  have hsum : b + bdag = e₀ := by
    unfold b bdag
    simp [sub_eq_add_neg, smul_add, add_assoc, add_left_comm]
    rw [← add_smul]
    norm_num
  have hsquare : (b + bdag) * (b + bdag) = 1 := by
    rw [hsum, e₀_sq]
  rw [add_mul, mul_add, mul_add] at hsquare
  rw [b_sq, bdag_sq] at hsquare
  simpa [add_assoc, add_comm, add_left_comm] using hsquare

/-! ## 3. osp(1|2) supercharge target boundary -/

def Gplus (_a adag : CliffordAlgebra q11) : CliffordAlgebra q11 := adag * b
def Gminus (a _adag : CliffordAlgebra q11) : CliffordAlgebra q11 := a * bdag

/--
Target closure predicate for the displayed `osp(1|2)` supercharge relation.

The full relation needs a genuine boson/fermion oscillator model.  It is kept as
an explicit target predicate here rather than a theorem derived from
insufficient local Clifford data.
-/
def OSpSuperchargeClosure (a adag : CliffordAlgebra q11) : Prop :=
  Gplus a adag * Gminus a adag + Gminus a adag * Gplus a adag = 2 * adag * a

/-- Read back a supplied `osp(1|2)` supercharge closure target proof. -/
theorem anticomm_Gplus_Gminus
    (a adag : CliffordAlgebra q11)
    (h_closure : OSpSuperchargeClosure a adag) :
    Gplus a adag * Gminus a adag + Gminus a adag * Gplus a adag = 2 * adag * a :=
  h_closure

/-! ## 4. Genuine boson/fermion oscillator closure surface -/

/--
A bosonic oscillator surface with the Heisenberg commutator relation.

This is algebraic carrier data for bounded/formal operator models.  It is not
by itself an analytic construction of an unbounded oscillator representation.
-/
structure BosonicOscillatorSurface (Op : Type*) [Ring Op] where
  a : Op
  adag : Op
  commutator : a * adag - adag * a = 1

/-- Trivial instance of BosonicOscillatorSurface on PUnit. -/
def punitBosonicOscillatorSurface : BosonicOscillatorSurface PUnit where
  a := ⟨⟩
  adag := ⟨⟩
  commutator := rfl

/-- A fermionic CAR surface. -/
structure FermionicCARSurface (Op : Type*) [Ring Op] where
  b : Op
  bdag : Op
  b_sq : b * b = 0
  bdag_sq : bdag * bdag = 0
  anticomm : b * bdag + bdag * b = 1

/-- Trivial instance of FermionicCARSurface on PUnit. -/
def punitFermionicCARSurface : FermionicCARSurface PUnit where
  b := ⟨⟩
  bdag := ⟨⟩
  b_sq := rfl
  bdag_sq := rfl
  anticomm := rfl

/-- The split `Cl(1,1)` ladder pair as a genuine CAR surface. -/
def cl11FermionicCARSurface : FermionicCARSurface (CliffordAlgebra q11) where
  b := b
  bdag := bdag
  b_sq := b_sq
  bdag_sq := bdag_sq
  anticomm := anticomm_bbdag

/--
Compatibility asserting that the bosonic and fermionic oscillator generators
commute as independent tensor factors/readouts.
-/
structure BosonFermionInterface (Op : Type*) [Ring Op]
    (B : BosonicOscillatorSurface Op) (F : FermionicCARSurface Op) where
  a_b : B.a * F.b = F.b * B.a
  adag_b : B.adag * F.b = F.b * B.adag
  a_bdag : B.a * F.bdag = F.bdag * B.a
  adag_bdag : B.adag * F.bdag = F.bdag * B.adag

/-- Trivial instance of BosonFermionInterface on PUnit. -/
def punitBosonFermionInterface : BosonFermionInterface PUnit punitBosonicOscillatorSurface punitFermionicCARSurface where
  a_b := rfl
  adag_b := rfl
  a_bdag := rfl
  adag_bdag := rfl

variable {Op : Type*} [Ring Op]

/-- Positive odd supercharge `Q₊ = a† b`. -/
def Qplus (B : BosonicOscillatorSurface Op) (F : FermionicCARSurface Op) : Op :=
  B.adag * F.b

/-- Negative odd supercharge `Q₋ = a b†`. -/
def Qminus (B : BosonicOscillatorSurface Op) (F : FermionicCARSurface Op) : Op :=
  B.a * F.bdag

/--
The algebraic SUSY oscillator Hamiltonian readout produced by the boson/fermion
factorization.
-/
def susyOscillatorHamiltonian (B : BosonicOscillatorSurface Op) (F : FermionicCARSurface Op) : Op :=
  B.adag * B.a * (F.b * F.bdag) + B.a * B.adag * (F.bdag * F.b)

private theorem qplus_qminus_factor
    (B : BosonicOscillatorSurface Op) (F : FermionicCARSurface Op)
    (I : BosonFermionInterface Op B F) :
    (B.adag * F.b) * (B.a * F.bdag) = B.adag * B.a * (F.b * F.bdag) := by
  calc
    (B.adag * F.b) * (B.a * F.bdag)
        = B.adag * (F.b * B.a) * F.bdag := by noncomm_ring
    _ = B.adag * (B.a * F.b) * F.bdag := by rw [← I.a_b]
    _ = B.adag * B.a * (F.b * F.bdag) := by noncomm_ring

private theorem qminus_qplus_factor
    (B : BosonicOscillatorSurface Op) (F : FermionicCARSurface Op)
    (I : BosonFermionInterface Op B F) :
    (B.a * F.bdag) * (B.adag * F.b) = B.a * B.adag * (F.bdag * F.b) := by
  calc
    (B.a * F.bdag) * (B.adag * F.b)
        = B.a * (F.bdag * B.adag) * F.b := by noncomm_ring
    _ = B.a * (B.adag * F.bdag) * F.b := by rw [← I.adag_bdag]
    _ = B.a * B.adag * (F.bdag * F.b) := by noncomm_ring

/--
Kernel-checked odd--odd supercharge closure for the boson/fermion oscillator
surface.

This proves the algebraic anticommutator identity
`{Q₊, Q₋} = H_susy` for the explicitly defined Hamiltonian readout.  It does
not claim the remaining `osp(1|2)` even-sector brackets, Virasoro stepping, or
an analytic unbounded-operator representation.
-/
theorem osp_supercharge_oscillator_closure
    (B : BosonicOscillatorSurface Op) (F : FermionicCARSurface Op)
    (I : BosonFermionInterface Op B F) :
    Qplus B F * Qminus B F + Qminus B F * Qplus B F =
      susyOscillatorHamiltonian B F := by
  unfold Qplus Qminus susyOscillatorHamiltonian
  rw [qplus_qminus_factor B F I, qminus_qplus_factor B F I]

end InfoGeometry.Algebra.Cl11OSp12
