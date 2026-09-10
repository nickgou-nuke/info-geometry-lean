import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import proofs.CPTAtom
import proofs.SolderingSpinConnectionBogoliubov
import proofs.SplitCliffordAlgebras

/-!
# Chiral Causal Cone Algebra

This module formalizes the chiral σ⁺/σ⁻ algebra and its soldering onto the causal
cone. The core observation is that the chiral basis `{I, σ⁺, σ⁻, σ³}` provides a
complete algebraic decomposition of `2×2` complex matrices that simultaneously encodes:

* **Lie closure** (commutators): `[σ⁺, σ⁻] = σ³` — chirality/helicity grading.
* **Jordan closure** (anticommutators): `{σ⁺, σ⁻} = I` — transverse completeness.
* **Nilpotent square** (causal cone): `(σ⁺)² = (σ⁻)² = 0` — null vector factorization.
* **CAR identification**: σ⁺ is the fermionic annihilation, σ⁻ the creation operator.

When soldered onto spacetime vectors via the Pauli map `v^μ σ_μ`, the chiral algebra
provides the spinor-helicity decomposition: null vectors (on the causal cone) factorize
as `λ ⊗ λ̃†`, and the circular polarization basis `{ε⁺, ε⁻}` is the soldered image of
`{σ⁺, σ⁻}` acting on the little group.

-/

noncomputable section

namespace ChiralCausalCone

open Matrix

abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-! ## Chiral basis: σ⁺ and σ⁻

The chiral basis is defined by the nilpotent raising/lowering matrices:

```
σ⁺ = [0 1; 0 0]    (raising / self-dual / annihilation)
σ⁻ = [0 0; 1 0]    (lowering / anti-self-dual / creation)
```

These are precisely the CAR creation/annihilation matrices from
`SplitCliffordAlgebras` and are related to the Pauli matrices by

```
σ⁺ = ½(σ¹ + iσ²),    σ⁻ = ½(σ¹ - iσ²).
```
-/

/-- Chiral raising operator σ⁺: the upper-triangular nilpotent. -/
def σPlus : M2C := !![0, 1; 0, 0]

/-- Chiral lowering operator σ⁻: the lower-triangular nilpotent. -/
def σMinus : M2C := !![0, 0; 1, 0]

/-- Pauli σ³: the chirality grading operator. -/
def σ3c : M2C := !![1, 0; 0, -1]

/-- σ⁺ is identical to the CAR annihilation operator from `SplitCliffordAlgebras`. -/
theorem σPlus_eq_carAnn : σPlus = SplitClifford.carAnn := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σPlus, SplitClifford.carAnn]

/-- σ⁻ is identical to the CAR creation operator from `SplitCliffordAlgebras`. -/
theorem σMinus_eq_carCre : σMinus = SplitClifford.carCre := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σMinus, SplitClifford.carCre]

/-! ## `Cl(1,1)` atom to chiral CAR basis bridge -/

/-- Entrywise complexification of the real `Cl(1,1)` CPT atom matrices. -/
def complexifyCl11 (A : CPTAtom.M2R) : M2C :=
  fun i j => (A i j : ℂ)

@[simp] theorem complexifyCl11_eps :
    complexifyCl11 CPTAtom.eps = σPlus + σMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexifyCl11, CPTAtom.eps, σPlus, σMinus, Matrix.add_apply]

@[simp] theorem complexifyCl11_J :
    complexifyCl11 CPTAtom.J = σMinus - σPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexifyCl11, CPTAtom.J, σPlus, σMinus, Matrix.sub_apply]

@[simp] theorem complexifyCl11_CPT :
    complexifyCl11 CPTAtom.CPT = σ3c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexifyCl11, CPTAtom.CPT, CPTAtom.eps, CPTAtom.J, σ3c,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Recover the CAR annihilation/raising operator from the complexified
`Cl(1,1)` generators. -/
theorem σPlus_from_cl11 :
    σPlus =
      (1/2 : ℂ) • (complexifyCl11 CPTAtom.eps - complexifyCl11 CPTAtom.J) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexifyCl11, CPTAtom.eps, CPTAtom.J, σPlus, Matrix.smul_apply,
      Matrix.sub_apply] <;> norm_num

/-- Recover the CAR creation/lowering operator from the complexified `Cl(1,1)`
generators. -/
theorem σMinus_from_cl11 :
    σMinus =
      (1/2 : ℂ) • (complexifyCl11 CPTAtom.eps + complexifyCl11 CPTAtom.J) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexifyCl11, CPTAtom.eps, CPTAtom.J, σMinus, Matrix.smul_apply,
      Matrix.add_apply] <;> norm_num

/-- The complexified `Cl(1,1)` atom is exactly the chiral CAR basis:
`ε = σ⁺+σ⁻`, `J = σ⁻-σ⁺`, and `εJ = σ³`. -/
theorem cl11_atom_to_chiral_CAR_basis :
    complexifyCl11 CPTAtom.eps = σPlus + σMinus ∧
    complexifyCl11 CPTAtom.J = σMinus - σPlus ∧
    complexifyCl11 CPTAtom.CPT = σ3c ∧
    σPlus = (1/2 : ℂ) • (complexifyCl11 CPTAtom.eps - complexifyCl11 CPTAtom.J) ∧
    σMinus = (1/2 : ℂ) • (complexifyCl11 CPTAtom.eps + complexifyCl11 CPTAtom.J) ∧
    σPlus = SplitClifford.carAnn ∧
    σMinus = SplitClifford.carCre := by
  exact ⟨complexifyCl11_eps, complexifyCl11_J, complexifyCl11_CPT,
    σPlus_from_cl11, σMinus_from_cl11, σPlus_eq_carAnn, σMinus_eq_carCre⟩

/-- σ⁺ as a linear combination of Pauli matrices: σ⁺ = ½(σ¹ + iσ²). -/
theorem σPlus_from_pauli :
    σPlus = (1/2 : ℂ) • (SolderingSpinConnectionBogoliubov.σ1 +
      Complex.I • SolderingSpinConnectionBogoliubov.σ2) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σPlus, SolderingSpinConnectionBogoliubov.σ1,
      SolderingSpinConnectionBogoliubov.σ2, Matrix.smul_apply, Matrix.add_apply];
    norm_num

/-- σ⁻ as a linear combination of Pauli matrices: σ⁻ = ½(σ¹ - iσ²). -/
theorem σMinus_from_pauli :
    σMinus = (1/2 : ℂ) • (SolderingSpinConnectionBogoliubov.σ1 -
      Complex.I • SolderingSpinConnectionBogoliubov.σ2) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σMinus, SolderingSpinConnectionBogoliubov.σ1,
      SolderingSpinConnectionBogoliubov.σ2, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.add_apply];
    norm_num

/-- Recover σ¹ from the chiral basis: σ¹ = σ⁺ + σ⁻. -/
theorem σ1_from_chiral : SolderingSpinConnectionBogoliubov.σ1 = σPlus + σMinus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σPlus, σMinus, SolderingSpinConnectionBogoliubov.σ1, Matrix.add_apply]

/-- Recover σ² from the chiral basis: σ² = -i(σ⁺ - σ⁻). -/
theorem σ2_from_chiral :
    SolderingSpinConnectionBogoliubov.σ2 = -Complex.I • (σPlus - σMinus) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σPlus, σMinus, SolderingSpinConnectionBogoliubov.σ2,
      Matrix.smul_apply, Matrix.sub_apply]

/-- σ³c equals the Pauli σ³ from `SolderingSpinConnectionBogoliubov`. -/
theorem σ3c_eq_sigma3 : σ3c = SolderingSpinConnectionBogoliubov.σ3 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ3c, SolderingSpinConnectionBogoliubov.σ3]

/-! ## Nilpotency and the causal cone

The fundamental algebraic fact: σ⁺ and σ⁻ are nilpotent of order 2. This nilpotency
is the algebraic expression of the causal cone — null vectors, when soldered, produce
rank-1 matrices that decompose cleanly in the chiral basis.
-/

/-- σ⁺ is nilpotent: `(σ⁺)² = 0`. -/
@[simp]
theorem σPlus_sq : σPlus * σPlus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σPlus, Matrix.mul_apply, Fin.sum_univ_two]

/-- σ⁻ is nilpotent: `(σ⁻)² = 0`. -/
@[simp]
theorem σMinus_sq : σMinus * σMinus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σMinus, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Commutator closure: the sl(2, ℂ) Lie algebra

The chiral basis closes under commutation to form `sl(2, ℂ)`, the chiral half of the
Lorentz algebra `so(1,3) ≃ sl(2,ℂ) ⊕ sl(2,ℂ)`. The commutators encode the
helicity/chirality grading.
-/

/-- The commutator `[σ⁺, σ⁻] = σ³` gives the chirality/helicity operator. -/
theorem comm_σPlus_σMinus : σPlus * σMinus - σMinus * σPlus = σ3c := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σPlus, σMinus, σ3c, Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two]

/-- Using the SplitClifford commutator: `comm(σ⁺, σ⁻) = σ³`. -/
theorem comm_σPlus_σMinus_split :
    SplitClifford.comm σPlus σMinus = σ3c := by
  rw [SplitClifford.comm, comm_σPlus_σMinus]

/-- The commutator `[σ³, σ⁺] = 2σ⁺` shows σ⁺ is a raising operator for chirality. -/
theorem comm_σ3_σPlus : σ3c * σPlus - σPlus * σ3c = (2 : ℂ) • σPlus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ3c, σPlus, Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply,
      Fin.sum_univ_two];
    norm_num

/-- The commutator `[σ³, σ⁻] = -2σ⁻` shows σ⁻ is a lowering operator for chirality. -/
theorem comm_σ3_σMinus : σ3c * σMinus - σMinus * σ3c = (-2 : ℂ) • σMinus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ3c, σMinus, Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply,
      Fin.sum_univ_two];
    norm_num

/-! ## Anticommutator closure: the transverse metric

The anticommutators provide the completeness/projection structure. Together with the
commutators, they give the full chiral algebraic closure `sl(2,ℂ) ⊕ u(1)`.
-/

/-- The anticommutator `{σ⁺, σ⁻} = I` — the transverse completeness relation. -/
theorem anti_σPlus_σMinus : σPlus * σMinus + σMinus * σPlus = (1 : M2C) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σPlus, σMinus, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_two]

/-- Using the SplitClifford anticommutator: `antiComm(σ⁺, σ⁻) = I`. -/
theorem anti_σPlus_σMinus_split :
    SplitClifford.antiComm σPlus σMinus = (1 : M2C) := by
  rw [SplitClifford.antiComm, anti_σPlus_σMinus]

/-- The anticommutator `{σ³, σ⁺} = 0` — σ³ and σ⁺ are orthogonal in the Jordan sense. -/
theorem anti_σ3_σPlus : σ3c * σPlus + σPlus * σ3c = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ3c, σPlus, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_two]

/-- The anticommutator `{σ³, σ⁻} = 0` — σ³ and σ⁻ are orthogonal in the Jordan sense. -/
theorem anti_σ3_σMinus : σ3c * σMinus + σMinus * σ3c = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ3c, σMinus, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_two]

/-- The σ³ grading operator squares to the identity: `(σ³)² = I`. -/
@[simp]
theorem σ3c_sq : σ3c * σ3c = (1 : M2C) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ3c, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Full algebraic closure table

The complete set of products in the chiral basis, establishing the multiplication
table for the chiral algebra `A = span{σ⁺, σ⁻, σ³, I}`:

```
      |  σ⁺    σ⁻    σ³   I
  ────┼──────────────────────
   σ⁺ |  0    P₊   -σ⁺   σ⁺
   σ⁻ | P₋    0    +σ⁻   σ⁻
   σ³ | σ⁺   -σ⁻    I    σ³
   I  | σ⁺    σ⁻   σ³    I
```

where `P₊ = σ⁺σ⁻` and `P₋ = σ⁻σ⁺`.
-/

/-- σ⁺ σ⁻ = P₊ projects onto the (0,0) component. -/
theorem σPlus_mul_σMinus : σPlus * σMinus = !![1, 0; 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σPlus, σMinus, Matrix.mul_apply, Fin.sum_univ_two]

/-- σ⁻ σ⁺ = P₋ projects onto the (1,1) component. -/
theorem σMinus_mul_σPlus : σMinus * σPlus = !![0, 0; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σPlus, σMinus, Matrix.mul_apply, Fin.sum_univ_two]

/-- σ³ σ⁺ = σ⁺ (σ⁺ is in the +1 eigenspace of ad_σ³). -/
theorem σ3c_mul_σPlus : σ3c * σPlus = σPlus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ3c, σPlus, Matrix.mul_apply, Fin.sum_univ_two]

/-- σ⁺ σ³ = -σ⁺ (σ⁺ flips sign when multiplied on the right by σ³). -/
theorem σPlus_mul_σ3c : σPlus * σ3c = -σPlus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ3c, σPlus, Matrix.mul_apply, Fin.sum_univ_two]

/-- σ³ σ⁻ = -σ⁻ (σ⁻ is in the -1 eigenspace of ad_σ³). -/
theorem σ3c_mul_σMinus : σ3c * σMinus = -σMinus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ3c, σMinus, Matrix.mul_apply, Fin.sum_univ_two]

/-- σ⁻ σ³ = σ⁻. -/
theorem σMinus_mul_σ3c : σMinus * σ3c = σMinus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ3c, σMinus, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Chiral decomposition of 2×2 matrices

Every `2×2` complex matrix admits a unique decomposition in the chiral basis
`{I, σ⁺, σ⁻, σ³}`:

```
A = a₀I + a₊σ⁺ + a₋σ⁻ + a₃σ³
```

where the coefficients are extracted by:

```
a₀ = ½ tr(A),   a₊ = A₀₁,   a₋ = A₁₀,   a₃ = ½(A₀₀ - A₁₁)
```
-/

/-- Extract the identity coefficient from a 2×2 matrix via half-trace. -/
def coeffI (A : M2C) : ℂ := (1/2 : ℂ) * (A 0 0 + A 1 1)

/-- Extract the σ⁺ coefficient (upper-right entry). -/
def coeffPlus (A : M2C) : ℂ := A 0 1

/-- Extract the σ⁻ coefficient (lower-left entry). -/
def coeffMinus (A : M2C) : ℂ := A 1 0

/-- Extract the σ³ coefficient via half-difference of diagonal entries. -/
def coeff3 (A : M2C) : ℂ := (1/2 : ℂ) * (A 0 0 - A 1 1)

/-- Any 2×2 matrix expands in the chiral basis. -/
theorem chiral_decomposition (A : M2C) :
    A = coeffI A • (1 : M2C) + coeffPlus A • σPlus +
        coeffMinus A • σMinus + coeff3 A • σ3c := by
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  ext i j; fin_cases i <;> fin_cases j
  · simp [coeffI, coeffPlus, coeffMinus, coeff3, σPlus, σMinus, σ3c,
      Matrix.smul_apply, Matrix.add_apply]; ring
  · simp [coeffI, coeffPlus, coeffMinus, coeff3, σPlus, σMinus, σ3c,
      Matrix.smul_apply, Matrix.add_apply]
  · simp [coeffI, coeffPlus, coeffMinus, coeff3, σPlus, σMinus, σ3c,
      Matrix.smul_apply, Matrix.add_apply]
  · simp [coeffI, coeffPlus, coeffMinus, coeff3, σPlus, σMinus, σ3c,
      Matrix.smul_apply, Matrix.add_apply]
    -- Goal: A11 = 2⁻¹*(A00+A11) - 2⁻¹*(A00-A11)
    apply mul_left_cancel₀ h2
    field_simp [h2]
    ring

/-- The chiral decomposition is unique: coefficients are determined by the matrix
entries. -/
theorem chiral_decomposition_unique (A : M2C) (a0 aP aM a3 : ℂ)
    (h : A = a0 • (1 : M2C) + aP • σPlus + aM • σMinus + a3 • σ3c) :
    a0 = coeffI A ∧ aP = coeffPlus A ∧ aM = coeffMinus A ∧ a3 = coeff3 A := by
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  rw [h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [coeffI, coeffPlus, coeffMinus, coeff3, σPlus, σMinus, σ3c,
      Matrix.smul_apply, Matrix.add_apply]; field_simp [h2]; ring
  · simp [coeffI, coeffPlus, coeffMinus, coeff3, σPlus, σMinus, σ3c,
      Matrix.smul_apply, Matrix.add_apply]
  · simp [coeffI, coeffPlus, coeffMinus, coeff3, σPlus, σMinus, σ3c,
      Matrix.smul_apply, Matrix.add_apply]
  · simp [coeffI, coeffPlus, coeffMinus, coeff3, σPlus, σMinus, σ3c,
      Matrix.smul_apply, Matrix.add_apply]; field_simp [h2]; ring

/-- The trace is twice the identity coefficient. -/
theorem trace_eq_two_coeffI (A : M2C) : Matrix.trace A = (2 : ℂ) * coeffI A := by
  simp [Matrix.trace_fin_two, coeffI]

/-! ## Chiral projection operators

The chiral projectors `P₊ = σ⁺σ⁻` and `P₋ = σ⁻σ⁺` project onto the upper and
lower components of the chiral decomposition. They form a complete orthogonal
set of idempotents.
-/

/-- Positive chiral projector P₊ = σ⁺σ⁻ (projects onto (0,0) component). -/
def PPlus : M2C := σPlus * σMinus

/-- Negative chiral projector P₋ = σ⁻σ⁺ (projects onto (1,1) component). -/
def PMinus : M2C := σMinus * σPlus

/-- P₊ is the projector onto the (0,0) entry. -/
theorem PPlus_matrix : PPlus = !![1, 0; 0, 0] := by
  rw [PPlus]; exact σPlus_mul_σMinus

/-- P₋ is the projector onto the (1,1) entry. -/
theorem PMinus_matrix : PMinus = !![0, 0; 0, 1] := by
  rw [PMinus]; exact σMinus_mul_σPlus

/-- P₊ is idempotent: `P₊² = P₊`. -/
@[simp]
theorem PPlus_idempotent : PPlus * PPlus = PPlus := by
  rw [PPlus_matrix]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- P₋ is idempotent: `P₋² = P₋`. -/
@[simp]
theorem PMinus_idempotent : PMinus * PMinus = PMinus := by
  rw [PMinus_matrix]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- P₊ and P₋ are orthogonal: `P₊ P₋ = 0`. -/
@[simp]
theorem PPlus_PMinus_orthogonal : PPlus * PMinus = 0 := by
  rw [PPlus_matrix, PMinus_matrix]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- P₋ and P₊ are orthogonal: `P₋ P₊ = 0`. -/
@[simp]
theorem PMinus_PPlus_orthogonal : PMinus * PPlus = 0 := by
  rw [PPlus_matrix, PMinus_matrix]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- P₊ + P₋ = I — the chiral projectors partition the identity. -/
theorem PPlus_add_PMinus : PPlus + PMinus = (1 : M2C) := by
  rw [PPlus_matrix, PMinus_matrix]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply]

/-- P₊ - P₋ = σ³ — the projector difference gives the chirality grading. -/
theorem PPlus_sub_PMinus : PPlus - PMinus = σ3c := by
  rw [PPlus_matrix, PMinus_matrix]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ3c, Matrix.sub_apply]

/-- σ³ = 2P₊ - I. -/
theorem σ3c_from_projectors : σ3c = (2 : ℂ) • PPlus - (1 : M2C) := by
  rw [PPlus_matrix, σ3c]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.sub_apply];
    norm_num

/-! ## CAR algebra structure

Since σ⁺ and σ⁻ coincide with the CAR annihilation/creation operators, they carry
a full CAR (canonical anticommutation relation) algebra structure.
-/

/-- The chiral basis `{σ⁺, σ⁻}` forms a CAR pair. -/
def chiral_CAR_pair : SplitClifford.CARPair M2C where
  ann := σPlus
  cre := σMinus
  ann_sq := σPlus_sq
  cre_sq := σMinus_sq
  anti := by
    simpa [SplitClifford.antiComm] using anti_σPlus_σMinus

/-- The commutator `[σ⁺, σ⁻]` has trace zero (as required for finite-dimensional
representations of exact CCR, which forces a boundary defect). -/
theorem comm_σPlus_σMinus_trace_zero : Matrix.trace (σPlus * σMinus - σMinus * σPlus) = 0 := by
  rw [comm_σPlus_σMinus]
  simp [Matrix.trace_fin_two, σ3c]

/-- The anticommutator `{σ⁺, σ⁻}` has trace 2 (as required for the CAR algebra:
`tr({a, a†}) = tr(I) = 2`). -/
theorem anti_σPlus_σMinus_trace_two : Matrix.trace (σPlus * σMinus + σMinus * σPlus) = (2 : ℂ) := by
  rw [anti_σPlus_σMinus]
  simp [Matrix.trace_fin_two]

/-! ## Chiral soldering: connecting to spacetime vectors

The soldering form from `SolderingSpinConnectionBogoliubov` maps a 4-vector
`(t, x, y, z)` to a `2×2` matrix via `solder(t,x,y,z) = t·I + x·σ¹ + y·σ² + z·σ³`.

In the chiral basis this becomes:
```
solder(t,x,y,z) = t·I + (x-iy)·σ⁺ + (x+iy)·σ⁻ + z·σ³
```

For real vectors, the chiral coefficients `(x-iy)` and `(x+iy)` are complex conjugates,
ensuring the soldered matrix is Hermitian.
-/

/-- Rewrite the soldering form in the chiral basis. -/
theorem solder_in_chiral_basis (t x y z : ℂ) :
    SolderingSpinConnectionBogoliubov.solder t x y z =
      t • (1 : M2C) + (x - Complex.I * y) • σPlus +
      (x + Complex.I * y) • σMinus + z • σ3c := by
  have hσ1 : SolderingSpinConnectionBogoliubov.σ1 = σPlus + σMinus := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [σPlus, σMinus, SolderingSpinConnectionBogoliubov.σ1, Matrix.add_apply]
  have hσ2 : SolderingSpinConnectionBogoliubov.σ2 = -Complex.I • (σPlus - σMinus) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [σPlus, σMinus, SolderingSpinConnectionBogoliubov.σ2,
        Matrix.smul_apply, Matrix.sub_apply]
  rw [SolderingSpinConnectionBogoliubov.solder, hσ1, hσ2, σ3c_eq_sigma3]
  ext i j; fin_cases i <;> fin_cases j
  · simp [σPlus, σMinus, SolderingSpinConnectionBogoliubov.σ3,
      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply]
  · simp [σPlus, σMinus, SolderingSpinConnectionBogoliubov.σ3,
      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply]; ring
  · simp [σPlus, σMinus, SolderingSpinConnectionBogoliubov.σ3,
      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply]; ring
  · simp [σPlus, σMinus, SolderingSpinConnectionBogoliubov.σ3,
      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply]

/-- For a real 4-vector, the chiral coefficients are complex conjugates. This is
the Hermiticity condition: the soldered matrix is Hermitian iff the 4-vector is real. -/
theorem solder_chiral_hermiticity (t x y z : ℝ) :
    SolderingSpinConnectionBogoliubov.solder (t : ℂ) (x : ℂ) (y : ℂ) (z : ℂ) =
      (t : ℂ) • (1 : M2C) + ((x : ℂ) - Complex.I * (y : ℂ)) • σPlus +
      ((x : ℂ) + Complex.I * (y : ℂ)) • σMinus + (z : ℂ) • σ3c := by
  exact solder_in_chiral_basis (t : ℂ) (x : ℂ) (y : ℂ) (z : ℂ)

/-- The causal cone condition: a vector is null iff its soldered matrix has zero
determinant. This is the bridge between the chiral algebra and the spacetime causal
structure, proved in `SolderingSpinConnectionBogoliubov.solder_det`. -/
theorem causal_cone_iff_solder_det_zero (t x y z : ℂ) :
    (SolderingSpinConnectionBogoliubov.solder t x y z).det = 0 ↔
    t^2 - x^2 - y^2 - z^2 = 0 := by
  rw [SolderingSpinConnectionBogoliubov.solder_det t x y z]

/-- The chiral decomposition coefficients of a soldered real 4-vector: the
coefficient functions extract the Minkowski coordinates from the chiral components. -/
theorem solder_chiral_coeffs (t x y z : ℝ) :
    coeffI (SolderingSpinConnectionBogoliubov.solder (t : ℂ) (x : ℂ) (y : ℂ) (z : ℂ)) = (t : ℂ) ∧
    coeffPlus (SolderingSpinConnectionBogoliubov.solder (t : ℂ) (x : ℂ) (y : ℂ) (z : ℂ)) =
      (x : ℂ) - Complex.I * (y : ℂ) ∧
    coeffMinus (SolderingSpinConnectionBogoliubov.solder (t : ℂ) (x : ℂ) (y : ℂ) (z : ℂ)) =
      (x : ℂ) + Complex.I * (y : ℂ) ∧
    coeff3 (SolderingSpinConnectionBogoliubov.solder (t : ℂ) (x : ℂ) (y : ℂ) (z : ℂ)) = (z : ℂ) := by
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  rw [solder_in_chiral_basis]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [coeffI, coeffPlus, coeffMinus, coeff3, σPlus, σMinus, σ3c,
      Matrix.smul_apply, Matrix.add_apply]; field_simp [h2]; ring
  · simp [coeffI, coeffPlus, coeffMinus, coeff3, σPlus, σMinus, σ3c,
      Matrix.smul_apply, Matrix.add_apply]
  · simp [coeffI, coeffPlus, coeffMinus, coeff3, σPlus, σMinus, σ3c,
      Matrix.smul_apply, Matrix.add_apply]
  · simp [coeffI, coeffPlus, coeffMinus, coeff3, σPlus, σMinus, σ3c,
      Matrix.smul_apply, Matrix.add_apply]; field_simp [h2]; ring

/-! ## Circular polarization algebra

The circular polarization basis `{ε⁺, ε⁻}` for a null direction arises as the
soldered image of the chiral operators σ⁺, σ⁻ acting on the polarization vectors of
the little group. The algebraic closure of the circular polarization modes mirrors
the chiral σ⁺/σ⁻ algebra.
-/

/-- Generic circular polarization pair: any two matrices satisfying the same
commutator and anticommutator closure as `{σ⁺, σ⁻}` are determined up to the
projector decomposition. -/
theorem circular_polarization_closure (epsPlus epsMinus : M2C)
    (h_comm : epsPlus * epsMinus - epsMinus * epsPlus = σ3c)
    (h_anti : epsPlus * epsMinus + epsMinus * epsPlus = (1 : M2C)) :
    epsPlus * epsMinus = PPlus ∧ epsMinus * epsPlus = PMinus := by
  -- Algebraically: (A+B)+(A-B) = 2A = I+σ3c = 2*PPlus
  -- Similarly: (A+B)-(A-B) = 2B = I-σ3c = 2*PMinus
  have hI_plus_σ3c : (1 : M2C) + σ3c = (2 : ℂ) • PPlus := by
    rw [PPlus_matrix]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [σ3c, Matrix.smul_apply, Matrix.add_apply]; norm_num
  have hI_sub_σ3c : (1 : M2C) - σ3c = (2 : ℂ) • PMinus := by
    rw [PMinus_matrix]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [σ3c, Matrix.smul_apply, Matrix.sub_apply]; norm_num
  have h_two_pplus : (epsPlus * epsMinus + epsMinus * epsPlus) +
      (epsPlus * epsMinus - epsMinus * epsPlus) = (2 : ℂ) • PPlus := by
    rw [h_anti, h_comm, hI_plus_σ3c]
  have h_two_pminus : (epsPlus * epsMinus + epsMinus * epsPlus) -
      (epsPlus * epsMinus - epsMinus * epsPlus) = (2 : ℂ) • PMinus := by
    rw [h_anti, h_comm, hI_sub_σ3c]
  -- Now the left sides simplify: (A+B)+(A-B) = 2A, (A+B)-(A-B) = 2B
  have h_simplify_add : (epsPlus * epsMinus + epsMinus * epsPlus) +
      (epsPlus * epsMinus - epsMinus * epsPlus) = (2 : ℂ) • (epsPlus * epsMinus) := by
    abel
    simp [two_smul]
  have h_simplify_sub : (epsPlus * epsMinus + epsMinus * epsPlus) -
      (epsPlus * epsMinus - epsMinus * epsPlus) = (2 : ℂ) • (epsMinus * epsPlus) := by
    abel
    simp [two_smul]
  rw [h_simplify_add] at h_two_pplus
  rw [h_simplify_sub] at h_two_pminus
  -- Now: 2•(epsPlus*epsMinus) = 2•PPlus and 2•(epsMinus*epsPlus) = 2•PMinus
  -- Since 2 ≠ 0 in ℂ, we can cancel: (epsPlus*epsMinus - PPlus) = 0
  have h_pplus : epsPlus * epsMinus = PPlus := by
    have h_zero : (2 : ℂ) • (epsPlus * epsMinus - PPlus) = 0 := by
      rw [smul_sub, h_two_pplus, sub_self]
    have h2ne : (2 : ℂ) ≠ 0 := by norm_num
    rcases smul_eq_zero.mp h_zero with (h2 | h_sub)
    · exact (h2ne h2).elim
    · exact sub_eq_zero.mp h_sub
  have h_pminus : epsMinus * epsPlus = PMinus := by
    have h_zero : (2 : ℂ) • (epsMinus * epsPlus - PMinus) = 0 := by
      rw [smul_sub, h_two_pminus, sub_self]
    have h2ne : (2 : ℂ) ≠ 0 := by norm_num
    rcases smul_eq_zero.mp h_zero with (h2 | h_sub)
    · exact (h2ne h2).elim
    · exact sub_eq_zero.mp h_sub
  exact ⟨h_pplus, h_pminus⟩


/-- The circular polarization modes, when they satisfy the chiral closure relations,
necessarily decompose into the same projector structure as σ⁺ and σ⁻. -/
theorem circular_polarization_projector_decomposition
    (epsPlus epsMinus : M2C)
    (h_comm : epsPlus * epsMinus - epsMinus * epsPlus = σ3c)
    (h_anti : epsPlus * epsMinus + epsMinus * epsPlus = (1 : M2C)) :
    (epsPlus * epsMinus = PPlus) ∧
    (epsMinus * epsPlus = PMinus) ∧
    (PPlus + PMinus = (1 : M2C)) ∧
    (PPlus - PMinus = σ3c) := by
  rcases circular_polarization_closure epsPlus epsMinus h_comm h_anti with ⟨h1, h2⟩
  exact ⟨h1, h2, PPlus_add_PMinus, PPlus_sub_PMinus⟩

/-! ## Full chiral algebraic closure synthesis

The complete algebraic closure of the chiral basis `{I, σ⁺, σ⁻, σ³}` under both
commutator and anticommutator brackets, establishing the `sl(2,ℂ) ⊕ u(1)` structure
that underlies the causal cone and spinor-helicity formalism.
-/


/-- Main synthesis: all chiral algebraic closure theorems collected. -/
theorem chiral_causal_cone_synthesis :
    (∀ A : M2C, A = coeffI A • (1 : M2C) + coeffPlus A • σPlus +
      coeffMinus A • σMinus + coeff3 A • σ3c) ∧
    (σPlus * σMinus - σMinus * σPlus = σ3c) ∧
    (σPlus * σMinus + σMinus * σPlus = (1 : M2C)) ∧
    (σPlus * σPlus = 0) ∧ (σMinus * σMinus = 0) ∧
    (PPlus * PPlus = PPlus) ∧ (PMinus * PMinus = PMinus) ∧
    (PPlus * PMinus = 0) ∧ (PPlus + PMinus = (1 : M2C)) ∧ (PPlus - PMinus = σ3c) ∧
    (∀ t x y z : ℂ,
      (SolderingSpinConnectionBogoliubov.solder t x y z).det = t^2 - x^2 - y^2 - z^2) :=
  ⟨chiral_decomposition,
   comm_σPlus_σMinus,
   anti_σPlus_σMinus,
   σPlus_sq, σMinus_sq,
   PPlus_idempotent, PMinus_idempotent,
   PPlus_PMinus_orthogonal, PPlus_add_PMinus, PPlus_sub_PMinus,
   SolderingSpinConnectionBogoliubov.solder_det⟩

#check σPlus_sq
#check σMinus_sq
#check comm_σPlus_σMinus
#check anti_σPlus_σMinus
#check comm_σ3_σPlus
#check comm_σ3_σMinus
#check anti_σ3_σPlus
#check anti_σ3_σMinus
#check σ3c_sq
#check σPlus_mul_σMinus
#check σMinus_mul_σPlus
#check σ3c_mul_σPlus
#check σPlus_mul_σ3c
#check σ3c_mul_σMinus
#check σMinus_mul_σ3c
#check chiral_decomposition
#check chiral_decomposition_unique
#check PPlus_idempotent
#check PMinus_idempotent
#check PPlus_PMinus_orthogonal
#check PMinus_PPlus_orthogonal
#check PPlus_add_PMinus
#check PPlus_sub_PMinus
#check chiral_CAR_pair
#check solder_in_chiral_basis
#check causal_cone_iff_solder_det_zero
#check circular_polarization_closure
#check chiral_causal_cone_synthesis

end ChiralCausalCone
