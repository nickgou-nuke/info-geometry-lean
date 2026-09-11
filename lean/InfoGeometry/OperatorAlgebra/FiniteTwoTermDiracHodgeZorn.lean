import InfoGeometry.OperatorAlgebra.FaithfulOperatorZornEnvelope
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.DiscreteDiracHodgeChiral
import Mathlib.Tactic

/-!
# A specified finite two-term Dirac--Hodge complex

A rectangular real matrix `B : C^0 -> C^1` determines a genuine two-term
cochain complex on `Omega = C^0 x C^1`.  Its exterior derivative and
codifferential are the strict lower and upper blocks

`d(f,g) = (0, B f)`,  `delta(f,g) = (B^T g, 0)`.

Consequently `d^2 = delta^2 = 0`, `D = d + delta`, and
`D^2 = d delta + delta d`.  The parity involution `(f,g) |-> (f,-g)`
anticommutes with both odd maps.

The same maps form an operator-Zorn block.  Summing its two sheet outputs on a
diagonally embedded form recovers `D`; this is the requested explicit
intertwining theorem, not only a resemblance of block shapes.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.FiniteTwoTermDiracHodgeZorn

open Matrix
open InfoGeometry.OperatorAlgebra.FaithfulOperatorZornEnvelope
open InfoGeometry.Canonical

abbrev ZeroForms (n0 : ℕ) := Fin n0 → ℝ
abbrev OneForms (n1 : ℕ) := Fin n1 → ℝ
abbrev TotalForms (n0 n1 : ℕ) := ZeroForms n0 × OneForms n1
abbrev FormEnd (n0 n1 : ℕ) := Module.End ℝ (TotalForms n0 n1)

variable {n0 n1 : ℕ}

/-- Degree-raising differential obtained from the incidence matrix `B`. -/
def exteriorDerivative
    (B : Matrix (Fin n1) (Fin n0) ℝ) : FormEnd n0 n1 where
  toFun omega := (0, B.mulVec omega.1)
  map_add' omega eta := by
    ext <;> simp [Matrix.mulVec_add]
  map_smul' r omega := by
    ext <;> simp [Matrix.mulVec_smul]

/-- Codifferential obtained from the transpose incidence matrix. -/
def codifferential
    (B : Matrix (Fin n1) (Fin n0) ℝ) : FormEnd n0 n1 where
  toFun omega := (B.transpose.mulVec omega.2, 0)
  map_add' omega eta := by
    ext <;> simp [Matrix.mulVec_add]
  map_smul' r omega := by
    ext <;> simp [Matrix.mulVec_smul]

/-- Even/odd form-degree involution. -/
def chirality : FormEnd n0 n1 where
  toFun omega := (omega.1, -omega.2)
  map_add' omega eta := by
    ext <;> simp [add_comm]
  map_smul' r omega := by
    ext <;> simp

@[simp] theorem exteriorDerivative_apply
    (B : Matrix (Fin n1) (Fin n0) ℝ)
    (omega : TotalForms n0 n1) :
    exteriorDerivative B omega = (0, B.mulVec omega.1) := rfl

@[simp] theorem codifferential_apply
    (B : Matrix (Fin n1) (Fin n0) ℝ)
    (omega : TotalForms n0 n1) :
    codifferential B omega = (B.transpose.mulVec omega.2, 0) := rfl

@[simp] theorem chirality_apply (omega : TotalForms n0 n1) :
    chirality omega = (omega.1, -omega.2) := rfl

/-- The strict degree-raising block is nilpotent. -/
@[simp] theorem exteriorDerivative_sq
    (B : Matrix (Fin n1) (Fin n0) ℝ) :
    exteriorDerivative B * exteriorDerivative B = 0 := by
  apply LinearMap.ext
  rintro ⟨f, g⟩
  ext <;> simp

/-- The strict degree-lowering block is nilpotent. -/
@[simp] theorem codifferential_sq
    (B : Matrix (Fin n1) (Fin n0) ℝ) :
    codifferential B * codifferential B = 0 := by
  apply LinearMap.ext
  rintro ⟨f, g⟩
  ext <;> simp

/-- Chirality is an involution. -/
@[simp] theorem chirality_sq :
    (chirality : FormEnd n0 n1) * chirality = 1 := by
  apply LinearMap.ext
  rintro ⟨f, g⟩
  simp [chirality]

/-- Concrete Dirac--Hodge operator `D = d + delta`. -/
def diracHodge
    (B : Matrix (Fin n1) (Fin n0) ℝ) : FormEnd n0 n1 :=
  DiscreteDiracHodgeChiral.diracHodge
    (exteriorDerivative B) (codifferential B)

/-- Concrete Hodge Laplacian. -/
def hodgeLaplacian
    (B : Matrix (Fin n1) (Fin n0) ℝ) : FormEnd n0 n1 :=
  DiscreteDiracHodgeChiral.hodgeLaplacian
    (exteriorDerivative B) (codifferential B)

@[simp] theorem diracHodge_apply
    (B : Matrix (Fin n1) (Fin n0) ℝ)
    (omega : TotalForms n0 n1) :
    diracHodge B omega =
      (B.transpose.mulVec omega.2, B.mulVec omega.1) := by
  ext <;> simp [diracHodge, DiscreteDiracHodgeChiral.diracHodge]

/-- The requested plus-sign Dirac--Kahler identity. -/
theorem diracHodge_sq_eq_hodgeLaplacian
    (B : Matrix (Fin n1) (Fin n0) ℝ) :
    diracHodge B * diracHodge B = hodgeLaplacian B :=
  DiscreteDiracHodgeChiral.diracHodge_sq_eq_hodgeLaplacian
    (exteriorDerivative B) (codifferential B)
    (exteriorDerivative_sq B) (codifferential_sq B)

/-- `d` is odd for form-degree parity. -/
theorem exteriorDerivative_anticommutes_chirality
    (B : Matrix (Fin n1) (Fin n0) ℝ) :
    exteriorDerivative B * chirality =
      -(chirality * exteriorDerivative B) := by
  apply LinearMap.ext
  rintro ⟨f, g⟩
  change exteriorDerivative B (chirality (f, g)) =
    -chirality (exteriorDerivative B (f, g))
  ext <;> simp [exteriorDerivative, chirality]

/-- `delta` is odd for form-degree parity. -/
theorem codifferential_anticommutes_chirality
    (B : Matrix (Fin n1) (Fin n0) ℝ) :
    codifferential B * chirality =
      -(chirality * codifferential B) := by
  apply LinearMap.ext
  rintro ⟨f, g⟩
  change codifferential B (chirality (f, g)) =
    -chirality (codifferential B (f, g))
  ext <;> simp [codifferential, chirality, Matrix.mulVec_neg]

/-- The full `D=d+delta` is odd. -/
theorem diracHodge_anticommutes_chirality
    (B : Matrix (Fin n1) (Fin n0) ℝ) :
    diracHodge B * chirality = -(chirality * diracHodge B) :=
  DiscreteDiracHodgeChiral.diracHodge_anticommutes_chirality
    (exteriorDerivative B) (codifferential B) chirality
    (exteriorDerivative_anticommutes_chirality B)
    (codifferential_anticommutes_chirality B)

/-- The Hodge Laplacian is parity-even. -/
theorem hodgeLaplacian_commutes_chirality
    (B : Matrix (Fin n1) (Fin n0) ℝ) :
    hodgeLaplacian B * chirality = chirality * hodgeLaplacian B :=
  DiscreteDiracHodgeChiral.hodgeLaplacian_commutes_chirality
    (exteriorDerivative B) (codifferential B) chirality
    (exteriorDerivative_sq B) (codifferential_sq B)
    (exteriorDerivative_anticommutes_chirality B)
    (codifferential_anticommutes_chirality B)

/-- Euclidean pairings on the two cochain degrees. -/
def innerZero (f h : ZeroForms n0) : ℝ :=
  ∑ i, f i * h i

def innerOne (g k : OneForms n1) : ℝ :=
  ∑ i, g i * k i

def formPairing
    (omega eta : TotalForms n0 n1) : ℝ :=
  innerZero omega.1 eta.1 + innerOne omega.2 eta.2

/-- The transpose construction makes `delta` the adjoint of `d`. -/
theorem exterior_codifferential_adjoint
    (B : Matrix (Fin n1) (Fin n0) ℝ)
    (omega eta : TotalForms n0 n1) :
    formPairing (exteriorDerivative B omega) eta =
      formPairing omega (codifferential B eta) := by
  rcases omega with ⟨f, g⟩
  rcases eta with ⟨h, k⟩
  change
    innerZero (0 : ZeroForms n0) h + innerOne (B.mulVec f) k =
      innerZero f (B.transpose.mulVec k) +
        innerOne g (0 : OneForms n1)
  have hzero0 : innerZero (0 : ZeroForms n0) h = 0 := by
    simp [innerZero]
  have hzero1 : innerOne g (0 : OneForms n1) = 0 := by
    simp [innerOne]
  rw [hzero0, hzero1, zero_add, add_zero]
  unfold innerZero innerOne
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  calc
    (∑ e : Fin n1, (∑ v : Fin n0, B e v * f v) * k e) =
        ∑ e : Fin n1, ∑ v : Fin n0, (B e v * f v) * k e := by
          apply Finset.sum_congr rfl
          intro e he
          rw [Finset.sum_mul]
    _ = ∑ v : Fin n0, ∑ e : Fin n1, (B e v * f v) * k e := by
          rw [Finset.sum_comm]
    _ = ∑ v : Fin n0, f v * (∑ e : Fin n1, B e v * k e) := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e he
          ring

/-- Operator-Zorn/Dirac block with `delta` in the upper channel and `d` in the
lower channel. -/
def diracZornBlock
    (B : Matrix (Fin n1) (Fin n0) ℝ) :
    Envelope (FormEnd n0 n1) :=
  !![0, codifferential B; exteriorDerivative B, 0]

/-- Exact square of the form-complex Zorn block. -/
theorem diracZornBlock_sq
    (B : Matrix (Fin n1) (Fin n0) ℝ) :
    diracZornBlock B * diracZornBlock B =
      !![codifferential B * exteriorDerivative B, 0;
         0, exteriorDerivative B * codifferential B] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [diracZornBlock, Matrix.mul_apply, Fin.sum_univ_two]

/-- Action of an envelope block on its two form sheets. -/
def blockAction
    (Z : Envelope (FormEnd n0 n1))
    (psi : Fin 2 → TotalForms n0 n1) :
    Fin 2 → TotalForms n0 n1 :=
  fun i => ∑ j : Fin 2, Z i j (psi j)

/-- Diagonal embedding of one total form in the two sheets. -/
def diagonalForm (omega : TotalForms n0 n1) :
    Fin 2 → TotalForms n0 n1 :=
  fun _ => omega

/-- Codiagonal summation of the two sheets. -/
def sumSheets (psi : Fin 2 → TotalForms n0 n1) :
    TotalForms n0 n1 :=
  psi 0 + psi 1

/-- The block action separates the codifferential and differential channels. -/
theorem diracZornBlock_action_diagonal
    (B : Matrix (Fin n1) (Fin n0) ℝ)
    (omega : TotalForms n0 n1) :
    blockAction (diracZornBlock B) (diagonalForm omega) =
      ![codifferential B omega, exteriorDerivative B omega] := by
  funext i
  fin_cases i <;>
    simp [blockAction, diracZornBlock, diagonalForm,
      Fin.sum_univ_two]

/-- Genuine intertwiner recovering `D=d+delta` from the two-sheet block. -/
theorem sumSheets_diracZornBlock_intertwines
    (B : Matrix (Fin n1) (Fin n0) ℝ)
    (omega : TotalForms n0 n1) :
    sumSheets (blockAction (diracZornBlock B) (diagonalForm omega)) =
      diracHodge B omega := by
  rw [diracZornBlock_action_diagonal]
  change codifferential B omega + exteriorDerivative B omega =
    exteriorDerivative B omega + codifferential B omega
  exact add_comm _ _

end InfoGeometry.OperatorAlgebra.FiniteTwoTermDiracHodgeZorn

