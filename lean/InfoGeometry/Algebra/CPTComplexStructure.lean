import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.Cl11Fermions

/-!
# CPT Complex Structure — The Cl(1,1) Atom as Geometric Compass

The Cl(1,1) Clifford algebra provides the internal complex structure for
the chiral split of the vacuum into 16₊ ⊕ 16₋ sheets.

## Architecture

```
  r0 (timelike, r0²=1)     r5 (spacelike, r5²=-1)
       │                          │
       ├──────────┬───────────────┤
       ▼          ▼               ▼
    P₊ = (1+r0)/2   P₋ = (1-r0)/2   J = r5 (complex structure)
    (Forward sheet)  (Backward sheet) (phase rotation)
       │          │               │
       └──────────┴───────────────┘
                  │
                  ▼
         B = r0·r5 (Euler operator)
         B² = 1 (hyperbolic generator)
```

The Euler operator B is the generator of Bogoliubov thermal boosts,
mixing the physical (16₊) and mirror (16₋) sheets via:
  U(θ) = cosh(θ)·I + sinh(θ)·B

This is the geometric engine behind the ThermalBogoliubov module and
the q-CCR thermal dial (q = exp(-β) = tanh²(θ/2)).

Witnessed by: `formalizations/cpt_compass_evidence.py` (SymPy+Clifford),
`formalizations/cpt_compass_gap.g` (GAP), `Cl11Fermions.lean`.
-/

open Cl11Fermions

noncomputable section

namespace InfoGeometry.Algebra.CPT

/-! ## 1. The CPT Atom structure -/

/--
A representation of the Cl(1,1) Clifford algebra.
r0: timelike generator (r0² = 1)
r5: spacelike generator (r5² = -1)
anticommute: r0·r5 = -r5·r0
-/
structure Cl11Atom (K : Type*) [Ring K] where
  r0 : K
  r5 : K

def Cl11AtomLaws {K : Type*} [Ring K] (A : Cl11Atom K) : Prop :=
  A.r0 * A.r0 = 1 ∧
  A.r5 * A.r5 = -1 ∧
  A.r0 * A.r5 = -(A.r5 * A.r0)

/-- Native Mathlib instantiation of the Cl(1,1) atom using 2x2 real matrices. -/
def cl11MatrixAtom : Cl11Atom (Matrix (Fin 2) (Fin 2) ℝ) where
  r0 := !![0, 1; 1, 0]
  r5 := !![0, -1; 1, 0]

theorem cl11MatrixAtom_laws :
    Cl11AtomLaws cl11MatrixAtom := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [cl11MatrixAtom, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [cl11MatrixAtom, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [cl11MatrixAtom, Matrix.mul_apply, Fin.sum_univ_two]

variable {K : Type*} [Ring K] [Algebra ℝ K] (atom : Cl11Atom K)

/-- The internal complex structure J = r5. -/
abbrev ComplexStructure : K := atom.r5

/-- J² = -1: the complex structure ax!om. -/
theorem complex_structure_sq_neg_one (hatom : Cl11AtomLaws atom) :
    ComplexStructure atom * ComplexStructure atom = -1 :=
  hatom.2.1

/-- The Euler operator B = r0·J = r0·r5. -/
def EulerOperator : K := atom.r0 * ComplexStructure atom

/-- B² = +1: the Euler operator is an involution. -/
theorem euler_operator_sq_one (hatom : Cl11AtomLaws atom) :
    EulerOperator atom * EulerOperator atom = 1 := by
  dsimp [EulerOperator, ComplexStructure]
  have h_anti' : atom.r5 * atom.r0 = -(atom.r0 * atom.r5) := by
    rw [hatom.2.2, neg_neg]
  calc
    (atom.r0 * atom.r5) * (atom.r0 * atom.r5)
        = atom.r0 * (atom.r5 * atom.r0) * atom.r5 := by noncomm_ring
    _ = atom.r0 * (-(atom.r0 * atom.r5)) * atom.r5 := by rw [h_anti']
    _ = -(atom.r0 * atom.r0) * (atom.r5 * atom.r5) := by noncomm_ring
    _ = -(1 : K) * (-1 : K) := by rw [hatom.1, hatom.2.1]
    _ = 1 := by noncomm_ring

/-! ## 2. Chiral projection operators -/

/-- The positive chiral projector P₊ = (1 + r0)/2 (16₊ sheet). -/
def chiralProjectorPlus : K := (1/2 : ℝ) • (1 + atom.r0)

/-- The negative chiral projector P₋ = (1 - r0)/2 (16₋ sheet). -/
def chiralProjectorMinus : K := (1/2 : ℝ) • (1 - atom.r0)

/--
**Chiral orthogonality theorem.**
The two chiral sheets are orthogonal: P₊·P₋ = 0.
Together they form a partition of unity: P₊ + P₋ = 1.
-/
theorem chiral_sheets_orthogonal (hatom : Cl11AtomLaws atom) :
    chiralProjectorPlus atom * chiralProjectorMinus atom = 0 := by
  dsimp [chiralProjectorPlus, chiralProjectorMinus]
  calc
    ((1/2 : ℝ) • (1 + atom.r0)) * ((1/2 : ℝ) • (1 - atom.r0))
        = ((1/2 : ℝ) * (1/2 : ℝ)) • ((1 + atom.r0) * (1 - atom.r0)) := by
          rw [smul_mul_smul]
    _ = (1/4 : ℝ) • ((1 + atom.r0) * (1 - atom.r0)) := by norm_num
    _ = (1/4 : ℝ) • (0 : K) := by
      have h : (1 + atom.r0) * (1 - atom.r0) = 0 := by
        calc
          (1 + atom.r0) * (1 - atom.r0) = 1 - atom.r0 * atom.r0 := by noncomm_ring
          _ = 0 := by rw [hatom.1]; noncomm_ring
      rw [h]
    _ = 0 := smul_zero _

/-- The chiral projectors partition unity: P₊ + P₋ = 1. -/
theorem chiral_sheets_partition_unity :
    chiralProjectorPlus atom + chiralProjectorMinus atom = 1 := by
  dsimp [chiralProjectorPlus, chiralProjectorMinus]
  rw [← smul_add]
  have hsum : (1 + atom.r0) + (1 - atom.r0) = (2 : ℝ) • (1 : K) := by
    simp [two_smul]
  rw [hsum]
  rw [smul_smul]
  norm_num

/-! ## 3. Compass reversal under Euler operator -/

/-- The Euler operator reverses chiral sheets: `P₊ B = B P₋`. -/
theorem euler_operator_reverses_chiral_sheets (hatom : Cl11AtomLaws atom) :
    chiralProjectorPlus atom * EulerOperator atom =
      EulerOperator atom * chiralProjectorMinus atom := by
  dsimp [chiralProjectorPlus, chiralProjectorMinus, EulerOperator, ComplexStructure]
  rw [smul_mul_assoc, mul_smul_comm]
  congr 1
  calc
    (1 + atom.r0) * (atom.r0 * atom.r5) = atom.r0 * atom.r5 + atom.r5 := by
      rw [add_mul, one_mul, ← mul_assoc, hatom.1, one_mul]
    _ = atom.r0 * atom.r5 - atom.r0 * atom.r5 * atom.r0 := by
      have h : atom.r0 * atom.r5 * atom.r0 = - atom.r5 := by
        rw [hatom.2.2, neg_mul, mul_assoc, hatom.1, mul_one]
      rw [h]
      abel
    _ = atom.r0 * atom.r5 * (1 - atom.r0) := by
      rw [mul_sub, mul_one]

end InfoGeometry.Algebra.CPT
