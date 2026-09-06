import Mathlib

open Matrix

/-!
# Krein Carrier, Harmonic Horizon, and Moore-Penrose/Drazin Core

Finite algebraic model:

`carrier = exact ⊕ coexact ⊕ harmonic`.

The harmonic mode is the null/conformal boundary.  The degenerate operator
inverts only the exact/coexact core; its Moore-Penrose/Drazin inverse is the
same core projector in this normalized model.
-/

noncomputable section

abbrev Carrier := Fin 3
abbrev EndCarrier := Matrix Carrier Carrier ℝ

def PExact : EndCarrier := !![1, 0, 0; 0, 0, 0; 0, 0, 0]
def PCoexact : EndCarrier := !![0, 0, 0; 0, 1, 0; 0, 0, 0]
def PHarmonic : EndCarrier := !![0, 0, 0; 0, 0, 0; 0, 0, 1]
def PCore : EndCarrier := PExact + PCoexact

def Ldeg : EndCarrier := !![1, 0, 0; 0, 1, 0; 0, 0, 0]
def Lmp : EndCarrier := !![1, 0, 0; 0, 1, 0; 0, 0, 0]
def LDrazin : EndCarrier := !![1, 0, 0; 0, 1, 0; 0, 0, 0]

theorem projector_decomposition :
    PExact + PCoexact + PHarmonic = (1 : EndCarrier) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [PExact, PCoexact, PHarmonic]

theorem PExact_idem : PExact * PExact = PExact := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [PExact]

theorem PCoexact_idem : PCoexact * PCoexact = PCoexact := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [PCoexact]

theorem PHarmonic_idem : PHarmonic * PHarmonic = PHarmonic := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [PHarmonic]

theorem PCore_idem : PCore * PCore = PCore := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [PCore, PExact, PCoexact]

theorem exact_coexact_orthogonal : PExact * PCoexact = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [PExact, PCoexact]

theorem exact_harmonic_orthogonal : PExact * PHarmonic = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [PExact, PHarmonic]

theorem coexact_harmonic_orthogonal : PCoexact * PHarmonic = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [PCoexact, PHarmonic]

theorem L_kills_harmonic : Ldeg * PHarmonic = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ldeg, PHarmonic]

theorem L_identity_on_core : Ldeg * PCore = PCore := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ldeg, PCore, PExact, PCoexact]

theorem mp_outer_inverse : Ldeg * Lmp * Ldeg = Ldeg := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ldeg, Lmp]

theorem mp_inner_inverse : Lmp * Ldeg * Lmp = Lmp := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ldeg, Lmp]

theorem mp_left_core : Ldeg * Lmp = PCore := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ldeg, Lmp, PCore, PExact, PCoexact]

theorem mp_right_core : Lmp * Ldeg = PCore := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ldeg, Lmp, PCore, PExact, PCoexact]

theorem drazin_commutes : Ldeg * LDrazin = LDrazin * Ldeg := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ldeg, LDrazin]

theorem drazin_core_inverse : LDrazin * Ldeg * LDrazin = LDrazin := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ldeg, LDrazin]

theorem drazin_extracts_core : Ldeg * LDrazin = PCore := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ldeg, LDrazin, PCore, PExact, PCoexact]

def corePart (v : Carrier → ℝ) : Carrier → ℝ :=
  fun i => ∑ j, PCore i j * v j

def harmonicPart (v : Carrier → ℝ) : Carrier → ℝ :=
  fun i => ∑ j, PHarmonic i j * v j

theorem core_plus_harmonic (v : Carrier → ℝ) :
    (fun i => corePart v i + harmonicPart v i) = v := by
  funext i
  fin_cases i <;> simp [corePart, harmonicPart, PCore, PExact, PCoexact, PHarmonic, Fin.sum_univ_three]

def dikinCoreQuadratic (v : Carrier → ℝ) : ℝ :=
  (v 0) ^ 2 + (v 1) ^ 2

theorem dikin_ignores_harmonic (v : Carrier → ℝ) (h : v 0 = 0) (h' : v 1 = 0) :
    dikinCoreQuadratic v = 0 := by
  simp [dikinCoreQuadratic, h, h']

/-- Krein Moore-Penrose theorem: Hodge projectors split the carrier, the
    harmonic horizon is killed by the degenerate operator, and the
    Moore-Penrose/Drazin inverse extracts the non-null core. -/
theorem krein_moore_penrose_theorem :
    PExact + PCoexact + PHarmonic = 1 ∧
    PExact * PExact = PExact ∧
    PCoexact * PCoexact = PCoexact ∧
    PHarmonic * PHarmonic = PHarmonic ∧
    Ldeg * PHarmonic = 0 ∧
    Ldeg * PCore = PCore ∧
    Ldeg * Lmp * Ldeg = Ldeg ∧
    Lmp * Ldeg * Lmp = Lmp ∧
    Ldeg * Lmp = PCore ∧
    Lmp * Ldeg = PCore ∧
    Ldeg * LDrazin = PCore ∧
    (∀ v, (fun i => corePart v i + harmonicPart v i) = v) := by
  exact ⟨projector_decomposition, PExact_idem, PCoexact_idem, PHarmonic_idem,
    L_kills_harmonic, L_identity_on_core, mp_outer_inverse, mp_inner_inverse,
    mp_left_core, mp_right_core, drazin_extracts_core, core_plus_harmonic⟩
