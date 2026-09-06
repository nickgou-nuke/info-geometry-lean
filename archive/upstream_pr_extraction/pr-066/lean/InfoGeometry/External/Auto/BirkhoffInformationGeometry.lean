import Mathlib.Tactic

namespace BirkhoffInformationGeometry

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

def permId : M2R :=
  !![1, 0; 0, 1]

def permSwap : M2R :=
  !![0, 1; 1, 0]

def rowSum (A : M2R) (i : Fin 2) : ℝ :=
  ∑ j : Fin 2, A i j

def colSum (A : M2R) (j : Fin 2) : ℝ :=
  ∑ i : Fin 2, A i j

def IsDoublyStochastic (A : M2R) : Prop :=
  (∀ i j : Fin 2, 0 ≤ A i j) ∧
    (∀ i : Fin 2, rowSum A i = 1) ∧
    (∀ j : Fin 2, colSum A j = 1)

def convexBlend (t : ℝ) (A B : M2R) : M2R :=
  t • A + (1 - t) • B

theorem permId_rowSum (i : Fin 2) : rowSum permId i = 1 := by
  fin_cases i <;> simp [rowSum, permId]

theorem permId_colSum (j : Fin 2) : colSum permId j = 1 := by
  fin_cases j <;> simp [colSum, permId]

theorem permSwap_rowSum (i : Fin 2) : rowSum permSwap i = 1 := by
  fin_cases i <;> simp [rowSum, permSwap]

theorem permSwap_colSum (j : Fin 2) : colSum permSwap j = 1 := by
  fin_cases j <;> simp [colSum, permSwap]

theorem permId_doublyStochastic : IsDoublyStochastic permId := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [permId]
  · constructor
    · exact permId_rowSum
    · exact permId_colSum

theorem permSwap_doublyStochastic : IsDoublyStochastic permSwap := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [permSwap]
  · constructor
    · exact permSwap_rowSum
    · exact permSwap_colSum

theorem permId_ne_permSwap : permId ≠ permSwap := by
  intro h
  have h00 : permId 0 0 = permSwap 0 0 := by rw [h]
  norm_num [permId, permSwap] at h00

theorem convexBlend_perm_entries (t : ℝ) :
    convexBlend t permId permSwap = !![t, 1 - t; 1 - t, t] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [convexBlend, permId, permSwap, Matrix.add_apply]

theorem convexBlend_perm_rowSum (t : ℝ) (i : Fin 2) :
    rowSum (convexBlend t permId permSwap) i = 1 := by
  fin_cases i <;> simp [rowSum, convexBlend_perm_entries]

theorem convexBlend_perm_colSum (t : ℝ) (j : Fin 2) :
    colSum (convexBlend t permId permSwap) j = 1 := by
  fin_cases j <;> simp [colSum, convexBlend_perm_entries]

theorem convexBlend_perm_doublyStochastic {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    IsDoublyStochastic (convexBlend t permId permSwap) := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [convexBlend_perm_entries] <;> linarith
  · constructor
    · exact convexBlend_perm_rowSum t
    · exact convexBlend_perm_colSum t

theorem doublyStochastic_eq_convexBlend
    (A : M2R) (hA : IsDoublyStochastic A) :
    A = convexBlend (A 0 0) permId permSwap := by
  rcases hA with ⟨_, hrow, hcol⟩
  have hrow0 : A 0 0 + A 0 1 = 1 := by
    simpa [rowSum] using hrow 0
  have hcol0 : A 0 0 + A 1 0 = 1 := by
    simpa [colSum] using hcol 0
  have hrow1 : A 1 0 + A 1 1 = 1 := by
    simpa [rowSum] using hrow 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [convexBlend, permId, permSwap, Matrix.add_apply] <;>
    linarith

theorem doublyStochastic_has_permConvexCoeff
    (A : M2R) (hA : IsDoublyStochastic A) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ A = convexBlend t permId permSwap := by
  refine ⟨A 0 0, hA.1 0 0, ?_, doublyStochastic_eq_convexBlend A hA⟩
  have hrow0 : A 0 0 + A 0 1 = 1 := by
    simpa [rowSum] using hA.2.1 0
  have h01 : 0 ≤ A 0 1 := hA.1 0 1
  linarith

end BirkhoffInformationGeometry
