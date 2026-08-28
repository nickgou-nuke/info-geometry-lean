import Mathlib

namespace InfoGeometry.Algebra.Clifford55

abbrev Dim32 := Fin 32
abbrev Cl55Mat := Matrix Dim32 Dim32 ℝ

def Pvac : Cl55Mat := Matrix.single 0 0 1

theorem Pvac_mul_self : Pvac * Pvac = Pvac := by
  simpa [Pvac] using
    (Matrix.single_mul_single_same (R := ℝ)
      (0 : Dim32) (0 : Dim32) (0 : Dim32) (1 : ℝ))

def LeftIdeal : Submodule ℝ Cl55Mat where
  carrier := {M | M * Pvac = M}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    simpa [add_mul] using congrArg₂ (· + ·) hA hB
  smul_mem' := by
    intro c A hA
    simpa [Matrix.smul_mul] using congrArg (fun X => c • X) hA

def RightIdeal : Submodule ℝ Cl55Mat where
  carrier := {M | Pvac * M = M}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    simpa [mul_add] using congrArg₂ (· + ·) hA hB
  smul_mem' := by
    intro c A hA
    simpa [Matrix.mul_smul] using congrArg (fun X => c • X) hA

def ket (i : Dim32) : Cl55Mat := Matrix.single i 0 1
def bra (j : Dim32) : Cl55Mat := Matrix.single 0 j 1

theorem dyadic_commutator (g x y : Cl55Mat) :
    g * (x * y) - (x * y) * g =
      (g * x) * y - x * (y * g) := by
  rw [mul_assoc, mul_assoc]

theorem ket_mem_left (i : Dim32) : ket i ∈ LeftIdeal := by
  change ket i * Pvac = ket i
  simpa [ket, Pvac] using
    (Matrix.single_mul_single_same (R := ℝ) i (0 : Dim32) (0 : Dim32) (1 : ℝ))

theorem bra_mem_right (j : Dim32) : bra j ∈ RightIdeal := by
  change Pvac * bra j = bra j
  simpa [bra, Pvac] using
    (Matrix.single_mul_single_same (R := ℝ) (0 : Dim32) (0 : Dim32) j (1 : ℝ))

theorem dyad_eq_single (i j : Dim32) :
    ket i * bra j = Matrix.single i j 1 := by
  simpa [ket, bra] using
    (Matrix.single_mul_single_same (R := ℝ) i (0 : Dim32) j (1 : ℝ))

theorem dyad_corner_readback (i j : Dim32) :
    Pvac * (bra j * ket i) * Pvac = bra j * ket i := by
  calc
    Pvac * (bra j * ket i) * Pvac =
        (Pvac * bra j) * (ket i * Pvac) := by
      simp only [mul_assoc]
    _ = bra j * ket i := by
      rw [show Pvac * bra j = bra j from by
        change Pvac * bra j = bra j
        exact congrArg (fun X => X) (by
          simpa [bra, Pvac] using
            (Matrix.single_mul_single_same (R := ℝ)
              (0 : Dim32) (0 : Dim32) j (1 : ℝ)))]
      rw [show ket i * Pvac = ket i from ket_mem_left i]

theorem dyadic_span_eq_top :
    Submodule.span ℝ (Set.range (fun p : Dim32 × Dim32 => ket p.1 * bra p.2)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro M
  have hdecomp : M = ∑ i : Dim32, ∑ j : Dim32,
      (M i j) • Matrix.single i j 1 := by
    simpa [smul_eq_mul] using (Matrix.matrix_eq_sum_single M)
  rw [hdecomp]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  rw [← dyad_eq_single i j]
  have hmem : ket i * bra j ∈
      Submodule.span ℝ (Set.range (fun p : Dim32 × Dim32 => ket p.1 * bra p.2)) :=
    Submodule.subset_span (Set.mem_range_self (i, j))
  exact Submodule.smul_mem _ (M i j) hmem

theorem trace_dyadic_commutator_zero (A B : Cl55Mat) :
    Matrix.trace (A * B - B * A) = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm B A, sub_self]

theorem trace_dyad (i j : Dim32) :
    Matrix.trace (ket i * bra j) = if i = j then 1 else 0 := by
  rw [dyad_eq_single]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg h]
    exact Matrix.trace_single_eq_of_ne i j (1 : ℝ) h

end InfoGeometry.Algebra.Clifford55
