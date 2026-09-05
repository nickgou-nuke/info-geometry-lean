import InfoGeometry.Quantum.PenroseOnsagerYangOrderParameter
import Mathlib

/-!
# Two-mode fragmented versus coherent kernels

The same diagonal occupation data can be represented either by a diagonal
mixture with no cross coherence or by a rank-one coherent mode with nonzero
off-diagonal entries.  This is the finite algebraic distinction underlying the
Fock/coherent comparison in the Penrose--Onsager--Yang discussion.

No energetic preference, dynamical transition, measurement postulate, or
spontaneous symmetry breaking is asserted.
-/

noncomputable section

namespace InfoGeometry.Quantum.PenroseOnsagerYang

open scoped ComplexOrder

abbrev TwoModeKernel := Matrix (Fin 2) (Fin 2) ℂ

/-- Two-component complex mode. -/
def twoModeVector (a b : ℂ) : Mode (Fin 2) :=
  ![a, b]

/-- Rank-one coherent two-mode kernel. -/
def coherentTwoModeKernel (a b : ℂ) : TwoModeKernel :=
  rankOneKernel (twoModeVector a b)

/-- Diagonal two-mode occupation kernel, with no cross coherence. -/
def fragmentedTwoModeKernel (N0 N1 : ℝ) : TwoModeKernel :=
  !![(N0 : ℂ), 0;
     0, (N1 : ℂ)]

/-- Diagonal kernel carrying the same two occupation magnitudes as amplitudes
`a` and `b`. -/
def incoherentKernelOfAmplitudes (a b : ℂ) : TwoModeKernel :=
  fragmentedTwoModeKernel (Complex.normSq a) (Complex.normSq b)

@[simp] theorem coherentTwoModeKernel_zero_zero (a b : ℂ) :
    coherentTwoModeKernel a b 0 0 = (Complex.normSq a : ℂ) := by
  simp [coherentTwoModeKernel, rankOneKernel, twoModeVector,
    Complex.mul_conj]

@[simp] theorem coherentTwoModeKernel_one_one (a b : ℂ) :
    coherentTwoModeKernel a b 1 1 = (Complex.normSq b : ℂ) := by
  simp [coherentTwoModeKernel, rankOneKernel, twoModeVector,
    Complex.mul_conj]

@[simp] theorem coherentTwoModeKernel_zero_one (a b : ℂ) :
    coherentTwoModeKernel a b 0 1 = a * Complex.conj b := by
  simp [coherentTwoModeKernel, rankOneKernel, twoModeVector]

@[simp] theorem coherentTwoModeKernel_one_zero (a b : ℂ) :
    coherentTwoModeKernel a b 1 0 = b * Complex.conj a := by
  simp [coherentTwoModeKernel, rankOneKernel, twoModeVector]

@[simp] theorem fragmentedTwoModeKernel_zero_one (N0 N1 : ℝ) :
    fragmentedTwoModeKernel N0 N1 0 1 = 0 := by
  simp [fragmentedTwoModeKernel]

@[simp] theorem fragmentedTwoModeKernel_one_zero (N0 N1 : ℝ) :
    fragmentedTwoModeKernel N0 N1 1 0 = 0 := by
  simp [fragmentedTwoModeKernel]

/-- A coherent two-mode kernel is positive semidefinite. -/
theorem coherentTwoModeKernel_posSemidef (a b : ℂ) :
    (coherentTwoModeKernel a b).PosSemidef :=
  rankOneKernel_posSemidef (twoModeVector a b)

/-- A coherent two-mode kernel has determinant zero. -/
@[simp] theorem coherentTwoModeKernel_det (a b : ℂ) :
    Matrix.det (coherentTwoModeKernel a b) = 0 := by
  rw [Matrix.det_fin_two]
  simp [coherentTwoModeKernel, rankOneKernel, twoModeVector]
  ring

/-- Trace of the coherent kernel. -/
theorem coherentTwoModeKernel_trace (a b : ℂ) :
    Matrix.trace (coherentTwoModeKernel a b) =
      (Complex.normSq a : ℂ) + (Complex.normSq b : ℂ) := by
  simp [Matrix.trace, coherentTwoModeKernel, rankOneKernel,
    twoModeVector, Complex.mul_conj, Fin.sum_univ_two]

/-- Determinant of the diagonal fragmented kernel. -/
theorem fragmentedTwoModeKernel_det (N0 N1 : ℝ) :
    Matrix.det (fragmentedTwoModeKernel N0 N1) =
      (N0 : ℂ) * (N1 : ℂ) := by
  rw [Matrix.det_fin_two]
  simp [fragmentedTwoModeKernel]

/-- Trace of the diagonal fragmented kernel. -/
theorem fragmentedTwoModeKernel_trace (N0 N1 : ℝ) :
    Matrix.trace (fragmentedTwoModeKernel N0 N1) =
      (N0 : ℂ) + (N1 : ℂ) := by
  simp [Matrix.trace, fragmentedTwoModeKernel, Fin.sum_univ_two]

/-- Coherent and incoherent kernels built from the same amplitudes have the
same diagonal occupations. -/
theorem coherent_incoherent_same_diagonal (a b : ℂ) :
    coherentTwoModeKernel a b 0 0 =
        incoherentKernelOfAmplitudes a b 0 0 ∧
      coherentTwoModeKernel a b 1 1 =
        incoherentKernelOfAmplitudes a b 1 1 := by
  constructor <;>
    simp [incoherentKernelOfAmplitudes, fragmentedTwoModeKernel]

/-- Their off-diagonal entries differ precisely by the coherence amplitude. -/
theorem coherent_incoherent_offDiagonal_readout (a b : ℂ) :
    coherentTwoModeKernel a b 0 1 = a * Complex.conj b ∧
      incoherentKernelOfAmplitudes a b 0 1 = 0 := by
  exact ⟨coherentTwoModeKernel_zero_one a b, by
    simp [incoherentKernelOfAmplitudes]⟩

/-- Nonzero cross coherence separates the coherent rank-one kernel from the
diagonal occupation kernel. -/
theorem coherent_ne_incoherent_of_cross_ne_zero
    {a b : ℂ} (hab : a * Complex.conj b ≠ 0) :
    coherentTwoModeKernel a b ≠ incoherentKernelOfAmplitudes a b := by
  intro h
  apply hab
  have h01 := congrArg (fun M : TwoModeKernel => M 0 1) h
  simpa [incoherentKernelOfAmplitudes] using h01

/-- A common global phase leaves the coherent two-mode kernel unchanged. -/
theorem coherentTwoModeKernel_globalPhase_invariant
    {u : ℂ} (hu : u * Complex.conj u = 1)
    (a b : ℂ) :
    coherentTwoModeKernel (u * a) (u * b) =
      coherentTwoModeKernel a b := by
  change
    rankOneKernel (twoModeVector (u * a) (u * b)) =
      rankOneKernel (twoModeVector a b)
  have hvec :
      twoModeVector (u * a) (u * b) =
        scalarAction u (twoModeVector a b) := by
    funext i
    fin_cases i <;> rfl
  rw [hvec]
  exact rankOneKernel_globalPhase_invariant hu (twoModeVector a b)

/-- Compact two-mode coherence packet. -/
theorem twoMode_coherence_packet
    {a b : ℂ} (hab : a * Complex.conj b ≠ 0) :
    Matrix.det (coherentTwoModeKernel a b) = 0 ∧
      (coherentTwoModeKernel a b).PosSemidef ∧
      coherentTwoModeKernel a b 0 0 =
        incoherentKernelOfAmplitudes a b 0 0 ∧
      coherentTwoModeKernel a b 1 1 =
        incoherentKernelOfAmplitudes a b 1 1 ∧
      coherentTwoModeKernel a b ≠ incoherentKernelOfAmplitudes a b := by
  exact ⟨coherentTwoModeKernel_det a b,
    coherentTwoModeKernel_posSemidef a b,
    (coherent_incoherent_same_diagonal a b).1,
    (coherent_incoherent_same_diagonal a b).2,
    coherent_ne_incoherent_of_cross_ne_zero hab⟩

end InfoGeometry.Quantum.PenroseOnsagerYang
