import InfoGeometry.Canonical.FiniteSuperchargeIndex

/-!
# Zero-mode pairing from an intertwining equivalence

This extends the existing finite supercharge owner.  The kernel equivalence
is constructed by restricting a linear equivalence which intertwines the
two odd blocks; equality of kernel dimensions is a consequence.

The owner `wittenIndex` is a difference of kernel dimensions.  Identifying
it with an analytic Fredholm index or a heat supertrace requires additional
operator and spectral hypotheses and is not asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteSuperchargeIndex

variable {m n : ℕ} (Q : FiniteSupercharge m n)
    (e : Plus m ≃ₗ[ℝ] Minus n)

/-- Intertwining maps a plus zero mode to a minus zero mode, in both directions. -/
theorem mem_kernel_iff_of_intertwining
    (h : Q.qMinus.comp e.toLinearMap = e.symm.toLinearMap.comp Q.qPlus)
    (x : Plus m) :
    e x ∈ LinearMap.ker Q.qMinus ↔ x ∈ LinearMap.ker Q.qPlus := by
  have hx : Q.qMinus (e x) = e.symm (Q.qPlus x) :=
    DFunLike.congr_fun h x
  simp only [LinearMap.mem_ker, hx]
  exact e.symm.map_eq_zero_iff

/-- The actual kernel submodules correspond under the sheet equivalence. -/
theorem map_kernel_eq_of_intertwining
    (h : Q.qMinus.comp e.toLinearMap = e.symm.toLinearMap.comp Q.qPlus) :
    (LinearMap.ker Q.qPlus).map e.toLinearMap = LinearMap.ker Q.qMinus := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_kernel_iff_of_intertwining Q e h x).mpr hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply (mem_kernel_iff_of_intertwining Q e h (e.symm y)).mp
    simpa using hy

/-- Native Mathlib restriction of the intertwiner to the two zero-mode spaces. -/
def kernelEquivOfIntertwining
    (h : Q.qMinus.comp e.toLinearMap = e.symm.toLinearMap.comp Q.qPlus) :
    LinearMap.ker Q.qPlus ≃ₗ[ℝ] LinearMap.ker Q.qMinus :=
  e.ofSubmodules _ _ (map_kernel_eq_of_intertwining Q e h)

/-- The finite kernel index vanishes because the zero-mode spaces are isomorphic. -/
theorem wittenIndex_eq_zero_of_intertwining
    (h : Q.qMinus.comp e.toLinearMap = e.symm.toLinearMap.comp Q.qPlus) :
    wittenIndex Q = 0 := by
  have hd := (kernelEquivOfIntertwining Q e h).finrank_eq
  simp [wittenIndex, hd]

/-- A paired vacuum may contain arbitrarily many zero modes. -/
theorem paired_zeroSupercharge_index (k : ℕ) :
    wittenIndex (zeroSupercharge k k) = 0 := by
  exact wittenIndex_eq_zero_of_intertwining (zeroSupercharge k k)
    (LinearEquiv.refl ℝ (Plus k)) (by simp [zeroSupercharge])

/-- An unpaired finite zero mode gives a well-defined nonzero index. -/
theorem unpaired_zeroSupercharge_index (k : ℕ) :
    wittenIndex (zeroSupercharge (k + 1) k) = 1 := by
  rw [zeroSupercharge_wittenIndex]
  push_cast
  ring

end InfoGeometry.Canonical.FiniteSuperchargeIndex
