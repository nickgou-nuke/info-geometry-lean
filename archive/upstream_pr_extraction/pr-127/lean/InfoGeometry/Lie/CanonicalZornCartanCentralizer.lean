import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

noncomputable section

/-!
# Native centralizer of the canonical Cartan subalgebra

The centralizer is defined directly as the set of derivations commuting with
every element of the existing native Cartan Lie subalgebra.  Its equality with
that subalgebra is obtained from the computed zero joint eigenspace.
-/

namespace InfoGeometry.Lie.CanonicalZornCartanCentralizer

open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.CanonicalZornCartanAdjointSpectrum
open InfoGeometry.Lie.CanonicalZornCartanAdjointAction
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
open InfoGeometry.Lie.CanonicalZornDerivationDimension

abbrev Der := InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations

theorem jointEigenspace_zero_eq_nativeCartan :
    jointEigenspace 0 = (axialCartanLieSubalgebra : Submodule ℝ Der) := by
  rw [jointEigenspace_zero_eq_cartanRootSpan, ← nativeCartan_eq_cartanRootSpan]

def axialCartanCentralizer : Set Der :=
  {D | ∀ H : axialCartanLieSubalgebra, ⁅(H : Der), D⁆ = 0}

theorem axialCartanCentralizer_eq_nativeCartan :
    axialCartanCentralizer = (axialCartanLieSubalgebra : Set Der) := by
  ext D
  constructor
  · intro hD
    have hzero : D ∈ jointEigenspace 0 := by
      rw [mem_jointEigenspace_iff]
      intro k
      change ⁅(axialCartanLieEquiv k : Der), D⁆ =
        (SMul.smul ((0 : Weight) k) D : Der)
      simp
      calc
        ⁅(axialCartanLieEquiv k : Der), D⁆ = 0 := hD (axialCartanLieEquiv k)
        _ = SMul.smul 0 D := (zero_smul ℝ D).symm
    rw [jointEigenspace_zero_eq_nativeCartan] at hzero
    exact hzero
  · intro hD H
    have hD' : D ∈ axialCartanLieSubalgebra := hD
    have h := axialCartanLieSubalgebra_bracket_zero H ⟨D, hD'⟩
    exact congrArg Subtype.val h

theorem axialCartanCentralizer_eq_cartanRootSpan :
    axialCartanCentralizer = (cartanRootSpan : Set Der) := by
  rw [axialCartanCentralizer_eq_nativeCartan]
  exact congrArg (fun S : Submodule ℝ Der => (S : Set Der))
    nativeCartan_eq_cartanRootSpan

instance axialCartanLieSubalgebra_isNilpotent :
    LieRing.IsNilpotent axialCartanLieSubalgebra := by
  rw [LieRing.IsNilpotent, LieModule.isNilpotent_iff ℝ]
  refine ⟨1, ?_⟩
  rw [LieModule.lowerCentralSeries_succ, LieModule.lowerCentralSeries_zero]
  rw [← LieSubmodule.toSubmodule_eq_bot]
  rw [LieSubmodule.lieIdeal_oper_eq_linear_span]
  rw [eq_bot_iff]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨a, b, rfl⟩
      exact (Submodule.mem_bot ℝ).2 (axialCartanLieSubalgebra_bracket_zero a b)
  | zero => exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih => exact Submodule.smul_mem _ c ih

theorem axialCartan_rootSpaceSum_invariant
    (H : axialCartanLieSubalgebra) {D : Der} (hD : D ∈ rootSpaceSum) :
    ⁅(H : Der), D⁆ ∈ rootSpaceSum := by
  let k : TracelessWeight := axialCartanLieEquiv.symm H
  refine Submodule.iSup_induction
    (motive := fun X => ⁅(H : Der), X⁆ ∈ rootSpaceSum)
    (fun j : nonzeroIndex => rootSpace j.1) hD ?_ ?_ ?_
  · intro j x hx
    change x ∈ rootSpace j.1 at hx
    have hxj := hx
    rw [rootSpace_eq_jointEigenspace j] at hxj
    have hx' := (mem_jointEigenspace_iff (rootWeight j.1) x).mp hxj k
    have hbr : ⁅(H : Der), x⁆ =
        (rootWeight j.1 k) • x := by
      simpa [CanonicalZornCartanAdjointAction.adCartan_apply, k] using hx'
    rw [hbr]
    exact rootSpaceSum.smul_mem _
      (le_iSup (fun j : nonzeroIndex => rootSpace j.1) j hx)
  · change ⁅(H : Der), (0 : Der)⁆ ∈ rootSpaceSum
    rw [lie_zero]
    exact Submodule.zero_mem _
  · intro x y hx hy
    rw [lie_add]
    exact rootSpaceSum.add_mem hx hy

instance axialCartan_isCartan :
    LieSubalgebra.IsCartanSubalgebra
      (axialCartanLieSubalgebra : LieSubalgebra ℝ Der) where
  nilpotent := axialCartanLieSubalgebra_isNilpotent
  self_normalizing := by
    ext D
    constructor
    · intro hD
      have h1 : D ∈ axialCartanCentralizer := by
        intro H
        obtain ⟨A, hA, B, hB, hAB⟩ :=
          Submodule.mem_sup.mp
            (show D ∈ cartanRootSpan ⊔ rootSpaceSum from
              (cartanRootSpan_sup_rootSpaceSum_eq_top ▸ Submodule.mem_top))
        have hcartan : ⁅(H : Der), D⁆ ∈ cartanRootSpan := by
          rw [← nativeCartan_eq_cartanRootSpan]
          exact (axialCartanLieSubalgebra.mem_normalizer_iff' D).mp hD H H.property
        have hroot : ⁅(H : Der), D⁆ ∈ rootSpaceSum := by
          rw [← hAB, lie_add]
          have hA' : A ∈ axialCartanLieSubalgebra := by
            rw [← nativeCartan_eq_cartanRootSpan] at hA
            exact hA
          have hzero : ⁅(H : Der), A⁆ = 0 := by
            exact congrArg Subtype.val
              (axialCartanLieSubalgebra_bracket_zero H ⟨A, hA'⟩)
          rw [hzero, zero_add]
          exact axialCartan_rootSpaceSum_invariant H hB
        have hboth : ⁅(H : Der), D⁆ ∈ cartanRootSpan ⊓ rootSpaceSum :=
          ⟨hcartan, hroot⟩
        rw [cartanRootSpan_inf_rootSpaceSum_eq_bot] at hboth
        exact (Submodule.mem_bot ℝ).mp hboth
      rwa [axialCartanCentralizer_eq_nativeCartan] at h1
    · intro hD
      exact LieSubalgebra.le_normalizer _ hD

end InfoGeometry.Lie.CanonicalZornCartanCentralizer
