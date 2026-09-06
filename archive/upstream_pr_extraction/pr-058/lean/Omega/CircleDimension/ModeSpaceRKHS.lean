namespace Omega.CircleDimension

/-- Logical composition of explicitly supplied mode-space and RKHS obligations.

    This theorem does not introduce an RKHS model: the six propositions are
    the concrete obligations that an owner module must instantiate. -/
theorem paper_circle_dimension_mode_space_rkhs
    (modeGramKernel modeSpanDense modeSpaceEqualsL2Zero rkhsKernelSectionsDense
      modeAssignmentIsometry modeAssignmentUnitaryExtension : Prop)
    (hKernel : modeGramKernel)
    (hDense : modeSpanDense)
    (hClosure : modeSpanDense → modeSpaceEqualsL2Zero)
    (hIsometry : modeGramKernel → modeAssignmentIsometry)
    (hUnitary : modeSpaceEqualsL2Zero → rkhsKernelSectionsDense → modeAssignmentIsometry →
      modeAssignmentUnitaryExtension)
    (hKernelSectionsDense : rkhsKernelSectionsDense) :
    modeSpanDense ∧ modeSpaceEqualsL2Zero ∧ modeAssignmentIsometry ∧
      modeAssignmentUnitaryExtension := by
  have hClosureEq : modeSpaceEqualsL2Zero := hClosure hDense
  have hIso : modeAssignmentIsometry := hIsometry hKernel
  exact ⟨hDense, hClosureEq, hIso, hUnitary hClosureEq hKernelSectionsDense hIso⟩

/-- The closure and unitary-extension consequences of the same explicit obligations. -/
theorem paper_circle_dimension_mode_space_rkhs_density
    (modeGramKernel modeSpanDense modeSpaceEqualsL2Zero rkhsKernelSectionsDense
      modeAssignmentIsometry modeAssignmentUnitaryExtension : Prop)
    (hKernel : modeGramKernel)
    (hDense : modeSpanDense)
    (hClosure : modeSpanDense → modeSpaceEqualsL2Zero)
    (hIsometry : modeGramKernel → modeAssignmentIsometry)
    (hUnitary : modeSpaceEqualsL2Zero → rkhsKernelSectionsDense → modeAssignmentIsometry →
      modeAssignmentUnitaryExtension)
    (hKernelSectionsDense : rkhsKernelSectionsDense) :
    modeSpaceEqualsL2Zero ∧ modeAssignmentUnitaryExtension := by
  have hClosureEq : modeSpaceEqualsL2Zero := hClosure hDense
  have hIso : modeAssignmentIsometry := hIsometry hKernel
  exact ⟨hClosureEq, hUnitary hClosureEq hKernelSectionsDense hIso⟩

end Omega.CircleDimension
