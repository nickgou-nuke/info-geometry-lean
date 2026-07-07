/-! ## 5. Native representation via VirasoroProject -/

/-- Maps the basis index (some m for L_m, none for C) to the truncated operators -/
def stageGenOper (n : ℕ) (J ψ : ℤ → Module.End 𝕂 V) : Option ℤ → Module.End 𝕂 V
  | some m => virasoroL n m J ψ
  | none => virasoroC

/-- The commutation condition over all index combinations -/
def StageGenCommCondition (n : ℕ) (J ψ : ℤ → Module.End 𝕂 V) : Prop :=
  ∀ i j : Option ℤ, (stageGenOper n J ψ i).commutator (stageGenOper n J ψ j) =
    LieAlgebra.representationOfBasisAux (VirasoroAlgebra.basisLC 𝕂) (stageGenOper n J ψ)
      ⁅VirasoroAlgebra.basisLC 𝕂 i, VirasoroAlgebra.basisLC 𝕂 j⁆

/-- The native Virasoro representation for the finite truncation stage, provided boundary defects vanish. -/
noncomputable def stageRepresentation (n : ℕ) (J ψ : ℤ → Module.End 𝕂 V)
    (h_comm : StageGenCommCondition n J ψ) :
    LieAlgebra.Representation 𝕂 𝕂 (VirasoroAlgebra 𝕂) V :=
  LieAlgebra.representationOfBasis (VirasoroAlgebra.basisLC 𝕂) h_comm