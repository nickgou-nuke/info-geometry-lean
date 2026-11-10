import Mathlib.Logic.Encodable.Basic
import Omega.SPG.BoundaryGodelizationHolographicDictionary

namespace Omega.SPG

/-- A monomial label is a finite list of natural-number exponents. -/
abbrev MultiIndex := List ℕ

/-- A finite support of monomial labels.  This is the concrete carrier formalized here. -/
abbrev FiniteMomentSupport := Finset MultiIndex

/-- Squarefree Gödel support code for a finite set of monomial labels. -/
abbrev BoundaryGodelCode := Finset ℕ

/-- Encode each multi-index by its natural-number Gödel code. -/
def boundaryGodelCode (U : FiniteMomentSupport) : BoundaryGodelCode :=
  U.image Encodable.encode

/-- A finite-support monomial moment is the indicator of support membership. -/
def monomialMoment (α : MultiIndex) (U : FiniteMomentSupport) : ℚ :=
  if α ∈ U then 1 else 0

/-- Read the same indicator from the encoded support. -/
def boundaryMomentFromGodel (α : MultiIndex) (code : BoundaryGodelCode) : ℚ :=
  if Encodable.encode α ∈ code then 1 else 0

/-- Encoding preserves and reflects membership of each multi-index. -/
theorem boundaryGodelCode_mem (α : MultiIndex) (U : FiniteMomentSupport) :
    Encodable.encode α ∈ boundaryGodelCode U ↔ α ∈ U := by
  change Encodable.encode α ∈ U.image Encodable.encode ↔ α ∈ U
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨β, hβ, hcode⟩
    have hβα : β = α := Encodable.encode_injective hcode
    simpa [hβα] using hβ
  · intro hα
    exact Finset.mem_image.mpr ⟨α, hα, rfl⟩

/-- The complete finite-support moment profile agrees with the profile read from its code. -/
theorem finiteSupport_moment_profile_readout (U : FiniteMomentSupport) :
    (fun α => monomialMoment α U) =
      fun α => boundaryMomentFromGodel α (boundaryGodelCode U) := by
  funext α
  simp [monomialMoment, boundaryMomentFromGodel, boundaryGodelCode_mem]

/-- The complete monomial-indicator profile determines its finite support. -/
theorem monomialMoment_profile_injective {U V : FiniteMomentSupport}
    (h : ∀ α, monomialMoment α U = monomialMoment α V) : U = V := by
  apply Finset.ext
  intro α
  specialize h α
  by_cases hU : α ∈ U <;> by_cases hV : α ∈ V
  · simp [hU, hV]
  · simp [monomialMoment, hU, hV] at h
  · simp [monomialMoment, hU, hV] at h
  · simp [hU, hV]

/-- The squarefree support code is injective because the encoded labels are injective. -/
theorem boundaryGodelCode_injective :
    Function.Injective (boundaryGodelCode : FiniteMomentSupport → BoundaryGodelCode) := by
  intro U V hcode
  apply monomialMoment_profile_injective
  intro α
  have hU := congrFun (finiteSupport_moment_profile_readout U) α
  have hV := congrFun (finiteSupport_moment_profile_readout V) α
  rw [hU, hV, hcode]

end Omega.SPG
