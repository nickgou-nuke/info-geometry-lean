import InfoGeometry.Quantum.TriadicWeylBridge

/-!
# Constructive Drazin/Weyl Compatibility Owner

Constructive owner interface for routing Drazin-side inverse candidates into the
Weyl-compatibility surface used by `TriadicWeylBridge`.
-/

namespace InfoGeometry.Canonical.DrazinWeylConstructive

open InfoGeometry.Krein
open InfoGeometry.Quantum.TriadicWeylBridge
open InfoGeometry.Canonical.DrazinInfiniteCore
open InfoGeometry.Canonical

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Constructive compatibility datum: a candidate inverse together with the proved
commutation relation against the spectral sheet involution.
-/
structure ConstructiveDrazinWeylData where
  drazinInverse : EndH
  commutes_spectralEpsilon :
    drazinInverse.comp (spectral_epsilon (E := E))
      = (spectral_epsilon (E := E)).comp drazinInverse

/--
Constructive Riesz-side Weyl package: keep the Drazin candidate on the
constructive witness lane and record the spectral-sheet commutation proof there.
-/
structure ConstructiveRieszWeylData (T : EndH) where
  riesz : ConstructiveRieszDecompositionAtZero (𝕂 := ℝ) T
  candidate_commutes_spectralEpsilon :
    (constructiveDrazinCandidate riesz).comp (spectral_epsilon (E := E))
      = (spectral_epsilon (E := E)).comp (constructiveDrazinCandidate riesz)

/-- Shim theorem exporting constructive commutation into legacy Weyl compatibility. -/
theorem drazinInverse_isWeylCompatible
    (D : ConstructiveDrazinWeylData (E := E)) :
    IsWeylCompatible (E := E) D.drazinInverse := by
  exact (isWeylCompatible_iff_comp_spectralEpsilon (E := E) D.drazinInverse).2
    D.commutes_spectralEpsilon

/--
The constructive Riesz candidate is Weyl-compatible once its spectral-sheet
commutation is proved on the witness lane.
-/
theorem constructiveDrazinCandidate_isWeylCompatible
    {T : EndH} (D : ConstructiveRieszWeylData (E := E) T) :
    IsWeylCompatible (E := E) (constructiveDrazinCandidate D.riesz) := by
  exact
    (isWeylCompatible_iff_comp_spectralEpsilon
      (E := E) (constructiveDrazinCandidate D.riesz)).2
      D.candidate_commutes_spectralEpsilon

/--
Constructive Riesz-side Weyl package yields a Drazin witness together with Weyl
compatibility for the same candidate, without any nonconstructive choice.
-/
theorem exists_isDrazinInverse_isWeylCompatible_of_constructiveRieszWeylData
    {T : EndH} (D : ConstructiveRieszWeylData (E := E) T) :
    ∃ k TD,
      Drazin.IsDrazinInverse T TD k ∧ IsWeylCompatible (E := E) TD := by
  refine ⟨D.riesz.k, constructiveDrazinCandidate D.riesz, ?_, ?_⟩
  · exact Drazin.IsDrazinInverse.mk
      (constructiveDrazinCandidate_comm (hR := D.riesz))
      (constructiveDrazinCandidate_inner (hR := D.riesz))
      (constructiveDrazinCandidate_power (hR := D.riesz))
  · exact constructiveDrazinCandidate_isWeylCompatible (E := E) D

/--
Translator-lane specialization: a constructive Drazin witness package produces
Weyl compatibility for the extracted inverse candidate.
-/
theorem rieszDrazinCandidate_isWeylCompatible
    {T : EndH}
    (hR : ConstructiveRieszDecompositionAtZero (𝕂 := ℝ) T)
    (hComm :
      (constructiveDrazinCandidate hR).comp (spectral_epsilon (E := E))
        = (spectral_epsilon (E := E)).comp (constructiveDrazinCandidate hR)) :
    IsWeylCompatible (E := E) (constructiveDrazinCandidate hR) := by
  exact constructiveDrazinCandidate_isWeylCompatible
    (E := E)
    { riesz := hR
      candidate_commutes_spectralEpsilon := hComm }

end InfoGeometry.Canonical.DrazinWeylConstructive
