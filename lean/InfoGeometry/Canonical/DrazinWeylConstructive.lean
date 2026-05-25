import InfoGeometry.Quantum.TriadicWeylBridge

set_option linter.unusedSectionVars false

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

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

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

/--
Local Weyl symmetry package for a constructive Riesz problem.

This removes the direct candidate-commutation assumption from the constructive
lane.  Instead, the regular problem is symmetric under the sheet involution
`ε`, and the regular inverse is unique among maps satisfying the same
regular-lane inverse/support equations.  The Drazin candidate is then forced to
commute with `ε`.
-/
structure ConstructiveRieszLocalWeylSymmetryData (T : EndH) where
  riesz : ConstructiveRieszDecompositionAtZero (𝕂 := ℝ) T
  operator_commutes_spectralEpsilon :
    T.comp (spectral_epsilon (E := E)) = (spectral_epsilon (E := E)).comp T
  projector_commutes_spectralEpsilon :
    riesz.P.comp (spectral_epsilon (E := E))
      = (spectral_epsilon (E := E)).comp riesz.P
  regular_inverse_unique :
    ∀ S' : EndH,
      S' * T = riesz.P →
      T * S' = riesz.P →
      S' * riesz.P = S' →
      riesz.P * S' = S' →
        S' = riesz.S

/--
Witness package for the broad infinite Drazin lane: keep the owned infinite
assumptions together with the spectral-sheet commutation proof for the classical
Riesz candidate they already expose.
-/
structure DrazinInfiniteWeylWitness (T : EndH) where
  assumptions : DrazinInfiniteAssumptions (𝕂 := ℝ) T
  classical_candidate_commutes_spectralEpsilon :
    assumptions.classical_riesz.D.comp (spectral_epsilon (E := E))
      = (spectral_epsilon (E := E)).comp assumptions.classical_riesz.D

/--
Proof-carrying classical Riesz witness for the Weyl bridge: bundle the legacy
classical decomposition witness with the spectral-sheet commutation proof it
already exports.
-/
structure ClassicalRieszWeylWitness (T : EndH) where
  classical_riesz : HasClassicalRieszDecompositionAtZero (𝕂 := ℝ) T
  classical_candidate_commutes_spectralEpsilon :
    classical_riesz.D.comp (spectral_epsilon (E := E))
      = (spectral_epsilon (E := E)).comp classical_riesz.D

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
The ε-conjugate of the constructive regular inverse is the same inverse when
the Riesz regular problem is locally Weyl-symmetric and the regular inverse is
unique. This is the constructive D2 forcing step.
-/
theorem spectralEpsilon_conj_constructiveDrazinCandidate_eq
    {T : EndH}
    (D : ConstructiveRieszLocalWeylSymmetryData (E := E) T) :
    (spectral_epsilon (E := E)) *
        constructiveDrazinCandidate D.riesz *
          (spectral_epsilon (E := E))
      =
    constructiveDrazinCandidate D.riesz := by
  let ε : EndH := spectral_epsilon (E := E)
  let Sε : EndH := ε * D.riesz.S * ε
  have hε2 : ε * ε = ContinuousLinearMap.id ℝ H₂ := by
    apply ContinuousLinearMap.ext
    intro x
    apply DoubledSpace.ext <;> simp [ε, spectral_epsilon]
  have hTε : T * ε = ε * T := by
    simpa [ε] using D.operator_commutes_spectralEpsilon
  have hPε : D.riesz.P * ε = ε * D.riesz.P := by
    simpa [ε] using D.projector_commutes_spectralEpsilon
  have hSε_left : Sε * T = D.riesz.P := by
    calc
      Sε * T = ε * D.riesz.S * ε * T := by simp [Sε, mul_assoc]
      _ = ε * D.riesz.S * (ε * T) := by simp [mul_assoc]
      _ = ε * D.riesz.S * (T * ε) := by rw [hTε]
      _ = ε * (D.riesz.S * T) * ε := by simp [mul_assoc]
      _ = ε * D.riesz.P * ε := by rw [D.riesz.left_inverse_on_regular]
      _ = (ε * D.riesz.P) * ε := by simp [mul_assoc]
      _ = (D.riesz.P * ε) * ε := by rw [← hPε]
      _ = D.riesz.P * (ε * ε) := by simp [mul_assoc]
      _ = D.riesz.P * ContinuousLinearMap.id ℝ H₂ := by rw [hε2]
      _ = D.riesz.P := by
        apply ContinuousLinearMap.ext
        intro x
        apply DoubledSpace.ext <;> simp
  have hSε_right : T * Sε = D.riesz.P := by
    calc
      T * Sε = T * (ε * D.riesz.S * ε) := by simp [Sε]
      _ = (T * ε) * D.riesz.S * ε := by simp [mul_assoc]
      _ = (ε * T) * D.riesz.S * ε := by rw [hTε]
      _ = ε * (T * D.riesz.S) * ε := by simp [mul_assoc]
      _ = ε * D.riesz.P * ε := by rw [D.riesz.right_inverse_on_regular]
      _ = (ε * D.riesz.P) * ε := by simp [mul_assoc]
      _ = (D.riesz.P * ε) * ε := by rw [← hPε]
      _ = D.riesz.P * (ε * ε) := by simp [mul_assoc]
      _ = D.riesz.P * ContinuousLinearMap.id ℝ H₂ := by rw [hε2]
      _ = D.riesz.P := by
        apply ContinuousLinearMap.ext
        intro x
        apply DoubledSpace.ext <;> simp
  have hSε_support_left : Sε * D.riesz.P = Sε := by
    calc
      Sε * D.riesz.P = ε * D.riesz.S * ε * D.riesz.P := by simp [Sε, mul_assoc]
      _ = ε * D.riesz.S * (ε * D.riesz.P) := by simp [mul_assoc]
      _ = ε * D.riesz.S * (D.riesz.P * ε) := by rw [← hPε]
      _ = ε * (D.riesz.S * D.riesz.P) * ε := by simp [mul_assoc]
      _ = ε * D.riesz.S * ε := by rw [D.riesz.S_supported_on_regular_left]
      _ = Sε := by rfl
  have hSε_support_right : D.riesz.P * Sε = Sε := by
    calc
      D.riesz.P * Sε = D.riesz.P * (ε * D.riesz.S * ε) := by simp [Sε]
      _ = (D.riesz.P * ε) * D.riesz.S * ε := by simp [mul_assoc]
      _ = (ε * D.riesz.P) * D.riesz.S * ε := by rw [hPε]
      _ = ε * (D.riesz.P * D.riesz.S) * ε := by simp [mul_assoc]
      _ = ε * D.riesz.S * ε := by rw [D.riesz.S_supported_on_regular_right]
      _ = Sε := by rfl
  simpa [constructiveDrazinCandidate, Sε, ε] using
    D.regular_inverse_unique Sε hSε_left hSε_right hSε_support_left hSε_support_right

/--
Local Weyl symmetry of the constructive Riesz problem forces the extracted
Drazin candidate to commute with the sheet involution.
-/
theorem constructiveDrazinCandidate_commutes_spectralEpsilon_of_localWeylSymmetry
    {T : EndH}
    (D : ConstructiveRieszLocalWeylSymmetryData (E := E) T) :
    (constructiveDrazinCandidate D.riesz).comp (spectral_epsilon (E := E))
      =
    (spectral_epsilon (E := E)).comp (constructiveDrazinCandidate D.riesz) := by
  let ε : EndH := spectral_epsilon (E := E)
  have hConj :
      ε * constructiveDrazinCandidate D.riesz * ε =
        constructiveDrazinCandidate D.riesz :=
    spectralEpsilon_conj_constructiveDrazinCandidate_eq (E := E) D
  apply ContinuousLinearMap.ext
  intro x
  have hAtεx :=
    congrArg (fun F : EndH => F (ε x)) hConj
  have hε2x : ε (ε x) = x := by
    exact congrArg (fun F : EndH => F x) (spectral_epsilon_involution (E := E))
  simpa [ε, ContinuousLinearMap.comp_apply, mul_assoc, hε2x] using hAtεx.symm

/--
Local Weyl symmetry discharges the older raw candidate-commutation package.
This is the bridge constructor downstream code should use when it has an
ε-symmetric Riesz problem plus regular-inverse uniqueness, rather than a direct
commutation proof for the extracted Drazin candidate.
-/
def constructiveRieszWeylData_of_localWeylSymmetry
    {T : EndH}
    (D : ConstructiveRieszLocalWeylSymmetryData (E := E) T) :
    ConstructiveRieszWeylData (E := E) T where
  riesz := D.riesz
  candidate_commutes_spectralEpsilon :=
    constructiveDrazinCandidate_commutes_spectralEpsilon_of_localWeylSymmetry
      (E := E) D

/--
Package the legacy classical Riesz witness plus an explicit spectral-sheet
commutation proof into the constructive Weyl bridge packet.
-/
def constructiveRieszWeylData_of_hasClassicalRieszDecompositionAtZero
    {T : EndH}
    (h : HasClassicalRieszDecompositionAtZero (𝕂 := ℝ) T)
    (hComm :
      h.D.comp (spectral_epsilon (E := E))
        = (spectral_epsilon (E := E)).comp h.D) :
    ConstructiveRieszWeylData (E := E) T where
  riesz :=
    constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero
      (𝕂 := ℝ) h
  candidate_commutes_spectralEpsilon := by
    simpa [constructiveDrazinCandidate,
      constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero] using hComm

/--
Proof-carrying classical Riesz witness route into the constructive Weyl bridge
packet.
-/
def constructiveRieszWeylData_of_classicalRieszWeylWitness
    {T : EndH}
    (W : ClassicalRieszWeylWitness (E := E) T) :
    ConstructiveRieszWeylData (E := E) T :=
  constructiveRieszWeylData_of_hasClassicalRieszDecompositionAtZero
    (E := E) W.classical_riesz W.classical_candidate_commutes_spectralEpsilon

/--
Package the broad infinite Drazin assumption lane into the constructive Weyl
bridge using its owned classical Riesz component.
-/
def constructiveRieszWeylData_of_drazinInfiniteAssumptions
    {T : EndH}
    (h : DrazinInfiniteAssumptions (𝕂 := ℝ) T)
    (hComm :
      h.classical_riesz.D.comp (spectral_epsilon (E := E))
        = (spectral_epsilon (E := E)).comp h.classical_riesz.D) :
    ConstructiveRieszWeylData (E := E) T :=
  constructiveRieszWeylData_of_hasClassicalRieszDecompositionAtZero
    (E := E) h.classical_riesz hComm

/--
Witness-routed infinite Drazin package: narrow the free commutation hypothesis
surface to one proof-carrying bundle on the infinite lane.
-/
def constructiveRieszWeylData_of_drazinInfiniteWeylWitness
    {T : EndH}
    (W : DrazinInfiniteWeylWitness (E := E) T) :
    ConstructiveRieszWeylData (E := E) T :=
  constructiveRieszWeylData_of_drazinInfiniteAssumptions
    (E := E) W.assumptions W.classical_candidate_commutes_spectralEpsilon

/--
Classical Riesz Weyl witness route: the converted constructive Drazin candidate
is Weyl-compatible without carrying a separate free commutation hypothesis.
-/
theorem constructiveDrazinCandidate_isWeylCompatible_of_classicalRieszWeylWitness
    {T : EndH}
    (W : ClassicalRieszWeylWitness (E := E) T) :
    IsWeylCompatible (E := E)
      (constructiveDrazinCandidate
        (constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero
          (𝕂 := ℝ) W.classical_riesz)) := by
  exact constructiveDrazinCandidate_isWeylCompatible
    (E := E)
    (constructiveRieszWeylData_of_classicalRieszWeylWitness (E := E) W)

/--
Broad infinite witness route: the constructive Drazin candidate extracted from
`DrazinInfiniteAssumptions` is Weyl-compatible once the spectral-sheet
commutation proof is bundled into `DrazinInfiniteWeylWitness`.
-/
theorem constructiveDrazinCandidate_isWeylCompatible_of_drazinInfiniteWeylWitness
    {T : EndH}
    (W : DrazinInfiniteWeylWitness (E := E) T) :
    IsWeylCompatible (E := E)
      (constructiveDrazinCandidate
        (constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero
          (𝕂 := ℝ) W.assumptions.classical_riesz)) := by
  exact constructiveDrazinCandidate_isWeylCompatible
    (E := E)
    (constructiveRieszWeylData_of_drazinInfiniteWeylWitness (E := E) W)

/--
Constructive D2 bridge: local Weyl symmetry and uniqueness of the regular
Riesz inverse imply Weyl compatibility of the constructive Drazin candidate.
-/
theorem constructiveDrazinCandidate_isWeylCompatible_of_localWeylSymmetry
    {T : EndH}
    (D : ConstructiveRieszLocalWeylSymmetryData (E := E) T) :
    IsWeylCompatible (E := E) (constructiveDrazinCandidate D.riesz) := by
  exact
    (isWeylCompatible_iff_comp_spectralEpsilon
      (E := E) (constructiveDrazinCandidate D.riesz)).2
      (constructiveDrazinCandidate_commutes_spectralEpsilon_of_localWeylSymmetry
        (E := E) D)

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
Proof-carrying classical Riesz witness route into the constructive Drazin/Weyl
existence theorem.
-/
theorem exists_isDrazinInverse_isWeylCompatible_of_classicalRieszWeylWitness
    {T : EndH}
    (W : ClassicalRieszWeylWitness (E := E) T) :
    ∃ k TD,
      Drazin.IsDrazinInverse T TD k ∧ IsWeylCompatible (E := E) TD := by
  exact
    exists_isDrazinInverse_isWeylCompatible_of_constructiveRieszWeylData
      (E := E)
      (constructiveRieszWeylData_of_classicalRieszWeylWitness (E := E) W)

/--
Classical Riesz witness lane exports the same constructive Drazin/Weyl package
without repeating the existential witness construction downstream.
-/
theorem exists_isDrazinInverse_isWeylCompatible_of_hasClassicalRieszDecompositionAtZero
    {T : EndH}
    (h : HasClassicalRieszDecompositionAtZero (𝕂 := ℝ) T)
    (hComm :
      h.D.comp (spectral_epsilon (E := E))
        = (spectral_epsilon (E := E)).comp h.D) :
    ∃ k TD,
      Drazin.IsDrazinInverse T TD k ∧ IsWeylCompatible (E := E) TD := by
  exact
    exists_isDrazinInverse_isWeylCompatible_of_classicalRieszWeylWitness
      (E := E)
      { classical_riesz := h
        classical_candidate_commutes_spectralEpsilon := hComm }

/--
Broad infinite Drazin assumptions export the same constructive Drazin/Weyl
package through their owned classical Riesz component.
-/
theorem exists_isDrazinInverse_isWeylCompatible_of_drazinInfiniteAssumptions
    {T : EndH}
    (h : DrazinInfiniteAssumptions (𝕂 := ℝ) T)
    (hComm :
      h.classical_riesz.D.comp (spectral_epsilon (E := E))
        = (spectral_epsilon (E := E)).comp h.classical_riesz.D) :
    ∃ k TD,
      Drazin.IsDrazinInverse T TD k ∧ IsWeylCompatible (E := E) TD := by
  exact
    exists_isDrazinInverse_isWeylCompatible_of_constructiveRieszWeylData
      (E := E)
      (constructiveRieszWeylData_of_drazinInfiniteAssumptions
        (E := E) h hComm)

/--
Proof-carrying infinite Drazin witness route into the constructive Drazin/Weyl
existence theorem.
-/
theorem exists_isDrazinInverse_isWeylCompatible_of_drazinInfiniteWeylWitness
    {T : EndH}
    (W : DrazinInfiniteWeylWitness (E := E) T) :
    ∃ k TD,
      Drazin.IsDrazinInverse T TD k ∧ IsWeylCompatible (E := E) TD := by
  exact
    exists_isDrazinInverse_isWeylCompatible_of_constructiveRieszWeylData
      (E := E)
      (constructiveRieszWeylData_of_drazinInfiniteWeylWitness (E := E) W)

/--
Constructive local-symmetry variant of the D2 witness theorem. The Weyl
compatibility proof is derived from ε-symmetry plus uniqueness, not supplied as
direct candidate commutation.
-/
theorem exists_isDrazinInverse_isWeylCompatible_of_localWeylSymmetry
    {T : EndH} (D : ConstructiveRieszLocalWeylSymmetryData (E := E) T) :
    ∃ k TD,
      Drazin.IsDrazinInverse T TD k ∧ IsWeylCompatible (E := E) TD := by
  refine ⟨D.riesz.k, constructiveDrazinCandidate D.riesz, ?_, ?_⟩
  · exact Drazin.IsDrazinInverse.mk
      (constructiveDrazinCandidate_comm (hR := D.riesz))
      (constructiveDrazinCandidate_inner (hR := D.riesz))
      (constructiveDrazinCandidate_power (hR := D.riesz))
  · exact constructiveDrazinCandidate_isWeylCompatible_of_localWeylSymmetry
      (E := E) D

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
