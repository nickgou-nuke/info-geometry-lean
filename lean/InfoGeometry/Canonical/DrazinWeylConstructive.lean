import InfoGeometry.Quantum.TriadicWeylBridge

set_option linter.unusedSectionVars false

/-!
# Constructive Drazin/Weyl Compatibility Owner

Constructive owner interface for routing Drazin-side inverse candidates into the
Weyl-compatibility surface used by `TriadicWeylBridge`.
-/

namespace DrazinWeylConstructive

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
constructive route and record the spectral-sheet commutation proof there.
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
WeylCompatibility package for the broad infinite Drazin lane: keep the owned infinite
assumptions together with the spectral-sheet commutation proof for the classical
Riesz candidate they already expose.
-/
structure DrazinInfiniteWeylCompatibility (T : EndH) where
  assumptions : DrazinInfiniteAssumptions (𝕂 := ℝ) T
  classical_candidate_commutes_spectralEpsilon :
    assumptions.classical_riesz.D.comp (spectral_epsilon (E := E))
      = (spectral_epsilon (E := E)).comp assumptions.classical_riesz.D

/--
Proof-carrying infinite Drazin compatibility replacing direct classical-candidate
commutation by local Weyl symmetry of the classical Riesz lane.

This is the broad infinite-dimensional analogue of
`ConstructiveRieszLocalWeylSymmetryData`: the structure keeps the owned infinite
assumptions and supplies only operator/projector `ε`-symmetry plus uniqueness of
the regular inverse on that lane.
-/
structure DrazinInfiniteLocalWeylSymmetry (T : EndH) where
  assumptions : DrazinInfiniteAssumptions (𝕂 := ℝ) T
  operator_commutes_spectralEpsilon :
    T.comp (spectral_epsilon (E := E)) = (spectral_epsilon (E := E)).comp T
  projector_commutes_spectralEpsilon :
    assumptions.classical_riesz.P.comp (spectral_epsilon (E := E))
      = (spectral_epsilon (E := E)).comp assumptions.classical_riesz.P
  regular_inverse_unique :
    ∀ S' : EndH,
      S' * T = assumptions.classical_riesz.P →
      T * S' = assumptions.classical_riesz.P →
      S' * assumptions.classical_riesz.P = S' →
      assumptions.classical_riesz.P * S' = S' →
        S' = assumptions.classical_riesz.D

/--
Proof-carrying classical Riesz compatibility for the Weyl bridge: bundle the legacy
classical decomposition structure with the spectral-sheet commutation proof it
already exports.
-/
structure ClassicalRieszWeylCompatibility (T : EndH) where
  classical_riesz : HasClassicalRieszDecompositionAtZero (𝕂 := ℝ) T
  classical_candidate_commutes_spectralEpsilon :
    classical_riesz.D.comp (spectral_epsilon (E := E))
      = (spectral_epsilon (E := E)).comp classical_riesz.D

/--
Proof-carrying classical Riesz compatibility replacing a direct spectral-sheet
commutation proof by local Weyl symmetry of the classical Riesz lane.

This is the classical analogue of
`DrazinInfiniteLocalWeylSymmetry`: keep the owned classical Riesz
package and force the regular inverse by operator/projector `ε`-symmetry plus
uniqueness on the regular lane.
-/
structure ClassicalRieszLocalWeylSymmetry (T : EndH) where
  classical_riesz : HasClassicalRieszDecompositionAtZero (𝕂 := ℝ) T
  operator_commutes_spectralEpsilon :
    T.comp (spectral_epsilon (E := E)) = (spectral_epsilon (E := E)).comp T
  projector_commutes_spectralEpsilon :
    classical_riesz.P.comp (spectral_epsilon (E := E))
      = (spectral_epsilon (E := E)).comp classical_riesz.P
  regular_inverse_unique :
    ∀ S' : EndH,
      S' * T = classical_riesz.P →
      T * S' = classical_riesz.P →
      S' * classical_riesz.P = S' →
      classical_riesz.P * S' = S' →
        S' = classical_riesz.D

/-- Shim theorem exporting constructive commutation into legacy Weyl compatibility. -/
theorem drazinInverse_isWeylCompatible
    (D : ConstructiveDrazinWeylData (E := E)) :
    IsWeylCompatible (E := E) D.drazinInverse := by
  exact (isWeylCompatible_iff_comp_spectralEpsilon (E := E) D.drazinInverse).2
    D.commutes_spectralEpsilon

/--
The constructive Riesz candidate is Weyl-compatible once its spectral-sheet
commutation is proved on the constructive route.
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
Convert the legacy classical Riesz structure plus an explicit spectral-sheet
commutation proof into the constructive Weyl bridge structure.
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
Proof-carrying classical Riesz compatibility route into the constructive Weyl bridge
structure.
-/
def constructiveRieszWeylData_of_classicalRieszWeylCompatibility
    {T : EndH}
    (W : ClassicalRieszWeylCompatibility (E := E) T) :
    ConstructiveRieszWeylData (E := E) T :=
  constructiveRieszWeylData_of_hasClassicalRieszDecompositionAtZero
    (E := E) W.classical_riesz W.classical_candidate_commutes_spectralEpsilon

/--
Convert the classical local-Weyl-symmetry structure into the narrower
constructive local-symmetry owner structure.
-/
def constructiveRieszLocalWeylSymmetryData_of_classicalRieszLocalWeylSymmetry
    {T : EndH}
    (W : ClassicalRieszLocalWeylSymmetry (E := E) T) :
    ConstructiveRieszLocalWeylSymmetryData (E := E) T where
  riesz :=
    constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero
      (𝕂 := ℝ) W.classical_riesz
  operator_commutes_spectralEpsilon := W.operator_commutes_spectralEpsilon
  projector_commutes_spectralEpsilon := by
    simpa [constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero]
      using W.projector_commutes_spectralEpsilon
  regular_inverse_unique := by
    intro S' hLeft hRight hSupportLeft hSupportRight
    simpa [constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero]
      using W.regular_inverse_unique S' hLeft hRight hSupportLeft hSupportRight

/--
Classical local-Weyl-symmetry route into the constructive Weyl bridge structure.
This removes the direct classical-candidate commutation proof on the honest
`ε`-symmetric branch.
-/
def constructiveRieszWeylData_of_classicalRieszLocalWeylSymmetry
    {T : EndH}
    (W : ClassicalRieszLocalWeylSymmetry (E := E) T) :
    ConstructiveRieszWeylData (E := E) T :=
  constructiveRieszWeylData_of_localWeylSymmetry
    (E := E)
    (constructiveRieszLocalWeylSymmetryData_of_classicalRieszLocalWeylSymmetry
      (E := E) W)

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
WeylCompatibility-routed infinite Drazin package: narrow the free commutation hypothesis
surface to one proof-carrying bundle on the infinite lane.
-/
def constructiveRieszWeylData_of_drazinInfiniteWeylCompatibility
    {T : EndH}
    (W : DrazinInfiniteWeylCompatibility (E := E) T) :
    ConstructiveRieszWeylData (E := E) T :=
  constructiveRieszWeylData_of_drazinInfiniteAssumptions
    (E := E) W.assumptions W.classical_candidate_commutes_spectralEpsilon

/--
Convert the broad infinite local-Weyl-symmetry structure into the narrower
constructive local-symmetry owner structure.
-/
def constructiveRieszLocalWeylSymmetryData_of_drazinInfiniteLocalWeylSymmetry
    {T : EndH}
    (W : DrazinInfiniteLocalWeylSymmetry (E := E) T) :
    ConstructiveRieszLocalWeylSymmetryData (E := E) T where
  riesz :=
    constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero
      (𝕂 := ℝ) W.assumptions.classical_riesz
  operator_commutes_spectralEpsilon := W.operator_commutes_spectralEpsilon
  projector_commutes_spectralEpsilon := by
    simpa [constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero]
      using W.projector_commutes_spectralEpsilon
  regular_inverse_unique := by
    intro S' hLeft hRight hSupportLeft hSupportRight
    simpa [constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero]
      using W.regular_inverse_unique S' hLeft hRight hSupportLeft hSupportRight

/--
Convert the broad infinite local-Weyl-symmetry package into the older infinite
Weyl compatibility interface.  This removes the direct classical-candidate
commutation proof from callers that can instead supply operator/projector
`ε`-symmetry plus regular-inverse uniqueness on the infinite Drazin lane.
-/
def drazinInfiniteWeylCompatibility_of_drazinInfiniteLocalWeylSymmetry
    {T : EndH}
    (W : DrazinInfiniteLocalWeylSymmetry (E := E) T) :
    DrazinInfiniteWeylCompatibility (E := E) T where
  assumptions := W.assumptions
  classical_candidate_commutes_spectralEpsilon := by
    simpa [constructiveRieszWeylData_of_localWeylSymmetry,
      constructiveRieszLocalWeylSymmetryData_of_drazinInfiniteLocalWeylSymmetry,
      constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero]
      using
        (constructiveRieszWeylData_of_localWeylSymmetry (E := E)
          (constructiveRieszLocalWeylSymmetryData_of_drazinInfiniteLocalWeylSymmetry
            (E := E) W)).candidate_commutes_spectralEpsilon

/--
Classical Riesz Weyl compatibility route: the converted constructive Drazin candidate
is Weyl-compatible without carrying a separate free commutation hypothesis.
-/
theorem constructiveDrazinCandidate_isWeylCompatible_of_classicalRieszWeylCompatibility
    {T : EndH}
    (W : ClassicalRieszWeylCompatibility (E := E) T) :
    IsWeylCompatible (E := E)
      (constructiveDrazinCandidate
        (constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero
          (𝕂 := ℝ) W.classical_riesz)) := by
  exact constructiveDrazinCandidate_isWeylCompatible
    (E := E)
    (constructiveRieszWeylData_of_classicalRieszWeylCompatibility (E := E) W)

/--
Classical local-symmetry route: the converted constructive Drazin candidate is
Weyl-compatible without carrying a separate direct commutation proof for the
classical Drazin inverse.
-/
theorem constructiveDrazinCandidate_isWeylCompatible_of_classicalRieszLocalWeylSymmetry
    {T : EndH}
    (W : ClassicalRieszLocalWeylSymmetry (E := E) T) :
    IsWeylCompatible (E := E)
      (constructiveDrazinCandidate
        (constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero
          (𝕂 := ℝ) W.classical_riesz)) := by
  exact constructiveDrazinCandidate_isWeylCompatible
    (E := E)
    (constructiveRieszWeylData_of_classicalRieszLocalWeylSymmetry
      (E := E) W)

/--
Classical local Weyl symmetry already forces Weyl compatibility of the owned
classical Drazin inverse itself. This removes the old need to carry a separate
commutation hypothesis for `W.classical_riesz.D` on the classical lane.
-/
theorem classicalDrazinInverse_isWeylCompatible_of_classicalRieszLocalWeylSymmetry
    {T : EndH}
    (W : ClassicalRieszLocalWeylSymmetry (E := E) T) :
    IsWeylCompatible (E := E) W.classical_riesz.D := by
  simpa [constructiveDrazinCandidate,
    constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero] using
    constructiveDrazinCandidate_isWeylCompatible_of_classicalRieszLocalWeylSymmetry
      (E := E) W

/--
Broad infinite compatibility route: the constructive Drazin candidate extracted from
`DrazinInfiniteAssumptions` is Weyl-compatible once the spectral-sheet
commutation proof is bundled into `DrazinInfiniteWeylCompatibility`.
-/
theorem constructiveDrazinCandidate_isWeylCompatible_of_drazinInfiniteWeylCompatibility
    {T : EndH}
    (W : DrazinInfiniteWeylCompatibility (E := E) T) :
    IsWeylCompatible (E := E)
      (constructiveDrazinCandidate
        (constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero
          (𝕂 := ℝ) W.assumptions.classical_riesz)) := by
  exact constructiveDrazinCandidate_isWeylCompatible
    (E := E)
    (constructiveRieszWeylData_of_drazinInfiniteWeylCompatibility (E := E) W)

/--
Infinite local-symmetry route: the constructive Drazin candidate extracted from
`DrazinInfiniteAssumptions` is Weyl-compatible once the classical Riesz lane is
`ε`-symmetric and its regular inverse is uniquely characterized there.
-/
theorem constructiveDrazinCandidate_isWeylCompatible_of_drazinInfiniteLocalWeylSymmetry
    {T : EndH}
    (W : DrazinInfiniteLocalWeylSymmetry (E := E) T) :
    IsWeylCompatible (E := E)
      (constructiveDrazinCandidate
        (constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero
          (𝕂 := ℝ) W.assumptions.classical_riesz)) := by
  exact constructiveDrazinCandidate_isWeylCompatible
    (E := E)
    (constructiveRieszWeylData_of_localWeylSymmetry
      (E := E)
      (constructiveRieszLocalWeylSymmetryData_of_drazinInfiniteLocalWeylSymmetry
        (E := E) W))

/--
Infinite local Weyl symmetry already forces Weyl compatibility of the owned
classical Drazin inverse itself. This removes the old need to carry a separate
commutation hypothesis for `W.assumptions.classical_riesz.D` on the infinite
lane.
-/
theorem classicalDrazinInverse_isWeylCompatible_of_drazinInfiniteLocalWeylSymmetry
    {T : EndH}
    (W : DrazinInfiniteLocalWeylSymmetry (E := E) T) :
    IsWeylCompatible (E := E) W.assumptions.classical_riesz.D := by
  simpa [constructiveDrazinCandidate,
    constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero] using
    constructiveDrazinCandidate_isWeylCompatible_of_drazinInfiniteLocalWeylSymmetry
      (E := E) W

/--
Raw infinite local-Weyl-symmetry route into direct Weyl compatibility for the
constructive Drazin candidate. This removes the explicit classical-candidate
commutation hypothesis from `DrazinInfiniteAssumptions` when the infinite lane
already owns operator/projector `ε`-symmetry plus uniqueness of the regular
inverse.
-/
theorem constructiveDrazinCandidate_isWeylCompatible_of_drazinInfiniteLocalWeylSymmetry_hypotheses
    {T : EndH}
    (h : DrazinInfiniteAssumptions (𝕂 := ℝ) T)
    (hOperator :
      T.comp (spectral_epsilon (E := E)) = (spectral_epsilon (E := E)).comp T)
    (hProjector :
      h.classical_riesz.P.comp (spectral_epsilon (E := E))
        = (spectral_epsilon (E := E)).comp h.classical_riesz.P)
    (hUnique :
      ∀ S' : EndH,
        S' * T = h.classical_riesz.P →
        T * S' = h.classical_riesz.P →
        S' * h.classical_riesz.P = S' →
        h.classical_riesz.P * S' = S' →
          S' = h.classical_riesz.D) :
    IsWeylCompatible (E := E)
      (constructiveDrazinCandidate
        (constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero
          (𝕂 := ℝ) h.classical_riesz)) := by
  exact
    constructiveDrazinCandidate_isWeylCompatible_of_drazinInfiniteLocalWeylSymmetry
      (E := E)
      { assumptions := h
        operator_commutes_spectralEpsilon := hOperator
        projector_commutes_spectralEpsilon := hProjector
        regular_inverse_unique := hUnique }

/--
Raw infinite local-Weyl-symmetry route into direct Weyl compatibility for the
owned classical Drazin inverse. This removes the explicit classical-candidate
commutation hypothesis from `DrazinInfiniteAssumptions` on the honest
`ε`-symmetric branch.
-/
theorem classicalDrazinInverse_isWeylCompatible_of_drazinInfiniteLocalWeylSymmetry_hypotheses
    {T : EndH}
    (h : DrazinInfiniteAssumptions (𝕂 := ℝ) T)
    (hOperator :
      T.comp (spectral_epsilon (E := E)) = (spectral_epsilon (E := E)).comp T)
    (hProjector :
      h.classical_riesz.P.comp (spectral_epsilon (E := E))
        = (spectral_epsilon (E := E)).comp h.classical_riesz.P)
    (hUnique :
      ∀ S' : EndH,
        S' * T = h.classical_riesz.P →
        T * S' = h.classical_riesz.P →
        S' * h.classical_riesz.P = S' →
        h.classical_riesz.P * S' = S' →
          S' = h.classical_riesz.D) :
    IsWeylCompatible (E := E) h.classical_riesz.D := by
  exact
    classicalDrazinInverse_isWeylCompatible_of_drazinInfiniteLocalWeylSymmetry
      (E := E)
      { assumptions := h
        operator_commutes_spectralEpsilon := hOperator
        projector_commutes_spectralEpsilon := hProjector
        regular_inverse_unique := hUnique }

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
Raw classical local-Weyl-symmetry route into direct Weyl compatibility for the
constructive Drazin candidate. This removes the explicit classical-candidate
commutation proof on the honest `ε`-symmetric branch.
-/
theorem constructiveDrazinCandidate_isWeylCompatible_of_hasClassicalRieszLocalWeylSymmetry
    {T : EndH}
    (h : HasClassicalRieszDecompositionAtZero (𝕂 := ℝ) T)
    (hOperator :
      T.comp (spectral_epsilon (E := E)) = (spectral_epsilon (E := E)).comp T)
    (hProjector :
      h.P.comp (spectral_epsilon (E := E))
        = (spectral_epsilon (E := E)).comp h.P)
    (hUnique :
      ∀ S' : EndH,
        S' * T = h.P →
        T * S' = h.P →
        S' * h.P = S' →
        h.P * S' = S' →
          S' = h.D) :
    IsWeylCompatible (E := E)
      (constructiveDrazinCandidate
        (constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero
          (𝕂 := ℝ) h)) := by
  exact constructiveDrazinCandidate_isWeylCompatible_of_classicalRieszLocalWeylSymmetry
    (E := E)
    { classical_riesz := h
      operator_commutes_spectralEpsilon := hOperator
      projector_commutes_spectralEpsilon := hProjector
      regular_inverse_unique := hUnique }

/--
Constructive Riesz-side Weyl structure yields a Drazin inverse together with Weyl
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
Proof-carrying classical Riesz compatibility route into the constructive Drazin/Weyl
existence theorem.
-/
theorem exists_isDrazinInverse_isWeylCompatible_of_classicalRieszWeylCompatibility
    {T : EndH}
    (W : ClassicalRieszWeylCompatibility (E := E) T) :
    ∃ k TD,
      Drazin.IsDrazinInverse T TD k ∧ IsWeylCompatible (E := E) TD := by
  exact
    exists_isDrazinInverse_isWeylCompatible_of_constructiveRieszWeylData
      (E := E)
      (constructiveRieszWeylData_of_classicalRieszWeylCompatibility (E := E) W)

/--
Classical local-Weyl-symmetry compatibility route into the constructive Drazin/Weyl
existence theorem. This removes the explicit classical-candidate commutation
commutation proof from the classical Riesz lane on the honest `ε`-symmetric branch.
-/
theorem exists_isDrazinInverse_isWeylCompatible_of_classicalRieszLocalWeylSymmetry
    {T : EndH}
    (W : ClassicalRieszLocalWeylSymmetry (E := E) T) :
    ∃ k TD,
      Drazin.IsDrazinInverse T TD k ∧ IsWeylCompatible (E := E) TD := by
  exact
    exists_isDrazinInverse_isWeylCompatible_of_constructiveRieszWeylData
      (E := E)
      (constructiveRieszWeylData_of_classicalRieszLocalWeylSymmetry
        (E := E) W)

/--
Classical Riesz compatibility lane exports the same constructive Drazin/Weyl package
without repeating the existential construction downstream.
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
    exists_isDrazinInverse_isWeylCompatible_of_classicalRieszWeylCompatibility
      (E := E)
      { classical_riesz := h
        classical_candidate_commutes_spectralEpsilon := hComm }

/--
Classical Riesz local-Weyl route into the same constructive Drazin/Weyl
existence theorem.  This avoids the direct candidate commutation hypothesis
`h.D.comp ε = ε.comp h.D`; the commutation is forced by operator/projector
`ε`-symmetry plus uniqueness of the regular inverse on the classical Riesz lane.
-/
theorem exists_isDrazinInverse_isWeylCompatible_of_hasClassicalRieszLocalWeylSymmetry
    {T : EndH}
    (h : HasClassicalRieszDecompositionAtZero (𝕂 := ℝ) T)
    (hOperator :
      T.comp (spectral_epsilon (E := E)) = (spectral_epsilon (E := E)).comp T)
    (hProjector :
      h.P.comp (spectral_epsilon (E := E))
        = (spectral_epsilon (E := E)).comp h.P)
    (hUnique :
      ∀ S' : EndH,
        S' * T = h.P →
        T * S' = h.P →
        S' * h.P = S' →
        h.P * S' = S' →
          S' = h.D) :
    ∃ k TD,
      Drazin.IsDrazinInverse T TD k ∧ IsWeylCompatible (E := E) TD := by
  exact
    exists_isDrazinInverse_isWeylCompatible_of_classicalRieszLocalWeylSymmetry
      (E := E)
      { classical_riesz := h
        operator_commutes_spectralEpsilon := hOperator
        projector_commutes_spectralEpsilon := hProjector
        regular_inverse_unique := hUnique }

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
Proof-carrying infinite Drazin compatibility route into the constructive Drazin/Weyl
existence theorem.
-/
theorem exists_isDrazinInverse_isWeylCompatible_of_drazinInfiniteWeylCompatibility
    {T : EndH}
    (W : DrazinInfiniteWeylCompatibility (E := E) T) :
    ∃ k TD,
      Drazin.IsDrazinInverse T TD k ∧ IsWeylCompatible (E := E) TD := by
  exact
    exists_isDrazinInverse_isWeylCompatible_of_constructiveRieszWeylData
      (E := E)
      (constructiveRieszWeylData_of_drazinInfiniteWeylCompatibility (E := E) W)

/--
Broad infinite local-symmetry route into the constructive Drazin/Weyl existence
theorem. This removes the explicit classical-candidate commutation proof from
the infinite assumption lane on the honest `ε`-symmetric branch.
-/
theorem exists_isDrazinInverse_isWeylCompatible_of_drazinInfiniteLocalWeylSymmetry
    {T : EndH}
    (W : DrazinInfiniteLocalWeylSymmetry (E := E) T) :
    ∃ k TD,
      Drazin.IsDrazinInverse T TD k ∧ IsWeylCompatible (E := E) TD := by
  exact
    exists_isDrazinInverse_isWeylCompatible_of_constructiveRieszWeylData
      (E := E)
      (constructiveRieszWeylData_of_localWeylSymmetry
        (E := E)
        (constructiveRieszLocalWeylSymmetryData_of_drazinInfiniteLocalWeylSymmetry
          (E := E) W))

/--
Raw infinite local-Weyl-symmetry route into the constructive Drazin/Weyl
existence theorem. This removes the explicit classical-candidate commutation
hypothesis from `DrazinInfiniteAssumptions` on the honest `ε`-symmetric branch.
-/
theorem exists_isDrazinInverse_isWeylCompatible_of_drazinInfiniteLocalWeylSymmetry_hypotheses
    {T : EndH}
    (h : DrazinInfiniteAssumptions (𝕂 := ℝ) T)
    (hOperator :
      T.comp (spectral_epsilon (E := E)) = (spectral_epsilon (E := E)).comp T)
    (hProjector :
      h.classical_riesz.P.comp (spectral_epsilon (E := E))
        = (spectral_epsilon (E := E)).comp h.classical_riesz.P)
    (hUnique :
      ∀ S' : EndH,
        S' * T = h.classical_riesz.P →
        T * S' = h.classical_riesz.P →
        S' * h.classical_riesz.P = S' →
        h.classical_riesz.P * S' = S' →
          S' = h.classical_riesz.D) :
    ∃ k TD,
      Drazin.IsDrazinInverse T TD k ∧ IsWeylCompatible (E := E) TD := by
  exact
    exists_isDrazinInverse_isWeylCompatible_of_drazinInfiniteLocalWeylSymmetry
      (E := E)
      { assumptions := h
        operator_commutes_spectralEpsilon := hOperator
        projector_commutes_spectralEpsilon := hProjector
        regular_inverse_unique := hUnique }

/--
Constructive local-symmetry variant of the D2 theorem. The Weyl
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
Translator-lane specialization: the constructive Drazin candidate extracted
from a proof-carrying classical Riesz Weyl compatibility is Weyl-compatible without a
separate free candidate-commutation hypothesis.
-/
theorem rieszDrazinCandidate_isWeylCompatible_of_classicalRieszWeylCompatibility
    {T : EndH}
    (W : ClassicalRieszWeylCompatibility (E := E) T) :
    IsWeylCompatible (E := E)
      (constructiveDrazinCandidate
        (constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero
          (𝕂 := ℝ) W.classical_riesz)) := by
  exact constructiveDrazinCandidate_isWeylCompatible_of_classicalRieszWeylCompatibility
    (E := E) W

/--
Translator-lane specialization: the constructive Drazin candidate extracted
from a proof-carrying classical local-Weyl-symmetry structure is Weyl-compatible
without a separate free candidate-commutation hypothesis.
-/
theorem rieszDrazinCandidate_isWeylCompatible_of_classicalRieszLocalWeylSymmetry
    {T : EndH}
    (W : ClassicalRieszLocalWeylSymmetry (E := E) T) :
    IsWeylCompatible (E := E)
      (constructiveDrazinCandidate
        (constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero
          (𝕂 := ℝ) W.classical_riesz)) := by
  exact
    constructiveDrazinCandidate_isWeylCompatible_of_classicalRieszLocalWeylSymmetry
      (E := E) W

/--
Translator-lane specialization: the constructive Drazin candidate extracted
from a proof-carrying infinite Drazin Weyl compatibility is Weyl-compatible without a
separate free candidate-commutation hypothesis.
-/
theorem rieszDrazinCandidate_isWeylCompatible_of_drazinInfiniteWeylCompatibility
    {T : EndH}
    (W : DrazinInfiniteWeylCompatibility (E := E) T) :
    IsWeylCompatible (E := E)
      (constructiveDrazinCandidate
        (constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero
          (𝕂 := ℝ) W.assumptions.classical_riesz)) := by
  exact constructiveDrazinCandidate_isWeylCompatible_of_drazinInfiniteWeylCompatibility
    (E := E) W

/--
Translator-lane specialization on the honest local-symmetry branch: the
constructive Drazin candidate is Weyl-compatible without a separate free
candidate-commutation hypothesis.
-/
theorem rieszDrazinCandidate_isWeylCompatible_of_localWeylSymmetry
    {T : EndH}
    (D : ConstructiveRieszLocalWeylSymmetryData (E := E) T) :
    IsWeylCompatible (E := E) (constructiveDrazinCandidate D.riesz) := by
  exact constructiveDrazinCandidate_isWeylCompatible_of_localWeylSymmetry
    (E := E) D

/--
Translator-lane specialization on the infinite local-Weyl-symmetry branch: the
constructive Drazin candidate extracted from the classical Riesz component of a
proof-carrying `DrazinInfiniteLocalWeylSymmetry` is Weyl-compatible
without a separate free candidate-commutation hypothesis.
-/
theorem rieszDrazinCandidate_isWeylCompatible_of_drazinInfiniteLocalWeylSymmetry
    {T : EndH}
    (W : DrazinInfiniteLocalWeylSymmetry (E := E) T) :
    IsWeylCompatible (E := E)
      (constructiveDrazinCandidate
        (constructiveRieszDecompositionAtZero_of_hasClassicalRieszDecompositionAtZero
          (𝕂 := ℝ) W.assumptions.classical_riesz)) := by
  exact constructiveDrazinCandidate_isWeylCompatible_of_drazinInfiniteLocalWeylSymmetry
    (E := E) W

/--
Translator-lane specialization: a constructive Drazin structure produces
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

end DrazinWeylConstructive
