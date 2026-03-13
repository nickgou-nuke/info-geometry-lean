import InfoGeometry.Canonical.Clifford

namespace InfoGeometry.Canonical.TomitaTakesaki

open InfoGeometry.Clifford
open InfoGeometry.Krein

/-!
# Tomita-Takesaki Modular Atom (Split `Cl(1,1)`)

This module packages the modular pair (`J`, `ε`) on doubled real space and
connects it to the exact split Clifford algebra used in routing:
`SplitCliffordAlg = CliffordAlgebra splitQ11`.
-/

section CliffordAtom

/-- The split Clifford algebra used by routing modules (`Cl(1,1)`). -/
noncomputable abbrev RoutingSplitCliffordAlg := CliffordAlgebra splitQ11

/-- Clifford generator corresponding to the modular conjugation direction. -/
noncomputable def cptJ : RoutingSplitCliffordAlg :=
  CliffordAlgebra.ι splitQ11 (1, 0)

/-- Clifford generator corresponding to `Jε` direction (complex structure axis). -/
noncomputable def cptJeps : RoutingSplitCliffordAlg :=
  CliffordAlgebra.ι splitQ11 (0, 1)

/-- Pseudoscalar `ε = J * (Jε)` in this sign convention. -/
noncomputable def cptEps : RoutingSplitCliffordAlg :=
  cptJ * cptJeps

/-- The four CPT atoms `{1, J, ε, Jε}` in split Clifford form. -/
def cptAtomSet : Set RoutingSplitCliffordAlg :=
  {1, cptJ, cptEps, cptJeps}

@[simp] lemma cptJ_sq :
    cptJ * cptJ = algebraMap ℝ RoutingSplitCliffordAlg 1 := by
  simp [cptJ, splitQ11_apply]

@[simp] lemma cptJeps_sq :
    cptJeps * cptJeps = algebraMap ℝ RoutingSplitCliffordAlg (-1) := by
  simp [cptJeps, splitQ11_apply]

/-- Lemma `cptJ_cptJeps_anticommute`. -/
lemma cptJ_cptJeps_anticommute :
    cptJ * cptJeps = -(cptJeps * cptJ) := by
  have hpolar : QuadraticMap.polar splitQ11 ((1 : ℝ), 0) ((0 : ℝ), 1) = 0 := by
    simp [QuadraticMap.polar, splitQ11_apply]
  rw [cptJ, cptJeps,
      CliffordAlgebra.ι_mul_ι_comm (Q := splitQ11) (a := ((1 : ℝ), 0)) (b := ((0 : ℝ), 1)),
      hpolar]
  simp

/-- Lemma `iota_mem_adjoin_cptAtomSet`. -/
lemma iota_mem_adjoin_cptAtomSet (v : ℝ × ℝ) :
    CliffordAlgebra.ι splitQ11 v ∈ Algebra.adjoin ℝ cptAtomSet := by
  have hJ : cptJ ∈ Algebra.adjoin ℝ cptAtomSet := by
    exact Algebra.subset_adjoin (by simp [cptAtomSet, cptJ])
  have hJeps : cptJeps ∈ Algebra.adjoin ℝ cptAtomSet := by
    exact Algebra.subset_adjoin (by simp [cptAtomSet, cptJeps])
  rcases v with ⟨a, b⟩
  have hdecomp :
      CliffordAlgebra.ι splitQ11 (a, b) = a • cptJ + b • cptJeps := by
    have hpair :
        ((a, b) : ℝ × ℝ)
          = a • (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ)
            + b • (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ) := by
      ext <;> simp
    calc
      CliffordAlgebra.ι splitQ11 (a, b)
          = CliffordAlgebra.ι splitQ11
              (a • (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ)
                + b • (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ)) := by
                rw [hpair]
      _ = a • CliffordAlgebra.ι splitQ11 (1, 0) + b • CliffordAlgebra.ι splitQ11 (0, 1) := by
            rw [(CliffordAlgebra.ι splitQ11).map_add,
                (CliffordAlgebra.ι splitQ11).map_smul,
                (CliffordAlgebra.ι splitQ11).map_smul]
      _ = a • cptJ + b • cptJeps := by simp [cptJ, cptJeps]
  have hsum : a • cptJ + b • cptJeps ∈ Algebra.adjoin ℝ cptAtomSet :=
    (Algebra.adjoin ℝ cptAtomSet).add_mem
      ((Algebra.adjoin ℝ cptAtomSet).smul_mem hJ a)
      ((Algebra.adjoin ℝ cptAtomSet).smul_mem hJeps b)
  simpa [hdecomp] using hsum

/-- Lemma `iota_range_subset_adjoin_cptAtomSet`. -/
lemma iota_range_subset_adjoin_cptAtomSet :
    Set.range (CliffordAlgebra.ι splitQ11) ⊆ Algebra.adjoin ℝ cptAtomSet := by
  intro x hx
  rcases hx with ⟨v, rfl⟩
  exact iota_mem_adjoin_cptAtomSet v

/--
Generator theorem: the CPT atom set `{1, J, ε, Jε}` generates the full split
Clifford algebra used in routing.
-/
theorem cptAtoms_generate_splitCliffordAlg :
    Algebra.adjoin ℝ cptAtomSet = ⊤ := by
  have hle :
      Algebra.adjoin ℝ (Set.range (CliffordAlgebra.ι splitQ11))
        ≤ Algebra.adjoin ℝ cptAtomSet := by
    refine Algebra.adjoin_le ?_
    intro x hx
    exact iota_range_subset_adjoin_cptAtomSet hx
  have htop :
      Algebra.adjoin ℝ (Set.range (CliffordAlgebra.ι splitQ11)) = ⊤ :=
    CliffordAlgebra.adjoin_range_ι (R := ℝ) (Q := splitQ11)
  apply top_unique
  simpa [htop] using hle

end CliffordAtom

section ModularRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Modular conjugation `J` (real-linear model of antilinear conjugation on complex space).
-/
noncomputable abbrev modularConjugationJ : DoubledSpace E →L[ℝ] DoubledSpace E :=
  modular_j (E := E)

/-- Modular sign involution `ε = sgn(K)`. -/
noncomputable abbrev modularSignEpsilon : DoubledSpace E →L[ℝ] DoubledSpace E :=
  spectral_epsilon (E := E)

/-- Composite `Jε`, the split-complex structure axis. -/
noncomputable abbrev modularComplexI : DoubledSpace E →L[ℝ] DoubledSpace E :=
  complex_i (E := E)

@[simp] lemma modularConjugationJ_sq :
    (modularConjugationJ (E := E)).comp (modularConjugationJ (E := E))
      = ContinuousLinearMap.id ℝ (DoubledSpace E) :=
  modular_j_involution (E := E)

@[simp] lemma modularSignEpsilon_sq :
    (modularSignEpsilon (E := E)).comp (modularSignEpsilon (E := E))
      = ContinuousLinearMap.id ℝ (DoubledSpace E) :=
  spectral_epsilon_involution (E := E)

/-- Lemma `modularConjugationJ_anticommutes_modularSign`. -/
lemma modularConjugationJ_anticommutes_modularSign :
    (modularConjugationJ (E := E)).comp (modularSignEpsilon (E := E))
      = -((modularSignEpsilon (E := E)).comp (modularConjugationJ (E := E))) :=
  modular_j_spectral_epsilon_anticommute (E := E)

@[simp] lemma modularComplexI_sq :
    (modularComplexI (E := E)).comp (modularComplexI (E := E))
      = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) :=
  complex_i_sq (E := E)

/-- `J` is even for the doubled-space `Z₂` grading. -/
lemma modularConjugationJ_isEven :
    isEven (E := E) (modularConjugationJ (E := E)) := by
  unfold isEven modularConjugationJ
  rfl

/-- `ε = sgn(K)` is odd for the doubled-space `Z₂` grading. -/
lemma modularSignEpsilon_isOdd :
    isOdd (E := E) (modularSignEpsilon (E := E)) := by
  simpa [modularSignEpsilon] using (spectral_epsilon_isOdd (E := E))

/-- `Jε` is odd for the doubled-space `Z₂` grading. -/
lemma modularComplexI_isOdd :
    isOdd (E := E) (modularComplexI (E := E)) := by
  simpa [modularComplexI] using (complex_i_isOdd (E := E))

/--
Odd-odd channel for the modular CPT atom vanishes:
`Jε + εJ = 0`.
-/
lemma modularConjugationJ_anticommutator_modularSignEpsilon :
    (modularConjugationJ (E := E)).comp (modularSignEpsilon (E := E))
      + (modularSignEpsilon (E := E)).comp (modularConjugationJ (E := E))
      = 0 := by
  have hanti := modularConjugationJ_anticommutes_modularSign (E := E)
  calc
    (modularConjugationJ (E := E)).comp (modularSignEpsilon (E := E))
        + (modularSignEpsilon (E := E)).comp (modularConjugationJ (E := E))
      = -((modularSignEpsilon (E := E)).comp (modularConjugationJ (E := E)))
          + (modularSignEpsilon (E := E)).comp (modularConjugationJ (E := E)) := by rw [hanti]
    _ = 0 := by abel

/--
Even-odd channel for the modular CPT atom:
`[J, ε] = 2(Jε)`.
-/
lemma modularConjugationJ_commutator_modularSignEpsilon :
    (modularConjugationJ (E := E)).comp (modularSignEpsilon (E := E))
      - (modularSignEpsilon (E := E)).comp (modularConjugationJ (E := E))
      = (2 : ℝ) • ((modularConjugationJ (E := E)).comp (modularSignEpsilon (E := E))) := by
  have hanti := modularConjugationJ_anticommutes_modularSign (E := E)
  let A := (modularConjugationJ (E := E)).comp (modularSignEpsilon (E := E))
  have htwo : (2 : ℝ) • A = A + A := by
    simpa using (two_smul ℝ A)
  calc
    (modularConjugationJ (E := E)).comp (modularSignEpsilon (E := E))
        - (modularSignEpsilon (E := E)).comp (modularConjugationJ (E := E))
      = A + A := by
          simp [A, sub_eq_add_neg, hanti]
    _ = (2 : ℝ) • A := by rw [htwo]
    _ = (2 : ℝ) • ((modularConjugationJ (E := E)).comp (modularSignEpsilon (E := E))) := by
          simp [A]

/--
Canonical supergraded package for the modular CPT atom `⟨1, ε, J, Jε⟩`.
-/
theorem modularCPT_supergraded_lie_package :
    isEven (E := E) (modularConjugationJ (E := E)) ∧
      isOdd (E := E) (modularSignEpsilon (E := E)) ∧
      isOdd (E := E) (modularComplexI (E := E)) ∧
      (modularConjugationJ (E := E)).comp (modularSignEpsilon (E := E))
        + (modularSignEpsilon (E := E)).comp (modularConjugationJ (E := E)) = 0 := by
  exact ⟨modularConjugationJ_isEven (E := E), modularSignEpsilon_isOdd (E := E),
    modularComplexI_isOdd (E := E),
    modularConjugationJ_anticommutator_modularSignEpsilon (E := E)⟩

/--
Canonical positive-time subspace in doubled form:
vectors with matched components `(x, x)`.
-/
def PositiveTimeVector (Ω : DoubledSpace E) : Prop :=
  ∃ x : E, Ω = to_doubled x x

/--
On the canonical positive-time subspace, modular conjugation `J` fixes vectors.
-/
lemma modularConjugationJ_fixed_of_positiveTimeVector
    (Ω : DoubledSpace E)
    (hΩ : PositiveTimeVector (E := E) Ω) :
    modularConjugationJ (E := E) Ω = Ω := by
  rcases hΩ with ⟨x, rfl⟩
  apply DoubledSpace.ext <;> simp [modularConjugationJ, modular_j]

/--
Reflection quadratic form is nonnegative on the canonical positive-time subspace.
-/
theorem reflectionQuadratic_nonneg_of_positiveTimeVector
    (Ω : DoubledSpace E)
    (hΩ : PositiveTimeVector (E := E) Ω) :
    0 ≤ inner ℝ ((modularConjugationJ (E := E)) Ω) Ω := by
  rw [modularConjugationJ_fixed_of_positiveTimeVector (E := E) Ω hΩ]
  exact real_inner_self_nonneg

/--
Canonical split-Clifford representation realized by the modular atom on doubled space.
-/
noncomputable abbrev tomitaRepresentation :
    RoutingSplitCliffordAlg →ₐ[ℝ] (DoubledSpace E →L[ℝ] DoubledSpace E) :=
  cl11Rep (E := E)

@[simp] lemma tomitaRepresentation_cptJ :
    tomitaRepresentation (E := E) cptJ = modularConjugationJ (E := E) := by
  simpa [tomitaRepresentation, cptJ, modularConjugationJ] using
    (cl11Rep_ι_one_zero (E := E))

@[simp] lemma tomitaRepresentation_cptJeps :
    tomitaRepresentation (E := E) cptJeps = modularComplexI (E := E) := by
  simpa [tomitaRepresentation, cptJeps, modularComplexI] using
    (cl11Rep_ι_zero_one (E := E))

@[simp] lemma tomitaRepresentation_cptEps :
    tomitaRepresentation (E := E) cptEps = modularSignEpsilon (E := E) := by
  simpa [tomitaRepresentation, cptEps, cptJ, cptJeps, modularSignEpsilon] using
    (cl11Rep_pseudoscalar (E := E))

end ModularRealization

end InfoGeometry.Canonical.TomitaTakesaki
