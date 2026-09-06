import InfoGeometry.Clifford.Lift
import InfoGeometry.Canonical.GrandCanonicalExperts

namespace InfoGeometry.Canonical.TomitaTakesaki

open InfoGeometry.Clifford
open InfoGeometry.Canonical.MoE

/-!
# Tomita-Takesaki Modular Atom (Split `Cl(1,1)`)

This module packages the modular pair (`J`, `ε`) on doubled real space and
connects it to the exact split Clifford algebra used in routing:
`SplitCliffordAlg = CliffordAlgebra splitQ11`.
-/

section CliffordAtom

/-- The split Clifford algebra used by routing modules (`Cl(1,1)`). -/
noncomputable abbrev RoutingSplitCliffordAlg := SplitCliffordAlg

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

lemma cptJ_cptJeps_anticommute :
    cptJ * cptJeps = -(cptJeps * cptJ) := by
  have hpolar : QuadraticMap.polar splitQ11 ((1 : ℝ), 0) ((0 : ℝ), 1) = 0 := by
    simp [QuadraticMap.polar, splitQ11_apply]
  rw [cptJ, cptJeps,
      CliffordAlgebra.ι_mul_ι_comm (Q := splitQ11) (a := ((1 : ℝ), 0)) (b := ((0 : ℝ), 1)),
      hpolar]
  simp

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/--
Modular conjugation `J` (real-linear model of antilinear conjugation on complex space).
-/
abbrev modularConjugationJ : DoubledSpace E →L[ℝ] DoubledSpace E :=
  modularJ (E := E)

/-- Modular sign involution `ε = sgn(K)`. -/
abbrev modularSignEpsilon : DoubledSpace E →L[ℝ] DoubledSpace E :=
  spectralEpsilon (E := E)

/-- Composite `Jε`, the split-complex structure axis. -/
abbrev modularComplexI : DoubledSpace E →L[ℝ] DoubledSpace E :=
  complexI (E := E)

@[simp] lemma modularConjugationJ_sq :
    (modularConjugationJ (E := E)).comp (modularConjugationJ (E := E))
      = ContinuousLinearMap.id ℝ (DoubledSpace E) :=
  modularJ_involution (E := E)

@[simp] lemma modularSignEpsilon_sq :
    (modularSignEpsilon (E := E)).comp (modularSignEpsilon (E := E))
      = ContinuousLinearMap.id ℝ (DoubledSpace E) :=
  spectralEpsilon_involution (E := E)

lemma modularConjugationJ_anticommutes_modularSign :
    (modularConjugationJ (E := E)).comp (modularSignEpsilon (E := E))
      = -((modularSignEpsilon (E := E)).comp (modularConjugationJ (E := E))) :=
  modularJ_spectralEpsilon_anticommute (E := E)

@[simp] lemma modularComplexI_sq :
    (modularComplexI (E := E)).comp (modularComplexI (E := E))
      = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) :=
  complexI_sq (E := E)

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
