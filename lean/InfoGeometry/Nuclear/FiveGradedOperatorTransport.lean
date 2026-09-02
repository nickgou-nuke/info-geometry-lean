import InfoGeometry.Nuclear.GradedBathCommutant
import InfoGeometry.OperatorAlgebra.ChiralRetainedWordFiveGradeClosure
import InfoGeometry.OperatorAlgebra.GradeActionInterface

/-! Transport of the associative nuclear five-grading through an algebra
equivalence.  This is the common interface for operator realizations; it does
not identify the separate Freudenthal/TKK carrier with an associative algebra. -/

namespace InfoGeometry.Nuclear.GradedBathCommutant.OperatorFiveGrading

variable {A B : Type*} [Ring A] [Ring B]
variable [Algebra ℝ A] [Algebra ℝ B]

def sector (G : OperatorFiveGrading A) :
    InfoGeometry.OperatorAlgebra.FiveGrade → Submodule ℝ A
  | .negTwo => G.gNegTwo
  | .negOne => G.gNegOne
  | .zero => G.gZero
  | .posOne => G.gPosOne
  | .posTwo => G.gPosTwo

@[simp] theorem sector_negTwo (G : OperatorFiveGrading A) :
    G.sector .negTwo = G.gNegTwo := rfl

@[simp] theorem sector_negOne (G : OperatorFiveGrading A) :
    G.sector .negOne = G.gNegOne := rfl

@[simp] theorem sector_zero (G : OperatorFiveGrading A) :
    G.sector .zero = G.gZero := rfl

@[simp] theorem sector_posOne (G : OperatorFiveGrading A) :
    G.sector .posOne = G.gPosOne := rfl

@[simp] theorem sector_posTwo (G : OperatorFiveGrading A) :
    G.sector .posTwo = G.gPosTwo := rfl

def transport (e : A ≃ₐ[ℝ] B) (G : OperatorFiveGrading A) :
    OperatorFiveGrading B where
  gNegTwo := G.gNegTwo.map e.toLinearMap
  gNegOne := G.gNegOne.map e.toLinearMap
  gZero := G.gZero.map e.toLinearMap
  gPosOne := G.gPosOne.map e.toLinearMap
  gPosTwo := G.gPosTwo.map e.toLinearMap
  negOne_posOne_mem_zero := by
    intro X Y hX hY
    rcases hX with ⟨X', hX', rfl⟩
    rcases hY with ⟨Y', hY', rfl⟩
    refine ⟨opCommutator X' Y', G.negOne_posOne_mem_zero hX' hY', ?_⟩
    simp [opCommutator]

  posOne_posOne_mem_posTwo := by
    intro X Y hX hY
    rcases hX with ⟨X', hX', rfl⟩
    rcases hY with ⟨Y', hY', rfl⟩
    refine ⟨opCommutator X' Y', G.posOne_posOne_mem_posTwo hX' hY', ?_⟩
    simp [opCommutator]
  negOne_negOne_mem_negTwo := by
    intro X Y hX hY
    rcases hX with ⟨X', hX', rfl⟩
    rcases hY with ⟨Y', hY', rfl⟩
    refine ⟨opCommutator X' Y', G.negOne_negOne_mem_negTwo hX' hY', ?_⟩
    simp [opCommutator]
  zero_posOne_mem_posOne := by
    intro X Y hX hY
    rcases hX with ⟨X', hX', rfl⟩
    rcases hY with ⟨Y', hY', rfl⟩
    refine ⟨opCommutator X' Y', G.zero_posOne_mem_posOne hX' hY', ?_⟩
    simp [opCommutator]
  zero_negOne_mem_negOne := by
    intro X Y hX hY
    rcases hX with ⟨X', hX', rfl⟩
    rcases hY with ⟨Y', hY', rfl⟩
    refine ⟨opCommutator X' Y', G.zero_negOne_mem_negOne hX' hY', ?_⟩
    simp [opCommutator]

theorem transport_sector_map (e : A ≃ₐ[ℝ] B) (G : OperatorFiveGrading A)
    (q : InfoGeometry.OperatorAlgebra.FiveGrade) :
    (transport e G).sector q = (G.sector q).map e.toLinearMap := by
  cases q <;> rfl

theorem transport_id (G : OperatorFiveGrading A) :
    transport (AlgEquiv.refl : A ≃ₐ[ℝ] A) G = G := by
  cases G
  have hmap : ∀ S : Submodule ℝ A,
      Submodule.map (AlgEquiv.refl : A ≃ₐ[ℝ] A).toLinearMap S = S := by
    intro S
    apply le_antisymm
    · rintro x ⟨y, hy, hxy⟩
      simpa using hxy ▸ hy
    · intro x hx
      exact ⟨x, hx, by simp⟩
  simp only [transport]
  congr 1 <;> apply hmap

theorem transport_comp
    {C : Type*} [Ring C] [Algebra ℝ C]
    (e₁ : A ≃ₐ[ℝ] B) (e₂ : B ≃ₐ[ℝ] C)
    (G : OperatorFiveGrading A) :
    transport e₂ (transport e₁ G) =
      transport (e₁.trans e₂) G := by
  cases G
  have hmap : ∀ S : Submodule ℝ A,
      Submodule.map e₂.toLinearMap (Submodule.map e₁.toLinearMap S) =
        Submodule.map (e₁.trans e₂).toLinearMap S := by
    intro S
    apply le_antisymm
    · rintro z ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro z ⟨x, hx, rfl⟩
      exact ⟨e₁ x, ⟨x, hx, rfl⟩, rfl⟩
  simp only [transport]
  congr 1 <;> apply hmap

theorem transport_maps_sector_family (e : A ≃ₐ[ℝ] B)
    (G : OperatorFiveGrading A) :
    InfoGeometry.OperatorAlgebra.MapsToGradeBetween
      (fun q => (G.sector q : Set A))
      (fun q => ((transport e G).sector q : Set B))
      (fun _ : Unit => e)
      (fun _ q => q) := by
  intro _ q X hX
  change e X ∈ (transport e G).sector q
  rw [transport_sector_map]
  exact ⟨X, hX, rfl⟩

theorem transport_symm_maps_sector_family (e : A ≃ₐ[ℝ] B)
    (G : OperatorFiveGrading A) :
    InfoGeometry.OperatorAlgebra.MapsToGradeBetween
      (fun q => ((transport e G).sector q : Set B))
      (fun q => (G.sector q : Set A))
      (fun _ : Unit => e.symm)
      (fun _ q => q) := by
  intro _ q Y hY
  change e.symm Y ∈ G.sector q
  change Y ∈ (transport e G).sector q at hY
  rw [transport_sector_map] at hY
  rcases hY with ⟨X, hX, hXY⟩
  have hYX : e.symm Y = X := by
    rw [← hXY]
    exact e.symm_apply_apply X
  simpa [hYX] using hX

theorem transport_sector_image_eq (e : A ≃ₐ[ℝ] B)
    (G : OperatorFiveGrading A)
    (q : InfoGeometry.OperatorAlgebra.FiveGrade) :
    e '' (G.sector q : Set A) =
      ((transport e G).sector q : Set B) := by
  apply InfoGeometry.OperatorAlgebra.linearEquiv_mapsToGradeBetween_image_eq
    e.toLinearEquiv (fun q => (G.sector q : Set A))
    (fun q => ((transport e G).sector q : Set B))
    (fun q => q) (fun q => q)
  · intro q
    exact transport_maps_sector_family e G () q
  · intro q
    exact transport_symm_maps_sector_family e G () q
  · intro q
    rfl

theorem transport_composed_sector_image_eq
    {C : Type*} [Ring C] [Algebra ℝ C]
    (e₁ : A ≃ₐ[ℝ] B) (e₂ : B ≃ₐ[ℝ] C)
    (G : OperatorFiveGrading A)
    (q : InfoGeometry.OperatorAlgebra.FiveGrade) :
    (e₁.trans e₂) '' (G.sector q : Set A) =
      ((transport e₂ (transport e₁ G)).sector q : Set C) := by
  rw [transport_comp]
  exact transport_sector_image_eq (e₁.trans e₂) G q

theorem transport_symm_transport_sector (e : A ≃ₐ[ℝ] B)
    (G : OperatorFiveGrading A)
    (q : InfoGeometry.OperatorAlgebra.FiveGrade) :
    (transport e.symm (transport e G)).sector q = G.sector q := by
  rw [transport_sector_map, transport_sector_map]
  apply le_antisymm
  · rintro _ ⟨Y, ⟨X, hX, rfl⟩, rfl⟩
    simpa using hX
  · rintro X hX
    exact ⟨e X, ⟨X, hX, rfl⟩, by simp⟩

@[simp] theorem transport_gNegTwo (e : A ≃ₐ[ℝ] B) (G : OperatorFiveGrading A) :
    (transport e G).gNegTwo = G.gNegTwo.map e.toLinearMap := rfl

end InfoGeometry.Nuclear.GradedBathCommutant.OperatorFiveGrading
