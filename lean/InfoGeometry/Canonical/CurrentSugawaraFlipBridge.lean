import InfoGeometry.External.Virasoro.HeisenbergAlgebra

/-!
# Heisenberg orientation flip bridge

This file packages the Heisenberg Lie-flip theorem on top of the involutive
current flip:

* `J_n ↦ J_-n`
* `K ↦ -K`
-/

namespace InfoGeometry.Canonical.CurrentSugawaraFlipBridge

open VirasoroProject
open Module

noncomputable section

variable {𝕜 : Type*} [Field 𝕜]

/-- Index reversal on the abelian current algebra. -/
def currentFlip :
    VirasoroProject.AbelianLieAlgebraOn ℤ 𝕜 ≃ₗ[𝕜] VirasoroProject.AbelianLieAlgebraOn ℤ 𝕜 :=
  Finsupp.mapDomain.linearEquiv (M := 𝕜) (R := 𝕜) (Equiv.neg ℤ)

@[simp] theorem currentFlip_single (i : ℤ) (a : 𝕜) :
    currentFlip (𝕜 := 𝕜) (Finsupp.single i a) = Finsupp.single (-i) a := by
  change Finsupp.mapDomain (Equiv.neg ℤ) (Finsupp.single i a) = _
  simp [Finsupp.mapDomain_single]

@[simp] theorem currentFlip_jgen (n : ℤ) :
    currentFlip (𝕜 := 𝕜) (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 n) =
      VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 (-n) := by
  change Finsupp.mapDomain (Equiv.neg ℤ) (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 n) = _
  simp [VirasoroProject.AbelianLieAlgebraOn.jgen_eq_single]

@[simp] theorem currentFlip_involutive (X : VirasoroProject.AbelianLieAlgebraOn ℤ 𝕜) :
    currentFlip (𝕜 := 𝕜) (currentFlip (𝕜 := 𝕜) X) = X := by
  simpa [currentFlip] using
    (Finsupp.mapDomain_comp (f := Equiv.neg ℤ) (g := Equiv.neg ℤ) (v := X)).symm

/-- The Heisenberg cocycle changes sign on the coefficient-one generators. -/
private theorem heisenbergCocycle_modeFlip_single_one (i j : ℤ) :
    VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin 𝕜
        (currentFlip (𝕜 := 𝕜) (Finsupp.single i (1 : 𝕜)))
        (currentFlip (𝕜 := 𝕜) (Finsupp.single j (1 : 𝕜)))
      =
    - VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin 𝕜
        (Finsupp.single i (1 : 𝕜))
        (Finsupp.single j (1 : 𝕜)) := by
  change VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin 𝕜
      (Finsupp.single (-i) (1 : 𝕜))
      (Finsupp.single (-j) (1 : 𝕜))
    =
    - VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin 𝕜
      (Finsupp.single i (1 : 𝕜))
      (Finsupp.single j (1 : 𝕜))
  by_cases h : i + j = 0
  · have hneg : (-i) + (-j) = 0 := by linarith
    simp [h, hneg]
  · have hneg : (-i) + (-j) ≠ 0 := by
      intro hh
      apply h
      linarith
    simp [h, hneg]

/-- The Heisenberg cocycle changes sign under mode reversal, for arbitrary coefficients. -/
private theorem heisenbergCocycle_modeFlip_single (i j : ℤ) (a b : 𝕜) :
    VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin 𝕜
        (currentFlip (𝕜 := 𝕜) (Finsupp.single i a))
        (currentFlip (𝕜 := 𝕜) (Finsupp.single j b))
      =
    - VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin 𝕜
        (Finsupp.single i a)
        (Finsupp.single j b) := by
  have h1 : Finsupp.single (-i) a = a • Finsupp.single (-i) (1 : 𝕜) := by
    simpa using (Finsupp.smul_single' a (-i) (1 : 𝕜)).symm
  have h2 : Finsupp.single (-j) b = b • Finsupp.single (-j) (1 : 𝕜) := by
    simpa using (Finsupp.smul_single' b (-j) (1 : 𝕜)).symm
  have h3 : Finsupp.single i a = a • Finsupp.single i (1 : 𝕜) := by
    simpa using (Finsupp.smul_single' a i (1 : 𝕜)).symm
  have h4 : Finsupp.single j b = b • Finsupp.single j (1 : 𝕜) := by
    simpa using (Finsupp.smul_single' b j (1 : 𝕜)).symm
  rw [currentFlip_single, currentFlip_single, h1, h2, h3, h4]
  rw [heisenbergCocycle_modeFlip_single_one (𝕜 := 𝕜) i j]
  simp [LinearMap.map_smul, smul_smul, neg_smul]

/-- The Heisenberg cocycle changes sign under mode reversal. -/
lemma heisenbergCocycle_modeFlip
    (X Y : VirasoroProject.AbelianLieAlgebraOn ℤ 𝕜) :
    VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin 𝕜
        (currentFlip (𝕜 := 𝕜) X) (currentFlip (𝕜 := 𝕜) Y) =
      - VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin 𝕜 X Y := by
  refine Finsupp.induction_linear X ?zero ?add ?single
  · simp [currentFlip]
  · intro X1 X2 hx1 hx2
    ext Y
    have h1 := hx1 Y
    have h2 := hx2 Y
    simp [h1, h2, add_comm, add_left_comm, add_assoc]
  · intro i a
    refine Finsupp.induction_linear Y ?zero ?add ?single
    · simp [currentFlip]
    · intro Y1 Y2 hy1 hy2
      have h1 := hy1
      have h2 := hy2
      simp [h1, h2, add_comm, add_left_comm, add_assoc]
    · intro j b
      simpa using heisenbergCocycle_modeFlip_single (𝕜 := 𝕜) i j a b

@[simp]
theorem heisenbergCocycleBilin_modeFlip_jgen
    (m n : ℤ) :
    AbelianLieAlgebraOn.heisenbergCocycleBilin 𝕜
        (currentFlip (𝕜 := 𝕜) (AbelianLieAlgebraOn.jgen 𝕜 m))
        (currentFlip (𝕜 := 𝕜) (AbelianLieAlgebraOn.jgen 𝕜 n))
      =
    - AbelianLieAlgebraOn.heisenbergCocycleBilin 𝕜
        (AbelianLieAlgebraOn.jgen 𝕜 m)
        (AbelianLieAlgebraOn.jgen 𝕜 n) := by
  simpa using heisenbergCocycle_modeFlip (𝕜 := 𝕜)
    (AbelianLieAlgebraOn.jgen 𝕜 m)
    (AbelianLieAlgebraOn.jgen 𝕜 n)

/--
Orientation reversal on the centrally extended Heisenberg algebra.

It flips modes and also flips the central generator:
`Jₙ ↦ J₋ₙ`, `K ↦ -K`.
-/
noncomputable def heisenbergModeFlip
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] :
    VirasoroProject.HeisenbergAlgebra 𝕜 ≃ₗ⁅𝕜⁆ VirasoroProject.HeisenbergAlgebra 𝕜 := by
  refine
    { toFun := fun X => ⟨currentFlip (𝕜 := 𝕜) X.fst, -X.snd⟩
      invFun := fun X => ⟨currentFlip (𝕜 := 𝕜) X.fst, -X.snd⟩
      map_add' := by
        intro X Y
        apply VirasoroProject.HeisenbergAlgebra.ext'
        · simp [currentFlip]
        · simp [currentFlip, add_comm, add_left_comm, add_assoc]
      map_smul' := by
        intro c X
        apply VirasoroProject.HeisenbergAlgebra.ext'
        · simp [currentFlip]
        · simp [currentFlip]
      left_inv := by
        intro X
        apply VirasoroProject.HeisenbergAlgebra.ext'
        · simp [currentFlip_involutive]
        · simp [currentFlip_involutive]
      right_inv := by
        intro X
        apply VirasoroProject.HeisenbergAlgebra.ext'
        · simp [currentFlip_involutive]
        · simp [currentFlip_involutive]
      map_lie' := by
        intro X Y
        apply VirasoroProject.HeisenbergAlgebra.ext'
        · simp [VirasoroProject.HeisenbergAlgebra.bracket_fst]
        · simp [VirasoroProject.HeisenbergAlgebra.bracket_snd, heisenbergCocycle_modeFlip] }

@[simp]
theorem heisenbergModeFlip_jgen
    (n : ℤ) :
    heisenbergModeFlip 𝕜 (HeisenbergAlgebra.jgen 𝕜 n)
      =
    HeisenbergAlgebra.jgen 𝕜 (-n) := by
  apply VirasoroProject.HeisenbergAlgebra.ext'
  · simp [heisenbergModeFlip, HeisenbergAlgebra.jgen_eq', currentFlip_jgen]
  · simp [heisenbergModeFlip, HeisenbergAlgebra.jgen_eq']

@[simp]
theorem heisenbergModeFlip_kgen :
    heisenbergModeFlip 𝕜 (HeisenbergAlgebra.kgen 𝕜)
      =
    - HeisenbergAlgebra.kgen 𝕜 := by
  apply VirasoroProject.HeisenbergAlgebra.ext'
  · simp [heisenbergModeFlip, HeisenbergAlgebra.kgen_eq']
  · simp [heisenbergModeFlip, HeisenbergAlgebra.kgen_eq']

@[simp]
theorem heisenbergModeFlip_involutive
    (X : HeisenbergAlgebra 𝕜) :
    heisenbergModeFlip 𝕜 (heisenbergModeFlip 𝕜 X) = X := by
  apply VirasoroProject.HeisenbergAlgebra.ext'
  · simp [heisenbergModeFlip, currentFlip_involutive]
  · simp [heisenbergModeFlip, currentFlip_involutive]

end InfoGeometry.Canonical.CurrentSugawaraFlipBridge

end VirasoroProject
