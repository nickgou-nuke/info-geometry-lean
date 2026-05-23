import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.External.Virasoro.HeisenbergAlgebra

/-!
# Current-to-Sugawara bridge

This file is a narrow adapter from a proved Heisenberg current representation
to the existing external Sugawara/Virasoro construction.

It does not reprove Sugawara and it does not assert a Lichnerowicz square
identity.  The only inputs are exactly the inputs required by
`VirasoroProject.sugawaraRepresentation`: current modes, local truncation, and
the Heisenberg commutator.
-/

namespace InfoGeometry.Canonical.CurrentSugawaraBridge

open Filter
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open VirasoroProject

/-- Index reversal on the abelian current algebra. -/
noncomputable def currentFlip
    {𝕜 : Type*} [Field 𝕜] :
    VirasoroProject.AbelianLieAlgebraOn ℤ 𝕜 ≃ₗ[𝕜] VirasoroProject.AbelianLieAlgebraOn ℤ 𝕜 :=
  Finsupp.mapDomain.linearEquiv (M := 𝕜) (R := 𝕜) (Equiv.neg ℤ)

@[simp] lemma currentFlip_jgen
    {𝕜 : Type*} [Field 𝕜] (n : ℤ) :
    currentFlip (𝕜 := 𝕜) (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 n) =
      VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 (-n) := by
  simpa [currentFlip, VirasoroProject.AbelianLieAlgebraOn.jgen_eq_single] using
    (Finsupp.mapDomain_single (f := Equiv.neg ℤ) (a := n) (b := (1 : 𝕜)))

@[simp] lemma currentFlip_zero
    {𝕜 : Type*} [Field 𝕜] :
    currentFlip (𝕜 := 𝕜) (0 : VirasoroProject.AbelianLieAlgebraOn ℤ 𝕜) = 0 := by
  simp [currentFlip]

@[simp] lemma currentFlip_add
    {𝕜 : Type*} [Field 𝕜]
    (X Y : VirasoroProject.AbelianLieAlgebraOn ℤ 𝕜) :
    currentFlip (𝕜 := 𝕜) (X + Y) = currentFlip (𝕜 := 𝕜) X + currentFlip (𝕜 := 𝕜) Y := by
  simp [currentFlip]

@[simp] lemma currentFlip_single
    {𝕜 : Type*} [Field 𝕜] (i : ℤ) (a : 𝕜) :
    currentFlip (𝕜 := 𝕜) (Finsupp.single i a) = Finsupp.single (-i) a := by
  simpa [currentFlip] using
    (Finsupp.mapDomain_single (f := Equiv.neg ℤ) (a := i) (b := a))

@[simp] lemma currentFlip_involutive
    {𝕜 : Type*} [Field 𝕜] (X : VirasoroProject.AbelianLieAlgebraOn ℤ 𝕜) :
    currentFlip (𝕜 := 𝕜) (currentFlip (𝕜 := 𝕜) X) = X := by
  rw [currentFlip, currentFlip, Finsupp.mapDomain_comp]
  simp [currentFlip]

/-- Algebraic conjugation on endomorphisms by a linear equivalence. -/
noncomputable def conjugateEnd
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (U : V ≃ₗ[𝕜] V) (A : V →ₗ[𝕜] V) : V →ₗ[𝕜] V :=
  U.toLinearMap.comp (A.comp U.symm.toLinearMap)

@[simp] lemma conjugateEnd_add
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (U : V ≃ₗ[𝕜] V) (A B : V →ₗ[𝕜] V) :
    conjugateEnd U (A + B) = conjugateEnd U A + conjugateEnd U B := by
  ext v
  simp [conjugateEnd]

@[simp] lemma conjugateEnd_mul
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (U : V ≃ₗ[𝕜] V) (A B : V →ₗ[𝕜] V) :
    conjugateEnd U (A * B) = conjugateEnd U A * conjugateEnd U B := by
  ext v
  simp [conjugateEnd]

@[simp] lemma conjugateEnd_comp
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (U : V ≃ₗ[𝕜] V) (A B : V →ₗ[𝕜] V) :
    conjugateEnd U (A ∘ₗ B) = conjugateEnd U A ∘ₗ conjugateEnd U B := by
  ext v
  simp [conjugateEnd]

@[simp] lemma conjugateEnd_smul
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (U : V ≃ₗ[𝕜] V) (a : 𝕜) (A : V →ₗ[𝕜] V) :
    conjugateEnd U (a • A) = a • conjugateEnd U A := by
  ext v
  simp [conjugateEnd]

@[simp] lemma conjugateEnd_one
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (U : V ≃ₗ[𝕜] V) :
    conjugateEnd U (1 : V →ₗ[𝕜] V) = 1 := by
  ext v
  simp [conjugateEnd]

/-- The Heisenberg cocycle picks up a minus sign under mode reversal. -/
theorem heisenbergCocycleBilin_modeFlip
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    (X Y : VirasoroProject.AbelianLieAlgebraOn ℤ 𝕜) :
    VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin 𝕜
        (currentFlip (𝕜 := 𝕜) X)
        (currentFlip (𝕜 := 𝕜) Y)
      =
    - VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin 𝕜 X Y := by
  induction X using Finsupp.induction_linear with
  | zero =>
      simp
  | add X₁ X₂ hX₁ hX₂ =>
      simp [hX₁, hX₂]
  | single i a =>
      induction Y using Finsupp.induction_linear with
      | zero =>
          simp
      | add Y₁ Y₂ hY₁ hY₂ =>
          simp [hY₁, hY₂]
      | single j b =>
          simp [currentFlip_single, VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin_apply_jgen_jgen]
          by_cases h : i + j = 0
          · have h' : (-i) + (-j) = 0 := by linarith
            simp [h, h']
          · have h' : (-i) + (-j) ≠ 0 := by
              intro hh
              apply h
              linarith
            simp [h, h']

/-- The Heisenberg algebra mode flip sends `J_n ↦ J_-n` and `K ↦ -K`. -/
noncomputable def heisenbergModeFlip
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] :
    VirasoroProject.HeisenbergAlgebra 𝕜 ≃ₗ[𝕜] VirasoroProject.HeisenbergAlgebra 𝕜 where
  toFun X := ⟨currentFlip (𝕜 := 𝕜) X.fst, -X.snd⟩
  map_add' X Y := by
    apply VirasoroProject.HeisenbergAlgebra.ext'
    · simp [currentFlip]
    · abel
  map_smul' c X := by
    apply VirasoroProject.HeisenbergAlgebra.ext'
    · simp [currentFlip]
    · ring
  invFun X := ⟨currentFlip (𝕜 := 𝕜) X.fst, -X.snd⟩
  left_inv := by
    intro X
    apply VirasoroProject.HeisenbergAlgebra.ext'
    · simpa [currentFlip] using (currentFlip_involutive (𝕜 := 𝕜) X.fst)
    · ring
  right_inv := by
    intro X
    apply VirasoroProject.HeisenbergAlgebra.ext'
    · simpa [currentFlip] using (currentFlip_involutive (𝕜 := 𝕜) X.fst)
    · ring

/-- The mode flip is a Lie algebra automorphism of the Heisenberg extension. -/
theorem heisenbergModeFlip_map_lie
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    (X Y : VirasoroProject.HeisenbergAlgebra 𝕜) :
    ⁅heisenbergModeFlip (𝕜 := 𝕜) X, heisenbergModeFlip (𝕜 := 𝕜) Y⁆ =
      heisenbergModeFlip (𝕜 := 𝕜) ⁅X, Y⁆ := by
  apply VirasoroProject.HeisenbergAlgebra.ext'
  · simp [VirasoroProject.HeisenbergAlgebra.bracket_def']
  · simp [VirasoroProject.HeisenbergAlgebra.bracket_def',
      heisenbergCocycleBilin_modeFlip]

/--
The exact current-representation interface required by the external Sugawara
construction.
-/
structure CurrentHeisenbergRep
    (𝕜 V : Type*) [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V] where
  /-- Heisenberg current modes. -/
  J : Int → V →ₗ[𝕜] V
  /-- Local truncation required for the Sugawara finite-support sums. -/
  trunc : ∀ v, atTop.Eventually (fun l => J l v = 0)
  /-- Heisenberg commutator law. -/
  comm :
    ∀ m n,
      (J m).commutator (J n) =
        if m + n = 0 then (m : 𝕜) • (1 : V →ₗ[𝕜] V) else 0

namespace CurrentHeisenbergRep

variable {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

/-- Sugawara stress-energy mode `L_n` attached to a current representation. -/
noncomputable def sugawaraStressMode
    (H : CurrentHeisenbergRep 𝕜 V) (n : Int) : V →ₗ[𝕜] V :=
  VirasoroProject.sugawaraGen (heiOper := H.J) H.trunc n

/-- The Sugawara stress mode is the explicit normal-ordered `pairNO` sum. -/
theorem sugawaraStressMode_eq_pairNO
    (H : CurrentHeisenbergRep 𝕜 V) (n : Int) (v : V) :
    H.sugawaraStressMode n v =
      (2 : 𝕜)⁻¹ • ∑ᶠ k, pairNO H.J (n - k) k v := by
  rw [sugawaraStressMode]
  simpa using (VirasoroProject.sugawaraGen_apply (heiOper := H.J) H.trunc n v)

/--
The external Sugawara/Virasoro representation generated by the current modes.
-/
noncomputable def currentSugawaraRepresentation
    (H : CurrentHeisenbergRep 𝕜 V) :
    VirasoroProject.VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ (V →ₗ[𝕜] V) :=
  sugawaraVirasoroRepresentation_from_heisenbergCurrent H.J H.trunc H.comm

/--
The Sugawara stress modes satisfy the Virasoro bracket with central charge
`c = 1`.
-/
theorem sugawaraStressMode_virasoroBracket
    (H : CurrentHeisenbergRep 𝕜 V) (m n : Int) :
    (H.sugawaraStressMode m).commutator (H.sugawaraStressMode n) =
      (m - n) • H.sugawaraStressMode (m + n)
        + if m + n = 0 then
            (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) • (1 : V →ₗ[𝕜] V))
          else 0 :=
  sugawaraVirasoro_from_heisenbergCurrent H.J H.trunc H.comm m n

/-- In the current Sugawara representation, the Virasoro central generator acts as identity. -/
theorem currentSugawaraRepresentation_central
    (H : CurrentHeisenbergRep 𝕜 V) :
    H.currentSugawaraRepresentation (VirasoroProject.VirasoroAlgebra.cgen 𝕜) =
      (1 : V →ₗ[𝕜] V) :=
  sugawaraVirasoroRepresentation_central_from_heisenbergCurrent H.J H.trunc H.comm

/-- The Virasoro `lgen` action is the Sugawara stress mode. -/
theorem currentSugawaraRepresentation_lgen_apply
    (H : CurrentHeisenbergRep 𝕜 V) (n : Int) :
    H.currentSugawaraRepresentation (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n) =
      H.sugawaraStressMode n := by
  ext v
  rw [currentSugawaraRepresentation, sugawaraStressMode]
  simpa [VirasoroProject.sugawaraGen_apply] using
    (VirasoroProject.sugawaraRepresentation_lgen_apply'
      (heiOper := H.J) H.trunc H.comm n v)

/-- The central Virasoro readout remains fixed under conjugation. -/
theorem currentSugawaraRepresentation_cgen_conjugate
    (H : CurrentHeisenbergRep 𝕜 V) (U : V ≃ₗ[𝕜] V) :
    conjugateEnd U
        (H.currentSugawaraRepresentation (VirasoroProject.VirasoroAlgebra.cgen 𝕜)) =
      (1 : V →ₗ[𝕜] V) := by
  rw [currentSugawaraRepresentation_central]
  simp

end CurrentHeisenbergRep

/--
Semantic adapter for the quantum Ricci scalar on the raw CAR mode algebra.

This exposes the Heisenberg central term safely without asserting a false
Lichnerowicz `J_m^2` identity, respecting the Sugawara owner theorem boundary.
-/
def quantumRicciScalar {A : Type*} [Ring A] (C : RawCARModeAlgebra A) : A :=
  completedCentral C

/-- The Heisenberg central term is exposed as the quantum Ricci scalar. -/
theorem heisenberg_central_term_is_quantumRicciScalar
    {A : Type*} [Ring A] (C : RawCARModeAlgebra A) :
    completedCentral C = quantumRicciScalar C := by
  rfl

end InfoGeometry.Canonical.CurrentSugawaraBridge
