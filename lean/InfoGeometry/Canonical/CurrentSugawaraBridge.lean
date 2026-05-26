import InfoGeometry.Canonical.CurrentSugawaraMetricDatum
import InfoGeometry.Canonical.MetricSugawaraBridge
import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.NilpotentFluxVirasoroReadout
import InfoGeometry.External.Virasoro.HeisenbergAlgebra
import InfoGeometry.External.Virasoro.FockSpace

/-!
# Current-to-Sugawara bridge

This file is a narrow adapter from a proved Heisenberg current representation
to the existing external Sugawara/Virasoro construction.

It does not reprove Sugawara and it does not assert a Lichnerowicz square
identity. The only inputs are exactly the inputs required by
`VirasoroProject.sugawaraRepresentation`: current modes, local truncation, and
the Heisenberg commutator.
-/

namespace InfoGeometry.Canonical.CurrentSugawaraBridge

open Filter
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open VirasoroProject
open InfoGeometry.Canonical.CurrentSugawaraMetricDatum
open CurrentMetricDatum

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

/--
The split 8-channel Sugawara signature datum.

This stays separate from the global Krein carrier.  It packages the metric
signature used for the indexed current contraction layer.
-/
noncomputable def splitEightSugawaraSignatureDatum :
    CurrentMetricDatum ℝ (Fin 8) :=
  CurrentMetricDatum.splitEightCurrentMetricDatum

@[simp] theorem splitEightSugawaraSignatureDatum_kappa :
    splitEightSugawaraSignatureDatum.kappa = splitEightKappa := by
  rfl

@[simp] theorem splitEightSugawaraSignatureDatum_kappaInv :
    splitEightSugawaraSignatureDatum.kappaInv = splitEightKappa := by
  rfl

/-- The split 8-channel Sugawara kernel is the finite-channel operator layer. -/
noncomputable def splitEightSugawaraKernel
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (H : CurrentMetricDatum.MetricHeisenbergCurrent ℝ V (Fin 8)) :
    ℤ → V → V :=
  MetricSugawaraBridge.splitEightKernel (V := V) H

@[simp] theorem splitEightSugawaraKernel_def
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (H : CurrentMetricDatum.MetricHeisenbergCurrent ℝ V (Fin 8))
    (n : ℤ) (v : V) :
    splitEightSugawaraKernel (V := V) H n v =
      (2 : ℝ)⁻¹ • ∑ᶠ k, ∑ i : Fin 8, ∑ j : Fin 8,
        H.metric.kappaInv i j • MetricSugawaraBridge.channelPairNO H i j (n - k) k v := by
  rfl

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

@[simp] lemma conjugateEnd_zero
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (U : V ≃ₗ[𝕜] V) :
    conjugateEnd U (0 : V →ₗ[𝕜] V) = 0 := by
  ext v
  simp [conjugateEnd]

@[simp] lemma conjugateEnd_sub
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (U : V ≃ₗ[𝕜] V)
    (A B : V →ₗ[𝕜] V) :
    conjugateEnd U (A - B) =
      conjugateEnd U A - conjugateEnd U B := by
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

/--
Scalar multiples of the identity are central in the endomorphism algebra.

This is the algebraic core needed for Jacobi closure of the Heisenberg
central extension term.
-/
theorem heisenberg_central_term_commutes
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (c : 𝕜) (J : V →ₗ[𝕜] V) :
    (c • (1 : V →ₗ[𝕜] V)) * J - J * (c • (1 : V →ₗ[𝕜] V)) = 0 := by
  ext v
  simp [sub_eq_add_neg]

/--
Commutator form of `heisenberg_central_term_commutes`.
-/
theorem heisenberg_central_term_commutator_eq_zero
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (c : 𝕜) (J : V →ₗ[𝕜] V) :
    (c • (1 : V →ₗ[𝕜] V)).commutator J = 0 := by
  simpa [LinearMap.commutator] using
    heisenberg_central_term_commutes (𝕜 := 𝕜) (V := V) c J

/--
Conjugation by a linear equivalence preserves the endomorphism commutator.
-/
theorem conjugateEnd_commutator
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (U : V ≃ₗ[𝕜] V)
    (A B : V →ₗ[𝕜] V) :
    (conjugateEnd U A).commutator (conjugateEnd U B) =
      conjugateEnd U (A.commutator B) := by
  change
    (conjugateEnd U A) * (conjugateEnd U B) -
        (conjugateEnd U B) * (conjugateEnd U A)
      =
    conjugateEnd U (A * B - B * A)
  rw [conjugateEnd_sub, conjugateEnd_mul, conjugateEnd_mul]

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

/--
The Sugawara central term vanishes on the global conformal modes
`m = -1, 0, 1`.

This is the representation-level version of the identity `m^3 - m = 0`
on the embedded `sl₂` modes.
-/
theorem sugawaraCentralTerm_zero_of_global_mode
    (H : CurrentHeisenbergRep 𝕜 V)
    {m n : Int}
    (hm : m = -1 ∨ m = 0 ∨ m = 1) :
    (if m + n = 0 then
        (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) • (1 : V →ₗ[𝕜] V))
      else
        0) = 0 := by
  rcases hm with hm | hm | hm
  · subst m
    by_cases hmn : (-1 : Int) + n = 0
    · simp [hmn]
      left
      norm_num
    · simp [hmn]
  · subst m
    by_cases hmn : (0 : Int) + n = 0
    · simp [hmn]
    · simp [hmn]
  · subst m
    by_cases hmn : (1 : Int) + n = 0
    · simp [hmn]
    · simp [hmn]

/--
On the global conformal modes `m = -1, 0, 1`, the Sugawara Virasoro bracket
has no central contribution.

This is the concrete `sl₂` subalgebra readout inside the already-developed
infinite-dimensional Virasoro/Sugawara representation.
-/
theorem sugawaraStressMode_virasoroBracket_global_mode
    (H : CurrentHeisenbergRep 𝕜 V)
    {m n : Int}
    (hm : m = -1 ∨ m = 0 ∨ m = 1) :
    ((H.sugawaraStressMode m).commutator
        (H.sugawaraStressMode n)) =
      (m - n) • H.sugawaraStressMode (m + n) := by
  rw [H.sugawaraStressMode_virasoroBracket m n]
  rw [H.sugawaraCentralTerm_zero_of_global_mode hm]
  simp

/-- Scalar central coefficient in the Sugawara Virasoro bracket. -/
def sugawaraCentralScalar (m n : Int) : 𝕜 :=
  if m + n = 0 then ((m ^ 3 - m : 𝕜) / (12 : 𝕜)) else 0

/--
Owner-side readout: the central operator term is exactly the scalar central
coefficient times the identity.
-/
theorem sugawaraCentralTerm_eq_scalar_smul_one
    (m n : Int) :
    (if m + n = 0 then
        (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) • (1 : V →ₗ[𝕜] V))
      else 0)
    = (sugawaraCentralScalar (𝕜 := 𝕜) m n) • (1 : V →ₗ[𝕜] V) := by
  unfold sugawaraCentralScalar
  by_cases hmn : m + n = 0
  · simp [hmn]
  · simp [hmn]

/--
Scalar-level vanishing of the Sugawara central coefficient on global conformal
modes `m = -1, 0, 1`.
-/
theorem sugawaraCentralScalar_zero_of_global_mode
    {m n : Int}
    (hm : m = -1 ∨ m = 0 ∨ m = 1) :
    sugawaraCentralScalar (𝕜 := 𝕜) m n = 0 := by
  unfold sugawaraCentralScalar
  rcases hm with hm | hm | hm
  · subst m
    by_cases hmn : (-1 : Int) + n = 0
    · simp [hmn]
      norm_num
    · simp [hmn]
  · subst m
    by_cases hmn : (0 : Int) + n = 0
    · simp [hmn]
    · simp [hmn]
  · subst m
    by_cases hmn : (1 : Int) + n = 0
    · simp [hmn]
    · simp [hmn]

/--
Concrete bridge readout (real scalars):
the Sugawara central scalar equals the finite nilpotent-flux central
coefficient already proved in the finite seed corridor.
-/
theorem sugawaraCentralScalar_eq_nilpotentFluxCentralCoefficient
    (m n : Int) :
    sugawaraCentralScalar (𝕜 := ℝ) m n =
      InfoGeometry.Canonical.NilpotentFluxVirasoroReadout.nilpotentFluxCentralCoefficient m n := by
  rw [InfoGeometry.Canonical.NilpotentFluxVirasoroReadout.nilpotentFluxCentralCoefficient_eq_virasoro]
  unfold sugawaraCentralScalar
  by_cases hmn : m + n = 0
  · simp [hmn]
  · simp [hmn]

/--
Real-scalar global-mode bridge readout:
the Sugawara central scalar vanishes on `m = -1,0,1` by transport through the
finite nilpotent-flux theorem.
-/
theorem sugawaraCentralScalar_zero_of_global_mode_via_nilpotentFlux
    {m n : Int}
    (hm : m = -1 ∨ m = 0 ∨ m = 1) :
    sugawaraCentralScalar (𝕜 := ℝ) m n = 0 := by
  rw [sugawaraCentralScalar_eq_nilpotentFluxCentralCoefficient]
  exact InfoGeometry.Canonical.NilpotentFluxVirasoroReadout.nilpotentFluxCentralCoefficient_zero_of_global_mode hm

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

/--
The Heisenberg current commutator is invariant under conjugation by a
linear equivalence.
-/
theorem conjugated_current_commutator
    (H : CurrentHeisenbergRep 𝕜 V)
    (U : V ≃ₗ[𝕜] V)
    (m n : Int) :
    (conjugateEnd U (H.J m)).commutator
        (conjugateEnd U (H.J n)) =
      if m + n = 0 then
        (m : 𝕜) • (1 : V →ₗ[𝕜] V)
      else
        0 := by
  rw [conjugateEnd_commutator]
  rw [H.comm m n]
  by_cases hmn : m + n = 0
  · simp [hmn, conjugateEnd_smul, conjugateEnd_one]
  · simp [hmn]

/--
The local truncation condition is invariant under conjugation by a linear
equivalence.
-/
theorem conjugated_current_trunc
    (H : CurrentHeisenbergRep 𝕜 V)
    (U : V ≃ₗ[𝕜] V) :
    ∀ v, atTop.Eventually
      (fun l => conjugateEnd U (H.J l) v = 0) := by
  intro v
  have htrunc := H.trunc (U.symm v)
  exact htrunc.mono (by
    intro l hl
    simp [conjugateEnd, hl])

end CurrentHeisenbergRep

/--
The Heisenberg algebra acts on the charged Fock space through its universal
enveloping algebra representation.

This is the concrete source-side current datum used to package a genuine
`CurrentHeisenbergRep` object from the existing charged Fock module structure.
-/
noncomputable def chargedFockSpaceHeisenbergMode
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (n : Int) :
    VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜] VirasoroProject.ChargedFockSpace 𝕜 α :=
  (UniversalEnvelopingAlgebra.representation
    (𝕜 := 𝕜) (𝓰 := VirasoroProject.HeisenbergAlgebra 𝕜)
    (V := VirasoroProject.ChargedFockSpace 𝕜 α))
    (VirasoroProject.HeisenbergAlgebra.jgen 𝕜 n)

@[simp] theorem chargedFockSpaceHeisenbergMode_apply
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (n : Int)
    (v : VirasoroProject.ChargedFockSpace 𝕜 α) :
    chargedFockSpaceHeisenbergMode 𝕜 α n v =
      ιUEA 𝕜 (VirasoroProject.HeisenbergAlgebra.jgen 𝕜 n) • v := by
  rfl

@[simp] theorem chargedFockSpaceHeisenbergRepresentation_kgen
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (UniversalEnvelopingAlgebra.representation
      (𝕜 := 𝕜) (𝓰 := VirasoroProject.HeisenbergAlgebra 𝕜)
      (V := VirasoroProject.ChargedFockSpace 𝕜 α))
      (VirasoroProject.HeisenbergAlgebra.kgen 𝕜) =
        (1 : VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜] VirasoroProject.ChargedFockSpace 𝕜 α) := by
  ext v
  simpa using (VirasoroProject.ChargedFockSpace.kgen_smul 𝕜 α v)

/--
Package the charged Fock space as a `CurrentHeisenbergRep`.

The current modes are the standard Heisenberg generators acting through the
universal enveloping algebra action on the charged Fock module.
-/
noncomputable def chargedFockSpaceCurrentHeisenbergRep
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    CurrentHeisenbergRep 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α) where
  J := chargedFockSpaceHeisenbergMode 𝕜 α
  trunc := by
    intro v
    filter_upwards [VirasoroProject.ChargedFockSpace.eventually_jgen_smul_eq_zero 𝕜 α v] with
      n hn
    simpa [chargedFockSpaceHeisenbergMode] using hn
  comm := by
    intro m n
    have hbr :=
      LieAlgebra.Representation.apply_bracket_eq_commutator
        (UniversalEnvelopingAlgebra.representation
          (𝕜 := 𝕜) (𝓰 := VirasoroProject.HeisenbergAlgebra 𝕜)
          (V := VirasoroProject.ChargedFockSpace 𝕜 α))
        (VirasoroProject.HeisenbergAlgebra.jgen 𝕜 m)
        (VirasoroProject.HeisenbergAlgebra.jgen 𝕜 n)
    by_cases hmn : m + n = 0
    · simpa [chargedFockSpaceHeisenbergMode,
          VirasoroProject.HeisenbergAlgebra.lie_jgen,
          hmn,
          chargedFockSpaceHeisenbergRepresentation_kgen] using hbr.symm
    · simpa [chargedFockSpaceHeisenbergMode,
          VirasoroProject.HeisenbergAlgebra.lie_jgen,
          hmn] using hbr.symm

/--
Packaged Heisenberg-to-Sugawara morphism.

This is the repository-native object that records the exact bridge already
proved by the current Sugawara owner surface: a Heisenberg current datum, the
associated Virasoro representation, and the two readbacks used downstream
(`cgen ↦ 1`, `lgen n ↦ L_n`).
It does not assert any split-Clifford source construction.
-/
structure CurrentSugawaraMorphism
    (𝕜 V : Type*) [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V] where
  /-- The Heisenberg current datum. -/
  heisenberg : CurrentHeisenbergRep 𝕜 V
  /-- The induced Virasoro representation. -/
  virasoro :
    VirasoroProject.VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ (V →ₗ[𝕜] V)
  /-- `L_n` is the Sugawara stress mode. -/
  lgen_apply :
    ∀ n : Int,
      virasoro (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n) =
        heisenberg.sugawaraStressMode n
  /-- The central Virasoro generator acts as the identity. -/
  central_apply :
    virasoro (VirasoroProject.VirasoroAlgebra.cgen 𝕜) =
      (1 : V →ₗ[𝕜] V)

namespace CurrentSugawaraMorphism

variable {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

/-- The canonical packaged Sugawara morphism induced by a Heisenberg current datum. -/
noncomputable def ofHeisenberg (H : CurrentHeisenbergRep 𝕜 V) :
    CurrentSugawaraMorphism 𝕜 V where
  heisenberg := H
  virasoro := H.currentSugawaraRepresentation
  lgen_apply := by
    intro n
    exact H.currentSugawaraRepresentation_lgen_apply n
  central_apply := H.currentSugawaraRepresentation_central

/-- Every Heisenberg current datum canonically yields a Sugawara morphism package. -/
theorem nonempty (H : CurrentHeisenbergRep 𝕜 V) :
    Nonempty (CurrentSugawaraMorphism 𝕜 V) :=
  ⟨ofHeisenberg H⟩

end CurrentSugawaraMorphism

/-- The charged Fock space canonically yields a current Sugawara morphism package. -/
theorem chargedFockSpace_currentSugawaraMorphism_nonempty
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    Nonempty (CurrentSugawaraMorphism 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α)) :=
  CurrentSugawaraMorphism.nonempty (chargedFockSpaceCurrentHeisenbergRep 𝕜 α)

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
