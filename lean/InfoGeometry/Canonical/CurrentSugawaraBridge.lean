/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CurrentSugawaraMetricDatum
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.MetricSugawaraBridge
import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.NilpotentFluxVirasoroReadout
import InfoGeometry.External.Virasoro.HeisenbergAlgebra
import InfoGeometry.External.Virasoro.FockSpace

/-!
# Current-to-Sugawara Virasoro Bridge

This module connects any Heisenberg current representation (`CurrentHeisenbergRep`)
to the normal-ordered Sugawara stress-energy modes and the resulting $c = 1$
Virasoro Lie algebra representation (`currentSugawaraRepresentation`).

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `VirasoroProject.sugawaraGen`, `VirasoroProject.sugawaraRepresentation`,
    `VirasoroProject.ChargedFockSpace`.
  * `InfoGeometry.Canonical.BosonizationConstructiveCurrent`:
    `sugawaraVirasoroRepresentation_from_heisenbergCurrent`,
    `sugawaraVirasoro_from_heisenbergCurrent`,
    `sugawaraVirasoroRepresentation_central_from_heisenbergCurrent`.
- BUCKET 2 (Deconfabulation):
  * Replaced the `CurrentHeisenbergRep` and `CurrentSugawaraMorphism` wrapper
    `structure`s with dependent product carriers and explicit projection functions,
    and eliminated all `:= rfl` wrapper lemmas.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `conjugateEnd` and its ring/commutator homomorphism theorems.
  * `heisenberg_central_term_commutes`, `heisenberg_central_term_commutator_eq_zero`.
  * `CurrentHeisenbergRep`: `sugawaraStressMode`, `sugawaraStressMode_eq_pairNO`,
    `currentSugawaraRepresentation`, `sugawaraStressMode_virasoroBracket`,
    `sugawaraCentralTerm_zero_of_global_mode`, `sugawaraStressMode_virasoroBracket_global_mode`,
    `currentSugawaraRepresentation_central`, `currentSugawaraRepresentation_lgen_apply`,
    `conjugated_current_commutator`, `conjugated_current_trunc`.
  * `chargedFockSpaceHeisenbergMode`, `chargedFockSpaceHeisenbergRepresentation_kgen`,
    `chargedFockSpaceCurrentHeisenbergRep`.
  * `CurrentSugawaraMorphism`, `CurrentSugawaraMorphism.ofHeisenberg`,
    `CurrentSugawaraMorphism.ofHeisenberg_readout`,
    `chargedFockSpace_currentSugawaraMorphism_readout`.
-/

namespace InfoGeometry.Canonical.CurrentSugawaraBridge

open Filter
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open VirasoroProject
open InfoGeometry.Canonical.CurrentSugawaraMetricDatum
open CurrentMetricDatum

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Algebraic conjugation on endomorphisms by a linear equivalence $U : V \simeq_𝕜 V$. -/
noncomputable def conjugateEnd
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (U : V ≃ₗ[𝕜] V) (A : V →ₗ[𝕜] V) : V →ₗ[𝕜] V :=
  U.toLinearMap.comp (A.comp U.symm.toLinearMap)

/-- Conjugation by a linear equivalence distributes over addition of endomorphisms. -/
@[simp] lemma conjugateEnd_add
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (U : V ≃ₗ[𝕜] V) (A B : V →ₗ[𝕜] V) :
    conjugateEnd U (A + B) = conjugateEnd U A + conjugateEnd U B := by
  ext v
  simp [conjugateEnd]

/-- The split 8-channel Sugawara signature datum. -/
noncomputable def splitEightSugawaraSignatureDatum :
    CurrentMetricDatum ℝ (Fin 8) :=
  CurrentMetricDatum.splitEightCurrentMetricDatum

/-- The split 8-channel Sugawara normal-ordered kernel. -/
noncomputable def splitEightSugawaraKernel
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (H : CurrentMetricDatum.MetricHeisenbergCurrent ℝ V (Fin 8)) :
    ℤ → V → V :=
  MetricSugawaraBridge.splitEightKernel (V := V) H

/-- Conjugation by a linear equivalence preserves endomorphism multiplication. -/
@[simp] lemma conjugateEnd_mul
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (U : V ≃ₗ[𝕜] V) (A B : V →ₗ[𝕜] V) :
    conjugateEnd U (A * B) = conjugateEnd U A * conjugateEnd U B := by
  ext v
  simp [conjugateEnd]

/-- Conjugation by a linear equivalence preserves linear-map composition. -/
@[simp] lemma conjugateEnd_comp
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (U : V ≃ₗ[𝕜] V) (A B : V →ₗ[𝕜] V) :
    conjugateEnd U (A ∘ₗ B) = conjugateEnd U A ∘ₗ conjugateEnd U B := by
  ext v
  simp [conjugateEnd]

/-- Conjugation by a linear equivalence maps the zero endomorphism to zero. -/
@[simp] lemma conjugateEnd_zero
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (U : V ≃ₗ[𝕜] V) :
    conjugateEnd U (0 : V →ₗ[𝕜] V) = 0 := by
  ext v
  simp [conjugateEnd]

/-- Conjugation by a linear equivalence distributes over subtraction of endomorphisms. -/
@[simp] lemma conjugateEnd_sub
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (U : V ≃ₗ[𝕜] V)
    (A B : V →ₗ[𝕜] V) :
    conjugateEnd U (A - B) =
      conjugateEnd U A - conjugateEnd U B := by
  ext v
  simp [conjugateEnd]

/-- Conjugation by a linear equivalence commutes with scalar multiplication. -/
@[simp] lemma conjugateEnd_smul
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (U : V ≃ₗ[𝕜] V) (a : 𝕜) (A : V →ₗ[𝕜] V) :
    conjugateEnd U (a • A) = a • conjugateEnd U A := by
  ext v
  simp [conjugateEnd]

/-- Conjugation by a linear equivalence fixes the identity endomorphism. -/
@[simp] lemma conjugateEnd_one
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (U : V ≃ₗ[𝕜] V) :
    conjugateEnd U (1 : V →ₗ[𝕜] V) = 1 := by
  ext v
  simp [conjugateEnd]

/-- Scalar multiples of the identity are central in the endomorphism algebra. -/
theorem heisenberg_central_term_commutes
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (c : 𝕜) (J : V →ₗ[𝕜] V) :
    (c • (1 : V →ₗ[𝕜] V)) * J - J * (c • (1 : V →ₗ[𝕜] V)) = 0 := by
  ext v
  simp

/-- Commutator form of `heisenberg_central_term_commutes`: $[c\cdot 1, J] = 0$. -/
theorem heisenberg_central_term_commutator_eq_zero
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (c : 𝕜) (J : V →ₗ[𝕜] V) :
    (c • (1 : V →ₗ[𝕜] V)).commutator J = 0 := by
  change (c • (1 : V →ₗ[𝕜] V)) * J - J * (c • (1 : V →ₗ[𝕜] V)) = 0
  exact heisenberg_central_term_commutes (𝕜 := 𝕜) (V := V) c J

/-- Conjugation by a linear equivalence preserves the endomorphism commutator. -/
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

/-- The Heisenberg current-representation carrier required by the Sugawara construction:
a mode family `J : ℤ → V →ₗ[𝕜] V` paired with its local truncation and Heisenberg
commutator certificates. -/
def CurrentHeisenbergRep
    (𝕜 V : Type*) [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V] : Type _ :=
  Σ J : Int → V →ₗ[𝕜] V,
    PLift ((∀ v, atTop.Eventually (fun l => J l v = 0)) ∧
      (∀ m n, (J m).commutator (J n) =
        if m + n = 0 then (m : 𝕜) • (1 : V →ₗ[𝕜] V) else 0))

namespace CurrentHeisenbergRep

variable {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

/-- Construct a `CurrentHeisenbergRep` from a mode family `J`, local truncation `trunc`,
and Heisenberg commutator law `comm`. -/
def mk
    (J : Int → V →ₗ[𝕜] V)
    (trunc : ∀ v, atTop.Eventually (fun l => J l v = 0))
    (comm : ∀ m n, (J m).commutator (J n) =
      if m + n = 0 then (m : 𝕜) • (1 : V →ₗ[𝕜] V) else 0) :
    CurrentHeisenbergRep 𝕜 V :=
  ⟨J, PLift.up ⟨trunc, comm⟩⟩

/-- Heisenberg current modes of a `CurrentHeisenbergRep`. -/
def J (H : CurrentHeisenbergRep 𝕜 V) : Int → V →ₗ[𝕜] V :=
  H.1

/-- Local truncation law of a `CurrentHeisenbergRep`. -/
theorem trunc (H : CurrentHeisenbergRep 𝕜 V) :
    ∀ v, atTop.Eventually (fun l => H.J l v = 0) := by
  unfold J
  exact H.2.down.1

/-- Heisenberg commutator law of a `CurrentHeisenbergRep`. -/
theorem comm (H : CurrentHeisenbergRep 𝕜 V) :
    ∀ m n, (H.J m).commutator (H.J n) =
      if m + n = 0 then (m : 𝕜) • (1 : V →ₗ[𝕜] V) else 0 := by
  unfold J
  exact H.2.down.2

/-- Sugawara stress-energy mode `L_n` attached to a current representation. -/
noncomputable def sugawaraStressMode
    (H : CurrentHeisenbergRep 𝕜 V) (n : Int) : V →ₗ[𝕜] V :=
  VirasoroProject.sugawaraGen (heiOper := H.J) H.trunc n

/-- The Sugawara stress mode evaluates to the normal-ordered `pairNO` sum. -/
theorem sugawaraStressMode_eq_pairNO
    (H : CurrentHeisenbergRep 𝕜 V) (n : Int) (v : V) :
    H.sugawaraStressMode n v =
      (2 : 𝕜)⁻¹ • ∑ᶠ k, pairNO H.J (n - k) k v := by
  rw [sugawaraStressMode]
  exact VirasoroProject.sugawaraGen_apply (heiOper := H.J) H.trunc n v

/-- The Sugawara/Virasoro Lie algebra representation generated by the current modes. -/
noncomputable def currentSugawaraRepresentation
    (H : CurrentHeisenbergRep 𝕜 V) :
    VirasoroProject.VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ (V →ₗ[𝕜] V) :=
  sugawaraVirasoroRepresentation_from_heisenbergCurrent H.J H.trunc H.comm

/-- The Sugawara stress modes satisfy the Virasoro bracket with central charge $c = 1$. -/
theorem sugawaraStressMode_virasoroBracket
    (H : CurrentHeisenbergRep 𝕜 V) (m n : Int) :
    (H.sugawaraStressMode m).commutator (H.sugawaraStressMode n) =
      (m - n) • H.sugawaraStressMode (m + n)
        + if m + n = 0 then
            (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) • (1 : V →ₗ[𝕜] V))
          else 0 := by
  unfold sugawaraStressMode
  exact sugawaraVirasoro_from_heisenbergCurrent H.J H.trunc H.comm m n

/-- The Sugawara central term vanishes on the global conformal $\mathfrak{sl}_2$ modes
$m \in \{-1, 0, 1\}$. -/
theorem sugawaraCentralTerm_zero_of_global_mode
    (H : CurrentHeisenbergRep 𝕜 V)
    {m n : Int}
    (hm : m = -1 ∨ m = 0 ∨ m = 1) :
    (if m + n = 0 then
        (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) • (1 : V →ₗ[𝕜] V))
      else
        0) = 0 := by
  have _ := H
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
    · simp
  · subst m
    by_cases hmn : (1 : Int) + n = 0
    · simp [hmn]
    · simp [hmn]

/-- On the global conformal modes $m \in \{-1, 0, 1\}$, the Sugawara Virasoro bracket
reduces to the centerless Witt/$\mathfrak{sl}_2$ commutator $(m - n) L_{m+n}$. -/
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

/-- Scalar central coefficient $(m^3 - m) / 12 \cdot \delta_{m+n,0}$ in the Sugawara Virasoro bracket. -/
def sugawaraCentralScalar (m n : Int) : 𝕜 :=
  if m + n = 0 then ((m ^ 3 - m : 𝕜) / (12 : 𝕜)) else 0

/-- The central operator term in the Sugawara Virasoro bracket equals
`sugawaraCentralScalar m n • 1`. -/
theorem sugawaraCentralTerm_eq_scalar_smul_one
    (m n : Int) :
    (if m + n = 0 then
        (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) • (1 : V →ₗ[𝕜] V))
      else 0)
    = (sugawaraCentralScalar (𝕜 := 𝕜) m n) • (1 : V →ₗ[𝕜] V) := by
  have _ := ‹CharZero 𝕜›
  unfold sugawaraCentralScalar
  by_cases hmn : m + n = 0
  · simp [hmn]
  · simp [hmn]

/-- Scalar-level vanishing of `sugawaraCentralScalar` on the global conformal modes
$m \in \{-1, 0, 1\}$. -/
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
    · simp
  · subst m
    by_cases hmn : (1 : Int) + n = 0
    · simp [hmn]
    · simp [hmn]

/-- Over $\mathbb{R}$, `sugawaraCentralScalar` equals `nilpotentFluxCentralCoefficient`. -/
theorem sugawaraCentralScalar_eq_nilpotentFluxCentralCoefficient
    (m n : Int) :
    sugawaraCentralScalar (𝕜 := ℝ) m n =
      InfoGeometry.Canonical.NilpotentFluxVirasoroReadout.nilpotentFluxCentralCoefficient m n := by
  rw [InfoGeometry.Canonical.NilpotentFluxVirasoroReadout.nilpotentFluxCentralCoefficient_eq_virasoro]
  unfold sugawaraCentralScalar
  by_cases hmn : m + n = 0
  · simp [hmn]
  · simp [hmn]

/-- Real-scalar global-mode vanishing of `sugawaraCentralScalar` via the nilpotent-flux theorem. -/
theorem sugawaraCentralScalar_zero_of_global_mode_via_nilpotentFlux
    {m n : Int}
    (hm : m = -1 ∨ m = 0 ∨ m = 1) :
    sugawaraCentralScalar (𝕜 := ℝ) m n = 0 := by
  rw [sugawaraCentralScalar_eq_nilpotentFluxCentralCoefficient]
  exact InfoGeometry.Canonical.NilpotentFluxVirasoroReadout.nilpotentFluxCentralCoefficient_zero_of_global_mode hm

/-- In the current Sugawara representation, the Virasoro central generator `cgen 𝕜`
acts as the identity endomorphism. -/
theorem currentSugawaraRepresentation_central
    (H : CurrentHeisenbergRep 𝕜 V) :
    H.currentSugawaraRepresentation (VirasoroProject.VirasoroAlgebra.cgen 𝕜) =
      (1 : V →ₗ[𝕜] V) := by
  unfold currentSugawaraRepresentation
  exact sugawaraVirasoroRepresentation_central_from_heisenbergCurrent H.J H.trunc H.comm

/-- The Virasoro generator `lgen 𝕜 n` acts as the Sugawara stress mode `H.sugawaraStressMode n`. -/
theorem currentSugawaraRepresentation_lgen_apply
    (H : CurrentHeisenbergRep 𝕜 V) (n : Int) :
    H.currentSugawaraRepresentation (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n) =
      H.sugawaraStressMode n := by
  ext v
  change VirasoroProject.sugawaraRepresentation
      (heiOper := H.J) H.trunc H.comm
      (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n) v =
    VirasoroProject.sugawaraGen (heiOper := H.J) H.trunc n v
  rw [VirasoroProject.sugawaraRepresentation_lgen_apply']
  exact Eq.refl _

/-- The central Virasoro generator action remains the identity under conjugation by $U$. -/
theorem currentSugawaraRepresentation_cgen_conjugate
    (H : CurrentHeisenbergRep 𝕜 V) (U : V ≃ₗ[𝕜] V) :
    conjugateEnd U
        (H.currentSugawaraRepresentation (VirasoroProject.VirasoroAlgebra.cgen 𝕜)) =
      (1 : V →ₗ[𝕜] V) := by
  rw [currentSugawaraRepresentation_central, conjugateEnd_one]

/-- The Heisenberg current commutator is invariant under conjugation by $U : V \simeq_𝕜 V$. -/
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

/-- The local truncation condition is invariant under conjugation by $U : V \simeq_𝕜 V$. -/
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

/-- The Heisenberg mode operator $J_n$ acting on `ChargedFockSpace 𝕜 α` through its
universal enveloping algebra representation. -/
noncomputable def chargedFockSpaceHeisenbergMode
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) (n : Int) :
    ModuleOfModuleAlgebra 𝕜 (𝓤 𝕜 (VirasoroProject.HeisenbergAlgebra 𝕜))
      (VirasoroProject.ChargedFockSpace 𝕜 α) →ₗ[𝕜]
    ModuleOfModuleAlgebra 𝕜 (𝓤 𝕜 (VirasoroProject.HeisenbergAlgebra 𝕜))
      (VirasoroProject.ChargedFockSpace 𝕜 α) :=
  (UniversalEnvelopingAlgebra.representation
    (𝕜 := 𝕜) (𝓰 := VirasoroProject.HeisenbergAlgebra 𝕜)
    (V := VirasoroProject.ChargedFockSpace 𝕜 α))
    (VirasoroProject.HeisenbergAlgebra.jgen 𝕜 n)

/-- On `ChargedFockSpace 𝕜 α`, the central Heisenberg generator `kgen 𝕜` acts as the
identity endomorphism. -/
@[simp] theorem chargedFockSpaceHeisenbergRepresentation_kgen
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    (UniversalEnvelopingAlgebra.representation
      (𝕜 := 𝕜) (𝓰 := VirasoroProject.HeisenbergAlgebra 𝕜)
      (V := VirasoroProject.ChargedFockSpace 𝕜 α))
      (VirasoroProject.HeisenbergAlgebra.kgen 𝕜) =
        (1 : ModuleOfModuleAlgebra 𝕜
          (𝓤 𝕜 (VirasoroProject.HeisenbergAlgebra 𝕜))
          (VirasoroProject.ChargedFockSpace 𝕜 α) →ₗ[𝕜]
          ModuleOfModuleAlgebra 𝕜
            (𝓤 𝕜 (VirasoroProject.HeisenbergAlgebra 𝕜))
            (VirasoroProject.ChargedFockSpace 𝕜 α)) := by
  ext v
  change ModuleOfModuleAlgebra.mkAddHom 𝕜
      (𝓤 𝕜 (VirasoroProject.HeisenbergAlgebra 𝕜))
      (VirasoroProject.ChargedFockSpace 𝕜 α)
      (ιUEA 𝕜 (VirasoroProject.HeisenbergAlgebra.kgen 𝕜) •
        ModuleOfModuleAlgebra.unMkAddHom 𝕜
          (𝓤 𝕜 (VirasoroProject.HeisenbergAlgebra 𝕜))
          (VirasoroProject.ChargedFockSpace 𝕜 α) v) = v
  exact VirasoroProject.ChargedFockSpace.kgen_smul 𝕜 α
    (ModuleOfModuleAlgebra.unMkAddHom 𝕜
      (𝓤 𝕜 (VirasoroProject.HeisenbergAlgebra 𝕜))
      (VirasoroProject.ChargedFockSpace 𝕜 α) v)

/-- The canonical `CurrentHeisenbergRep` on `ChargedFockSpace 𝕜 α`. -/
noncomputable def chargedFockSpaceCurrentHeisenbergRep
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    CurrentHeisenbergRep 𝕜
      (ModuleOfModuleAlgebra 𝕜 (𝓤 𝕜 (VirasoroProject.HeisenbergAlgebra 𝕜))
        (VirasoroProject.ChargedFockSpace 𝕜 α)) :=
  CurrentHeisenbergRep.mk
    (chargedFockSpaceHeisenbergMode 𝕜 α)
    (by
      intro v
      filter_upwards [VirasoroProject.ChargedFockSpace.eventually_jgen_smul_eq_zero 𝕜 α
        (ModuleOfModuleAlgebra.unMkAddHom 𝕜
          (𝓤 𝕜 (VirasoroProject.HeisenbergAlgebra 𝕜))
          (VirasoroProject.ChargedFockSpace 𝕜 α) v)] with
        n hn
      change ModuleOfModuleAlgebra.mkAddHom 𝕜
        (𝓤 𝕜 (VirasoroProject.HeisenbergAlgebra 𝕜))
        (VirasoroProject.ChargedFockSpace 𝕜 α)
        (ιUEA 𝕜 (VirasoroProject.HeisenbergAlgebra.jgen 𝕜 n) •
          ModuleOfModuleAlgebra.unMkAddHom 𝕜
            (𝓤 𝕜 (VirasoroProject.HeisenbergAlgebra 𝕜))
            (VirasoroProject.ChargedFockSpace 𝕜 α) v) = 0
      simpa using congrArg
        (ModuleOfModuleAlgebra.mkAddHom 𝕜
          (𝓤 𝕜 (VirasoroProject.HeisenbergAlgebra 𝕜))
          (VirasoroProject.ChargedFockSpace 𝕜 α)) hn)
    (by
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
            hmn] using hbr.symm)

/-- Packaged Heisenberg-to-Sugawara morphism carrier: a `CurrentHeisenbergRep` paired
with its induced Virasoro Lie algebra representation and generator readbacks. -/
def CurrentSugawaraMorphism
    (𝕜 V : Type*) [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V] : Type _ :=
  Σ (HV : CurrentHeisenbergRep 𝕜 V × (VirasoroProject.VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ (V →ₗ[𝕜] V))),
    PLift ((∀ n : Int, HV.2 (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n) =
              HV.1.sugawaraStressMode n) ∧
           (HV.2 (VirasoroProject.VirasoroAlgebra.cgen 𝕜) = (1 : V →ₗ[𝕜] V)))

namespace CurrentSugawaraMorphism

variable {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

/-- The Heisenberg current component of a `CurrentSugawaraMorphism`. -/
def heisenberg (M : CurrentSugawaraMorphism 𝕜 V) : CurrentHeisenbergRep 𝕜 V :=
  M.1.1

/-- The induced Virasoro representation component of a `CurrentSugawaraMorphism`. -/
def virasoro (M : CurrentSugawaraMorphism 𝕜 V) :
    VirasoroProject.VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ (V →ₗ[𝕜] V) :=
  M.1.2

/-- The `lgen` Sugawara stress-mode readback of a `CurrentSugawaraMorphism`. -/
theorem lgen_apply (M : CurrentSugawaraMorphism 𝕜 V) :
    ∀ n : Int,
      M.virasoro (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n) =
        M.heisenberg.sugawaraStressMode n := by
  unfold virasoro heisenberg
  exact M.2.down.1

/-- The central generator identity readback of a `CurrentSugawaraMorphism`. -/
theorem central_apply (M : CurrentSugawaraMorphism 𝕜 V) :
    M.virasoro (VirasoroProject.VirasoroAlgebra.cgen 𝕜) =
      (1 : V →ₗ[𝕜] V) := by
  unfold virasoro
  exact M.2.down.2

/-- The canonical packaged Sugawara morphism induced by a Heisenberg current datum. -/
noncomputable def ofHeisenberg (H : CurrentHeisenbergRep 𝕜 V) :
    CurrentSugawaraMorphism 𝕜 V :=
  ⟨(H, H.currentSugawaraRepresentation),
   PLift.up ⟨fun n => H.currentSugawaraRepresentation_lgen_apply n,
             H.currentSugawaraRepresentation_central⟩⟩

/-- The canonical Sugawara morphism induced by `H` recovers `H`, its Virasoro
representation, and the `lgen` and `cgen` operator actions. -/
theorem ofHeisenberg_readout (H : CurrentHeisenbergRep 𝕜 V) :
    (ofHeisenberg H).heisenberg = H ∧
      (ofHeisenberg H).virasoro = H.currentSugawaraRepresentation ∧
      (∀ n : Int,
        (ofHeisenberg H).virasoro (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n) =
          H.sugawaraStressMode n) ∧
      (ofHeisenberg H).virasoro (VirasoroProject.VirasoroAlgebra.cgen 𝕜) =
        (1 : V →ₗ[𝕜] V) := by
  unfold ofHeisenberg heisenberg virasoro
  refine ⟨Eq.refl _, Eq.refl _, ?_, ?_⟩
  · intro n
    exact H.currentSugawaraRepresentation_lgen_apply n
  · exact H.currentSugawaraRepresentation_central

end CurrentSugawaraMorphism

/-- The charged Fock space canonical Sugawara morphism satisfies the four component
and generator readout identities. -/
theorem chargedFockSpace_currentSugawaraMorphism_readout
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    let H := chargedFockSpaceCurrentHeisenbergRep 𝕜 α
    let M := CurrentSugawaraMorphism.ofHeisenberg H
    M.heisenberg = H ∧
      M.virasoro = H.currentSugawaraRepresentation ∧
      (∀ n : Int,
        M.virasoro (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n) =
          H.sugawaraStressMode n) ∧
      M.virasoro (VirasoroProject.VirasoroAlgebra.cgen 𝕜) =
        (1 :
          VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α) := by
  dsimp only
  exact CurrentSugawaraMorphism.ofHeisenberg_readout
    (chargedFockSpaceCurrentHeisenbergRep 𝕜 α)

/-- Semantic alias for the completed central element of a raw CAR mode algebra. -/
def quantumRicciScalar {A : Type*} [Ring A] (C : RawCARModeAlgebra A) : A :=
  completedCentral C

end InfoGeometry.Canonical.CurrentSugawaraBridge
