import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Auto.tomita_kms_v4

noncomputable section

open Complex
open Matrix

namespace AnomalousKMSFlow

open scoped BigOperators

/-- Finite-dimensional anomaly bookkeeping context for a Tomita-KMS boundary flow. -/
structure ModularAnomalyContext (H : Type*) [AddCommGroup H] [Module ℂ H] where
  J : Module.End ℂ H
  Γ : Module.End ℂ H
  K : Module.End ℂ H
  δK : Module.End ℂ H
  tr : Module.End ℂ H →ₗ[ℂ] ℂ
  hJ_sq : J * J = 1
  hΓ_sq : Γ * Γ = 1
  hPerturb : J * K * J = -K + δK
  hTraceConjJ : ∀ A : Module.End ℂ H, tr (J * A * J) = tr A
  hTraceConjΓ : ∀ A : Module.End ℂ H, tr (Γ * A * Γ) = tr A
  hGammaOddAnomaly : tr (Γ * δK * Γ) = -tr δK

/-- Modular anomaly contribution is detected by trace as a half-anomaly term.

From `J K J = -K + δK` and cyclic/linear trace under `J` conjugation:
`tr K = (1/2) tr δK`. -/
theorem anomaly_trace_formula (H : Type*) [AddCommGroup H] [Module ℂ H]
    (C : ModularAnomalyContext H) :
    C.tr C.K = (1 / 2 : ℂ) * C.tr C.δK := by
  let J := C.J
  let K := C.K
  let δ := C.δK
  have h1 : C.tr (J * K * J) = C.tr K := C.hTraceConjJ K
  rw [C.hPerturb] at h1
  have h2 : C.tr (-K + δ) = -C.tr K + C.tr δ := by
    simp [map_add, map_neg]
  rw [h2] at h1
  have h3 : -C.tr K + C.tr δ = C.tr K := h1
  have h4sum : C.tr δ = C.tr K + C.tr K := by
    have h4' := congrArg (fun z => z + C.tr K) h3
    simpa [add_assoc, add_left_comm, add_comm] using h4'
  have h4 : (2 : ℂ) * C.tr K = C.tr δ := by
    have h4symm : C.tr K + C.tr K = C.tr δ := by
      simpa [add_comm, add_left_comm, add_assoc] using h4sum.symm
    simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using h4symm
  calc
    C.tr K = (1 / 2 : ℂ) * ((2 : ℂ) * C.tr K) := by
      field_simp
    _ = (1 / 2 : ℂ) * C.tr δ := by rw [h4]

/-- Klein-bottle V₄ symmetry can force the anomalous trace to vanish if the anomaly
is simultaneously `Γ`-even (from trace conjugation invariance) and `Γ`-odd
in anomaly sector. -/
theorem anomaly_trace_vanishes (H : Type*) [AddCommGroup H] [Module ℂ H]
    (C : ModularAnomalyContext H) : C.tr C.δK = 0 := by
  have h : C.tr C.δK = -C.tr C.δK := by
    calc
      C.tr C.δK = C.tr (C.Γ * C.δK * C.Γ) := (C.hTraceConjΓ C.δK).symm
      _ = -C.tr C.δK := C.hGammaOddAnomaly
  have h2 : (2 : ℂ) * C.tr C.δK = 0 := by
    have h2' := congrArg (fun z => z + C.tr C.δK) h
    simpa [add_assoc, add_left_comm, add_comm, two_mul] using h2'
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- If the trace is faithful on this sector, annihilation of trace forces
`δK = 0` as an operator. -/
def TraceFaithful (H : Type*) [AddCommGroup H] [Module ℂ H]
    (tr : Module.End ℂ H →ₗ[ℂ] ℂ) : Prop :=
  Function.Injective tr

/-- The anomalous index associated to a modular-context. -/
def anomalousIndex (H : Type*) [AddCommGroup H] [Module ℂ H]
    (C : ModularAnomalyContext H) : ℂ :=
  C.tr C.K

theorem anomaly_operator_vanishes (H : Type*) [AddCommGroup H] [Module ℂ H]
    {tr : Module.End ℂ H →ₗ[ℂ] ℂ}
    (hFaith : TraceFaithful H tr)
    {δK : Module.End ℂ H}
    (hδzero : tr δK = 0) : δK = 0 := by
  exact hFaith (by simpa using hδzero)

theorem anomalous_operator_vanishes_v4 (H : Type*) [AddCommGroup H] [Module ℂ H]
    (C : ModularAnomalyContext H)
    (hFaith : TraceFaithful H C.tr) : C.δK = 0 := by
  exact anomaly_operator_vanishes H hFaith (anomaly_trace_vanishes H C)

theorem anomaly_trace_total_zero (H : Type*) [AddCommGroup H] [Module ℂ H]
    (C : ModularAnomalyContext H)
    (hFaith : TraceFaithful H C.tr) : C.tr C.K = 0 := by
  rw [anomaly_trace_formula (H := H) C]
  simp [anomalous_operator_vanishes_v4 (H := H) C hFaith]

/-- General V₄-type cross-cap trap with explicit involution ε.

If ε is involutive, commutes with δK, and implements cross-cap reversal
`ε * δK * ε = -δK`, then the anomaly operator must vanish. Hence the
anomalous index is zero.
-/
theorem anomaly_trap_from_crosscap
    (H : Type*) [AddCommGroup H] [Module ℂ H]
    (C : ModularAnomalyContext H)
    (ε : Module.End ℂ H)
    (hε_sq : ε * ε = 1)
    (h_auto : ε * C.δK = C.δK * ε)
    (h_crosscap : ε * C.δK * ε = -C.δK) : C.δK = 0 ∧ anomalousIndex H C = 0 := by
  have h_auto' : ε * C.δK * ε = C.δK := by
    calc
      ε * C.δK * ε = (C.δK * ε) * ε := by simpa [h_auto, mul_assoc]
      _ = C.δK * (ε * ε) := by simp [mul_assoc]
      _ = C.δK * 1 := by rw [hε_sq]
      _ = C.δK := by simp
  have h_sign : -C.δK = C.δK := by
    calc
      -C.δK = ε * C.δK * ε := by simpa using h_crosscap.symm
      _ = C.δK := h_auto'
  have hδ : C.δK = 0 := by
    ext x
    have hpoint : -(C.δK x) = C.δK x := by
      simpa using congrArg (fun T : Module.End ℂ H => T x) h_sign
    have hmul : (2 : ℂ) • (C.δK x) = 0 := by
      calc
        (2 : ℂ) • (C.δK x) = (C.δK x) + (C.δK x) := by
          simpa using (two_smul (R := ℂ) (M := H) (C.δK x))
        _ = -(C.δK x) + (C.δK x) := by simpa [hpoint]
        _ = 0 := neg_add_cancel (C.δK x)
    exact (smul_eq_zero.mp hmul).resolve_left (by norm_num)
  have hIndex : anomalousIndex H C = 0 := by
    rw [anomalousIndex, anomaly_trace_formula (H := H) C]
    simp [hδ]
  exact ⟨hδ, hIndex⟩

/-- Concrete γ-based corollary for an ambient modular context. -/
theorem anomaly_trap_from_gamma
    (H : Type*) [AddCommGroup H] [Module ℂ H]
    (C : ModularAnomalyContext H)
    (h_crosscap : C.Γ * C.δK * C.Γ = -C.δK)
    (h_auto : C.Γ * C.δK = C.δK * C.Γ) : C.δK = 0 ∧ anomalousIndex H C = 0 := by
  simpa [anomalousIndex] using
    (anomaly_trap_from_crosscap (H := H) C C.Γ C.hΓ_sq h_auto h_crosscap)

/-- Thermodynamic shadow of a modular anomaly: introducing `A(β)` in the total
partition multiplies the neutral unit by `exp(A(β))`. -/
def anomalousPartition (β : ℝ → ℝ) (A : ℝ → ℝ) : ℝ → ℝ :=
  fun s => (β s) * Real.exp (A s)

/-- In the grand-canonical anomaly convention, the anomalous total free energy is
`F_anom(β) = -(1/β) A(β)` when `Z_total = Z_boson * Z_super * exp(A)`. -/
def anomalousFreeEnergy (β : ℝ → ℝ) (A : ℝ → ℝ) : ℝ → ℝ :=
  fun s => -(1 / β s) * (A s)

/-- If anomaly vanishes identically, CPT thermodynamics remains neutral. -/
theorem anomaly_free_if_zero (β : ℝ → ℝ) (A : ℝ → ℝ) (hA : ∀ s, A s = 0) :
    (∀ s, anomalousPartition β A s = β s) ∧ (∀ s, anomalousFreeEnergy β A s = 0) := by
  constructor
  · intro s
    simp [anomalousPartition, hA s]
  · intro s
    simp [anomalousFreeEnergy, hA s]

/-- Spectral-line leakage from nonzero anomaly scale. -/
def anomalousLineLeak (A : ℝ → ℝ) : ℝ → ℝ := fun s => |A s|

/-- Index-induced constant leakage profile from anomalous index. -/
def anomalousIndexLeakProfile (H : Type*) [AddCommGroup H] [Module ℂ H]
    (C : ModularAnomalyContext H) : ℝ → ℝ :=
  fun _ => ‖anomalousIndex H C‖

theorem anomalous_index_zero_implies_no_leakage
    (H : Type*) [AddCommGroup H] [Module ℂ H]
    (C : ModularAnomalyContext H)
    (hIndex : anomalousIndex H C = 0) : ∀ s, anomalousLineLeak (anomalousIndexLeakProfile H C) s = 0 := by
  intro s
  simp [anomalousIndexLeakProfile, anomalousLineLeak, hIndex]

theorem leakage_characterization (A : ℝ → ℝ)
    (hA : ∀ s, A s = 0) : (∀ s, anomalousLineLeak A s = 0) := by
  intro s
  simp [anomalousLineLeak, hA s]

/-- One-line topological consequence: cross-cap trap closes spectral-line leakage at index level. -/
theorem anomaly_trap_implies_no_leakage
    (H : Type*) [AddCommGroup H] [Module ℂ H]
    (C : ModularAnomalyContext H)
    (ε : Module.End ℂ H)
    (hε_sq : ε * ε = 1)
    (h_auto : ε * C.δK = C.δK * ε)
    (h_crosscap : ε * C.δK * ε = -C.δK) : ∀ s, anomalousLineLeak (anomalousIndexLeakProfile H C) s = 0 := by
  exact anomalous_index_zero_implies_no_leakage (H := H) C
    ((anomaly_trap_from_crosscap (H := H) C ε hε_sq h_auto h_crosscap).2)

/-- Concrete γ-based corollary: topological trap gives no index leakage profile. -/
theorem anomaly_trap_from_gamma_implies_no_leakage
    (H : Type*) [AddCommGroup H] [Module ℂ H]
    (C : ModularAnomalyContext H)
    (h_crosscap : C.Γ * C.δK * C.Γ = -C.δK)
    (h_auto : C.Γ * C.δK = C.δK * C.Γ) : ∀ s, anomalousLineLeak (anomalousIndexLeakProfile H C) s = 0 := by
  exact anomaly_trap_implies_no_leakage (H := H) C C.Γ C.hΓ_sq h_auto h_crosscap

/-! 
Concrete V₄/Klein-bottle specialization on `Fin 2 → ℂ`:
`J` and `Γ` are realized by the canonical 2×2 matrices
`J = [[0,1],[1,0]]`, `Γ = diag(1,-1)`.
-/

/-- TOMITA-canonical V₄ maps imported from `tomita_kms_v4` and complexified. -/
def tomitaBottleJ : Module.End ℂ (Fin 2 → ℂ) :=
  Matrix.toLin' (Matrix.map kleinFourCanonical.J Complex.ofRealHom)

def tomitaBottleΓ : Module.End ℂ (Fin 2 → ℂ) :=
  Matrix.toLin' (Matrix.map kleinFourCanonical.Γ Complex.ofRealHom)

/-- Canonical V₄ modular conjugation in the 2-dim complex test sector. -/
def kleinBottleJ : Module.End ℂ (Fin 2 → ℂ) :=
  Matrix.toLin' (!![(0 : ℂ), 1; 1, 0])

def kleinBottleΓ : Module.End ℂ (Fin 2 → ℂ) :=
  Matrix.toLin' (!![(1 : ℂ), 0; 0, -1])

def kleinBottleTrace : Module.End ℂ (Fin 2 → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.trace ℂ (Fin 2 → ℂ)

theorem tomitaBottleJ_eq_kleinBottleJ : tomitaBottleJ = kleinBottleJ := by
  apply (LinearMap.toMatrix').injective
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [tomitaBottleJ, kleinBottleJ, kleinFourCanonical]

theorem tomitaBottleΓ_eq_kleinBottleΓ : tomitaBottleΓ = kleinBottleΓ := by
  apply (LinearMap.toMatrix').injective
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [tomitaBottleΓ, kleinBottleΓ, kleinFourCanonical]

theorem kleinBottleJ_sq : kleinBottleJ * kleinBottleJ = 1 := by
  have hM : LinearMap.toMatrix' (kleinBottleJ * kleinBottleJ)
      = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    calc
      LinearMap.toMatrix' (kleinBottleJ * kleinBottleJ)
          = LinearMap.toMatrix' kleinBottleJ * LinearMap.toMatrix' kleinBottleJ := by
          simpa using (LinearMap.toMatrix'_mul (f := kleinBottleJ) (g := kleinBottleJ))
      _ = !![(0 : ℂ), 1; 1, 0] * !![(0 : ℂ), 1; 1, 0] := by
          simp [kleinBottleJ]
      _ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
          ext i j <;> fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hlin : Matrix.toLin' (1 : Matrix (Fin 2) (Fin 2) ℂ) = kleinBottleJ * kleinBottleJ := by
    simpa [hM] using (Matrix.toLin'_toMatrix' (f := kleinBottleJ * kleinBottleJ))
  simpa using hlin.symm

theorem kleinBottleΓ_sq : kleinBottleΓ * kleinBottleΓ = 1 := by
  have hM : LinearMap.toMatrix' (kleinBottleΓ * kleinBottleΓ)
      = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    calc
      LinearMap.toMatrix' (kleinBottleΓ * kleinBottleΓ)
          = LinearMap.toMatrix' kleinBottleΓ * LinearMap.toMatrix' kleinBottleΓ := by
          simpa using (LinearMap.toMatrix'_mul (f := kleinBottleΓ) (g := kleinBottleΓ))
      _ = !![(1 : ℂ), 0; 0, -1] * !![(1 : ℂ), 0; 0, -1] := by
          simp [kleinBottleΓ]
      _ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
          ext i j <;> fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hlin : Matrix.toLin' (1 : Matrix (Fin 2) (Fin 2) ℂ) = kleinBottleΓ * kleinBottleΓ := by
    simpa [hM] using (Matrix.toLin'_toMatrix' (f := kleinBottleΓ * kleinBottleΓ))
  simpa using hlin.symm

theorem kleinBottleTraceConjJ (A : Module.End ℂ (Fin 2 → ℂ)) :
    kleinBottleTrace (kleinBottleJ * A * kleinBottleJ) = kleinBottleTrace A := by
  have h := LinearMap.trace_mul_comm (R := ℂ) (M := Fin 2 → ℂ) kleinBottleJ (A * kleinBottleJ)
  simpa [kleinBottleJ_sq, kleinBottleTrace, mul_assoc] using h

theorem kleinBottleTraceConjΓ (A : Module.End ℂ (Fin 2 → ℂ)) :
    kleinBottleTrace (kleinBottleΓ * A * kleinBottleΓ) = kleinBottleTrace A := by
  have h := LinearMap.trace_mul_comm (R := ℂ) (M := Fin 2 → ℂ) kleinBottleΓ (A * kleinBottleΓ)
  simpa [kleinBottleΓ_sq, kleinBottleTrace, mul_assoc] using h

/-- Build the abstract anomaly context from the TOMITA-canonical V₄ data. -/
def tomitaBottleAnomalyContext (K δK : Module.End ℂ (Fin 2 → ℂ))
    (hPert : tomitaBottleJ * K * tomitaBottleJ = -K + δK)
    (hΓOdd : kleinBottleTrace (tomitaBottleΓ * δK * tomitaBottleΓ) = -kleinBottleTrace δK)
    : ModularAnomalyContext (Fin 2 → ℂ) :=
  { J := tomitaBottleJ
    Γ := tomitaBottleΓ
    K := K
    δK := δK
    tr := kleinBottleTrace
    hJ_sq := by simpa [tomitaBottleJ_eq_kleinBottleJ] using (kleinBottleJ_sq)
    hΓ_sq := by simpa [tomitaBottleΓ_eq_kleinBottleΓ] using (kleinBottleΓ_sq)
    hPerturb := hPert
    hTraceConjJ := by
      intro A
      rw [tomitaBottleJ_eq_kleinBottleJ]
      exact kleinBottleTraceConjJ A
    hTraceConjΓ := by
      intro A
      rw [tomitaBottleΓ_eq_kleinBottleΓ]
      exact kleinBottleTraceConjΓ A
    hGammaOddAnomaly := by
      simpa [tomitaBottleΓ_eq_kleinBottleΓ] using hΓOdd
  }

/-- Build the abstract anomaly context from the concrete Klein V₄ data. -/

def kleinBottleAnomalyContext (K δK : Module.End ℂ (Fin 2 → ℂ))
    (hPert : kleinBottleJ * K * kleinBottleJ = -K + δK)
    (hΓOdd : kleinBottleTrace (kleinBottleΓ * δK * kleinBottleΓ) = -kleinBottleTrace δK)
    : ModularAnomalyContext (Fin 2 → ℂ) :=
  { J := kleinBottleJ
    Γ := kleinBottleΓ
    K := K
    δK := δK
    tr := kleinBottleTrace
    hJ_sq := kleinBottleJ_sq
    hΓ_sq := kleinBottleΓ_sq
    hPerturb := hPert
    hTraceConjJ := by
      intro A
      exact kleinBottleTraceConjJ A
    hTraceConjΓ := by
      intro A
      exact kleinBottleTraceConjΓ A
    hGammaOddAnomaly := hΓOdd
  }

/-- Concrete anomaly cancellation in the Klein V₄ sector (trace faithful + Γ-odd).
This is the requested V₄/Klein-bottle specialization of the abstract result. -/
theorem kleinBottle_anomaly_vanishes (K δK : Module.End ℂ (Fin 2 → ℂ))
    (hPert : kleinBottleJ * K * kleinBottleJ = -K + δK)
    (hΓOdd : kleinBottleTrace (kleinBottleΓ * δK * kleinBottleΓ) = -kleinBottleTrace δK)
    (hFaith : TraceFaithful (Fin 2 → ℂ) kleinBottleTrace) : δK = 0 := by
  let C := kleinBottleAnomalyContext K δK hPert hΓOdd
  exact anomalous_operator_vanishes_v4 (H := Fin 2 → ℂ) C hFaith

/-- Concrete V₄ trace-vanishing specialization. -/
theorem kleinBottle_anomaly_trace_vanishes (K δK : Module.End ℂ (Fin 2 → ℂ))
    (hPert : kleinBottleJ * K * kleinBottleJ = -K + δK)
    (hΓOdd : kleinBottleTrace (kleinBottleΓ * δK * kleinBottleΓ) = -kleinBottleTrace δK)
    : kleinBottleTrace δK = 0 := by
  let C := kleinBottleAnomalyContext K δK hPert hΓOdd
  exact anomaly_trace_vanishes (H := Fin 2 → ℂ) C

/-- Same cancellation statement using the TOMITA-canonical matrices directly. -/
theorem tomitaBottle_anomaly_vanishes (K δK : Module.End ℂ (Fin 2 → ℂ))
    (hPert : tomitaBottleJ * K * tomitaBottleJ = -K + δK)
    (hΓOdd : kleinBottleTrace (tomitaBottleΓ * δK * tomitaBottleΓ) = -kleinBottleTrace δK)
    (hFaith : TraceFaithful (Fin 2 → ℂ) kleinBottleTrace) : δK = 0 := by
  let C := tomitaBottleAnomalyContext K δK hPert hΓOdd
  exact anomalous_operator_vanishes_v4 (H := Fin 2 → ℂ) C hFaith

/-- Same Γ-odd cancellation result in TOMITA notation, via trace vanishing. -/
theorem tomitaBottle_anomaly_trace_vanishes (K δK : Module.End ℂ (Fin 2 → ℂ))
    (hPert : tomitaBottleJ * K * tomitaBottleJ = -K + δK)
    (hΓOdd : kleinBottleTrace (tomitaBottleΓ * δK * tomitaBottleΓ) = -kleinBottleTrace δK)
    : kleinBottleTrace δK = 0 := by
  let C := tomitaBottleAnomalyContext K δK hPert hΓOdd
  exact anomaly_trace_vanishes (H := Fin 2 → ℂ) C

end AnomalousKMSFlow
