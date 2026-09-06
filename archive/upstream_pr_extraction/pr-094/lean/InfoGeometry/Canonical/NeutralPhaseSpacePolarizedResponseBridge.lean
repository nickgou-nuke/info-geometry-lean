import InfoGeometry.Clifford.NeutralPhaseSpaceCore

/-!
# Polarized response on the neutral phase-space carrier

This file records only the algebraic compatibility needed for a polarized
response form. It does not assert positivity, Fisher geometry, a Hessian
interpretation, or a metriplectic structure.
-/

namespace InfoGeometry.Canonical.NeutralPhaseSpacePolarizedResponseBridge

open InfoGeometry.Clifford.NeutralPhaseSpaceCore

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

abbrev End (E : Type*) [AddCommGroup E] [Module ℝ E] :=
  PhaseSpaceCarrier E →ₗ[ℝ] PhaseSpaceCarrier E

noncomputable def polarizedForm
    (J L : End E) : PhaseSpaceCarrier E → PhaseSpaceCarrier E → ℝ :=
  fun X Y => canonicalNeutralBilin (J (L X)) Y

def EtaSelfAdjoint (L : End E) : Prop :=
  ∀ X Y, canonicalNeutralBilin (L X) Y = canonicalNeutralBilin X (L Y)

def CommutesWith (J L : End E) : Prop :=
  ∀ X, J (L X) = L (J X)

def HasPolarizedDissipation
    (J L : End E) : Prop :=
  ∀ X, 0 ≤ polarizedForm J L X X

private theorem canonicalNeutralBilin_symm_local
    (X Y : PhaseSpaceCarrier E) :
    canonicalNeutralBilin X Y = canonicalNeutralBilin Y X := by
  rcases X with ⟨x, ξ⟩
  rcases Y with ⟨y, η⟩
  simp [canonicalNeutralBilin_apply, add_comm]

theorem polarizedForm_response_selfAdjoint
    (J L : End E)
    (hL : EtaSelfAdjoint L)
    (hJL : CommutesWith J L)
    (X Y : PhaseSpaceCarrier E) :
    polarizedForm J L X Y = canonicalNeutralBilin (J X) (L Y) := by
  unfold polarizedForm
  rw [hJL X]
  exact hL (J X) Y

/-! ## Algebraic polarizations and response operators -/

/- A polarization is deliberately a structure on the existing neutral carrier.
It does not introduce a topology or identify the carrier with a Hilbert space. -/
structure NeutralKreinPolarization where
  J : End E
  j_involutive : J.comp J = LinearMap.id
  j_eta_symmetric : ∀ X Y,
    canonicalNeutralBilin (J X) Y = canonicalNeutralBilin X (J Y)
  hilbert_positive : ∀ X, X ≠ 0 → canonicalNeutralBilin (J X) X > 0

namespace NeutralKreinPolarization

variable (P : NeutralKreinPolarization (E := E))

noncomputable def hilbertMetric (X Y : PhaseSpaceCarrier E) : ℝ :=
  canonicalNeutralBilin (P.J X) Y

theorem J_square (X : PhaseSpaceCarrier E) :
    P.J (P.J X) = X := by
  exact LinearMap.congr_fun P.j_involutive X

theorem hilbertMetric_symm (X Y : PhaseSpaceCarrier E) :
    P.hilbertMetric X Y = P.hilbertMetric Y X := by
  unfold hilbertMetric
  rw [P.j_eta_symmetric]
  exact canonicalNeutralBilin_symm_local _ _

theorem hilbertMetric_positive (X : PhaseSpaceCarrier E) (hX : X ≠ 0) :
    0 < P.hilbertMetric X X := by
  exact P.hilbert_positive X hX

theorem eta_recovered (X Y : PhaseSpaceCarrier E) :
    P.hilbertMetric (P.J X) Y = canonicalNeutralBilin X Y := by
  unfold hilbertMetric
  rw [P.J_square]

end NeutralKreinPolarization

structure NeutralResponseOperator where
  A : End E
  a_eta_symmetric : ∀ X Y,
    canonicalNeutralBilin (A X) Y = canonicalNeutralBilin X (A Y)
  a_eta_positive : ∀ X, X ≠ 0 → canonicalNeutralBilin (A X) X > 0

namespace NeutralResponseOperator

variable (R : NeutralResponseOperator (E := E))

noncomputable def fisherMetric (X Y : PhaseSpaceCarrier E) : ℝ :=
  canonicalNeutralBilin (R.A X) Y

theorem fisherMetric_symm (X Y : PhaseSpaceCarrier E) :
    R.fisherMetric X Y = R.fisherMetric Y X := by
  unfold fisherMetric
  rw [R.a_eta_symmetric]
  exact canonicalNeutralBilin_symm_local _ _

theorem fisherMetric_positive (X : PhaseSpaceCarrier E) (hX : X ≠ 0) :
    0 < R.fisherMetric X X := by
  exact R.a_eta_positive X hX

theorem fisherMetric_eq_hilbertMetric
    (P : NeutralKreinPolarization (E := E))
    (hA : R.A = P.J) (X Y : PhaseSpaceCarrier E) :
    R.fisherMetric X Y = P.hilbertMetric X Y := by
  unfold fisherMetric NeutralKreinPolarization.hilbertMetric
  rw [hA]

end NeutralResponseOperator

/-! ## The algebraic metriplectic split

The positivity statement below is relative to a chosen polarization.  The
eta-symmetry conditions remain purely algebraic and do not assert a flow,
complete positivity, or a second-law theorem. -/
structure NeutralMetriplecticOperator where
  L : End E
  L_skew : End E
  L_sym : End E
  decomp : L = L_skew + L_sym
  skew_eta : ∀ X Y,
    canonicalNeutralBilin (L_skew X) Y =
      -canonicalNeutralBilin X (L_skew Y)
  sym_eta : ∀ X Y,
    canonicalNeutralBilin (L_sym X) Y =
      canonicalNeutralBilin X (L_sym Y)

namespace NeutralMetriplecticOperator

variable (M : NeutralMetriplecticOperator (E := E))

def HasPolarizedDissipation
    (P : NeutralKreinPolarization (E := E)) : Prop :=
  ∀ X, 0 ≤ P.hilbertMetric (M.L_sym X) X

def IsPolarizationCompatible
    (P : NeutralKreinPolarization (E := E)) : Prop :=
  M.L_sym.comp P.J = P.J.comp M.L_sym

theorem eta_split (X Y : PhaseSpaceCarrier E) :
    canonicalNeutralBilin (M.L X) Y =
      canonicalNeutralBilin (M.L_skew X) Y +
        canonicalNeutralBilin (M.L_sym X) Y := by
  rw [M.decomp]
  simp [map_add]

theorem skew_channel_swap (X Y : PhaseSpaceCarrier E) :
    canonicalNeutralBilin (M.L_skew X) Y =
      -canonicalNeutralBilin X (M.L_skew Y) :=
  M.skew_eta X Y

theorem symmetric_channel_swap (X Y : PhaseSpaceCarrier E) :
    canonicalNeutralBilin (M.L_sym X) Y =
      canonicalNeutralBilin X (M.L_sym Y) :=
  M.sym_eta X Y

theorem polarizedForm_symmetric_of_compatible
    (P : NeutralKreinPolarization (E := E))
    (hP : M.IsPolarizationCompatible P)
    (X Y : PhaseSpaceCarrier E) :
    polarizedForm P.J M.L_sym X Y =
      polarizedForm P.J M.L_sym Y X := by
  unfold polarizedForm
  have hX : P.J (M.L_sym X) = M.L_sym (P.J X) :=
    (LinearMap.congr_fun hP X).symm
  rw [hX]
  rw [M.sym_eta]
  rw [P.j_eta_symmetric]
  exact canonicalNeutralBilin_symm_local _ _

theorem dissipation_of
    (P : NeutralKreinPolarization (E := E))
    (hD : M.HasPolarizedDissipation P) (X : PhaseSpaceCarrier E) :
    0 ≤ P.hilbertMetric (M.L_sym X) X :=
  hD X

end NeutralMetriplecticOperator

end InfoGeometry.Canonical.NeutralPhaseSpacePolarizedResponseBridge
