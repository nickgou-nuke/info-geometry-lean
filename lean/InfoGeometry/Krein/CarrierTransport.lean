import InfoGeometry.Krein.InvolutiveSelfDualCarrier

/-!
# Carrier Transport

This module defines the minimal flow requirements for the involutive self-dual
carrier.

Scope discipline:
- flow law (`transport_zero`, `transport_add`),
- pairing preservation.

No commutation assumptions with `J`, `ε`, or `K` are included here.
-/

namespace InfoGeometry.Krein

/-- Minimal transport flow on an involutive self-dual carrier. -/
structure CarrierTransport (X : InvolutiveSelfDualCarrier) where
  transport : ℝ → (X.H →L[ℝ] X.H)

  transport_zero :
    transport 0 = ContinuousLinearMap.id ℝ X.H
  transport_add :
    ∀ s t, transport (s + t) = (transport s).comp (transport t)

  transport_preserves_pairing :
    ∀ t u v,
      X.kreinPairing (transport t u) (transport t v) = X.kreinPairing u v

namespace CarrierTransport

@[simp] theorem transport_zero_apply
    {X : InvolutiveSelfDualCarrier} (T : CarrierTransport X) (u : X.H) :
    T.transport 0 u = u := by
  have h := congrArg (fun f : X.H →L[ℝ] X.H => f u) T.transport_zero
  simpa using h

theorem transport_add_apply
    {X : InvolutiveSelfDualCarrier} (T : CarrierTransport X)
    (s t : ℝ) (u : X.H) :
    T.transport (s + t) u = T.transport s (T.transport t u) := by
  have h := congrArg (fun f : X.H →L[ℝ] X.H => f u)
    (T.transport_add s t)
  simpa [ContinuousLinearMap.comp_apply] using h

theorem transport_preserves_pairing_apply
    {X : InvolutiveSelfDualCarrier} (T : CarrierTransport X)
    (t : ℝ) (u v : X.H) :
    X.kreinPairing (T.transport t u) (T.transport t v) =
      X.kreinPairing u v :=
  T.transport_preserves_pairing t u v

theorem transport_neg_apply_left
    {X : InvolutiveSelfDualCarrier} (T : CarrierTransport X)
    (t : ℝ) (u : X.H) :
    T.transport (-t) (T.transport t u) = u := by
  have h := congrArg (fun f : X.H →L[ℝ] X.H => f u)
    (T.transport_add (-t) t)
  rw [neg_add_cancel, T.transport_zero] at h
  simpa [ContinuousLinearMap.comp_apply] using h.symm

theorem transport_neg_apply_right
    {X : InvolutiveSelfDualCarrier} (T : CarrierTransport X)
    (t : ℝ) (u : X.H) :
    T.transport t (T.transport (-t) u) = u := by
  have h := congrArg (fun f : X.H →L[ℝ] X.H => f u)
    (T.transport_add t (-t))
  rw [add_neg_cancel, T.transport_zero] at h
  simpa [ContinuousLinearMap.comp_apply] using h.symm

theorem transport_injective
    {X : InvolutiveSelfDualCarrier} (T : CarrierTransport X) (t : ℝ) :
    Function.Injective (T.transport t) := by
  intro u v h
  have h' := congrArg (T.transport (-t)) h
  simpa [T.transport_neg_apply_left] using h'

theorem transport_surjective
    {X : InvolutiveSelfDualCarrier} (T : CarrierTransport X) (t : ℝ) :
    Function.Surjective (T.transport t) := by
  intro v
  refine ⟨T.transport (-t) v, ?_⟩
  exact T.transport_neg_apply_right t v

noncomputable def transportLinearEquiv
    {X : InvolutiveSelfDualCarrier} (T : CarrierTransport X) (t : ℝ) :
    X.H ≃ₗ[ℝ] X.H :=
  LinearEquiv.ofBijective (T.transport t).toLinearMap
    ⟨transport_injective T t, transport_surjective T t⟩

@[simp] theorem transportLinearEquiv_apply
    {X : InvolutiveSelfDualCarrier} (T : CarrierTransport X)
    (t : ℝ) (u : X.H) :
    T.transportLinearEquiv t u = T.transport t u :=
  rfl

theorem transportLinearEquiv_add
    {X : InvolutiveSelfDualCarrier} (T : CarrierTransport X)
    (s t : ℝ) :
    T.transportLinearEquiv (s + t) =
      (T.transportLinearEquiv t).trans (T.transportLinearEquiv s) := by
  ext u
  simp [transport_add_apply]

@[simp] theorem transportLinearEquiv_zero
    {X : InvolutiveSelfDualCarrier} (T : CarrierTransport X) :
    T.transportLinearEquiv 0 = LinearEquiv.refl ℝ X.H := by
  ext u
  simp [transport_zero_apply]

theorem transportLinearEquiv_preserves_pairing
    {X : InvolutiveSelfDualCarrier} (T : CarrierTransport X)
    (t : ℝ) (u v : X.H) :
    X.kreinPairing (T.transportLinearEquiv t u)
        (T.transportLinearEquiv t v) =
      X.kreinPairing u v := by
  simp [transportLinearEquiv_apply,
    transport_preserves_pairing_apply]

  theorem transportLinearEquiv_neg
    {X : InvolutiveSelfDualCarrier} (T : CarrierTransport X)
    (t : ℝ) :
    T.transportLinearEquiv (-t) =
      (T.transportLinearEquiv t).symm := by
  ext u
  apply (T.transportLinearEquiv t).injective
  simp [transportLinearEquiv_apply, transport_neg_apply_right]

end CarrierTransport

end InfoGeometry.Krein
