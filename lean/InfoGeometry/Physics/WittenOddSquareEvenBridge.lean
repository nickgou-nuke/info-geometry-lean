import InfoGeometry.Physics.SupergradedDiracCrystal

namespace InfoGeometry.Physics

theorem odd_square_commutes_with_grading
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (Gamma Q : V →ₗ[ℚ] V)
    (hodd : Gamma.comp Q = - Q.comp Gamma) :
    Gamma.comp (Q.comp Q) = (Q.comp Q).comp Gamma := by
  calc
    Gamma.comp (Q.comp Q) = (Gamma.comp Q).comp Q :=
      (LinearMap.comp_assoc _ _ _).symm
    _ = (- Q.comp Gamma).comp Q := by
      exact congrArg (fun L => L.comp Q) hodd
    _ = - ((Q.comp Gamma).comp Q) := by rw [LinearMap.neg_comp]
    _ = - (Q.comp (Gamma.comp Q)) := by rw [LinearMap.comp_assoc]
    _ = - (Q.comp (- Q.comp Gamma)) := by
      exact congrArg (fun L => - Q.comp L) hodd
    _ = Q.comp (Q.comp Gamma) := by rw [LinearMap.comp_neg, neg_neg]
    _ = (Q.comp Q).comp Gamma := LinearMap.comp_assoc _ _ _

/-!
Transport laws are stated with the source operators, target operators, and
surjective intertwiner as explicit inputs.  No structure stores these laws as
evidence fields.
-/

theorem target_susy_algebra
    {V VInf : Type*}
    [AddCommGroup V] [Module ℚ V]
    [AddCommGroup VInf] [Module ℚ VInf]
    (stage : SupergradedDiracSystem V)
    (targetQ targetH : VInf →ₗ[ℚ] VInf)
    (map : V →ₗ[ℚ] VInf)
    (map_surjective : Function.Surjective map)
    (charge_intertwines : ∀ x, map (stage.Q x) = targetQ (map x))
    (hamiltonian_intertwines : ∀ x, map (stage.H x) = targetH (map x)) :
    targetQ.comp targetQ = targetH := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := map_surjective z
  simp only [LinearMap.comp_apply]
  rw [← charge_intertwines x,
    ← charge_intertwines (stage.Q x),
    ← hamiltonian_intertwines x]
  simpa [LinearMap.comp_apply] using
    congrArg (fun y => map y) (congrArg (fun L => L x) stage.susy_algebra)

theorem target_witten_odd
    {V VInf : Type*}
    [AddCommGroup V] [Module ℚ V]
    [AddCommGroup VInf] [Module ℚ VInf]
    (stage : SupergradedDiracSystem V)
    (targetGamma targetQ : VInf →ₗ[ℚ] VInf)
    (map : V →ₗ[ℚ] VInf)
    (map_surjective : Function.Surjective map)
    (gamma_intertwines : ∀ x, map (stage.Gamma x) = targetGamma (map x))
    (charge_intertwines : ∀ x, map (stage.Q x) = targetQ (map x)) :
    targetGamma.comp targetQ = - targetQ.comp targetGamma := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := map_surjective z
  simp only [LinearMap.comp_apply, LinearMap.neg_apply]
  rw [← charge_intertwines x,
    ← gamma_intertwines (stage.Q x),
    ← gamma_intertwines x,
    ← charge_intertwines (stage.Gamma x)]
  simpa [LinearMap.comp_apply] using
    congrArg (fun y => map y) (congrArg (fun L => L x) stage.witten_odd)

theorem target_hamiltonian_even
    {V VInf : Type*}
    [AddCommGroup V] [Module ℚ V]
    [AddCommGroup VInf] [Module ℚ VInf]
    (stage : SupergradedDiracSystem V)
    (targetGamma targetH : VInf →ₗ[ℚ] VInf)
    (map : V →ₗ[ℚ] VInf)
    (map_surjective : Function.Surjective map)
    (gamma_intertwines : ∀ x, map (stage.Gamma x) = targetGamma (map x))
    (hamiltonian_intertwines : ∀ x, map (stage.H x) = targetH (map x)) :
    targetGamma.comp targetH = targetH.comp targetGamma := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := map_surjective z
  simp only [LinearMap.comp_apply]
  rw [← hamiltonian_intertwines x,
    ← gamma_intertwines (stage.H x),
    ← gamma_intertwines x,
    ← hamiltonian_intertwines (stage.Gamma x)]
  simpa [LinearMap.comp_apply] using
    congrArg (fun y => map y)
      (congrArg (fun L => L x) (SupergradedDiracSystem.hamiltonian_even stage))

end InfoGeometry.Physics
