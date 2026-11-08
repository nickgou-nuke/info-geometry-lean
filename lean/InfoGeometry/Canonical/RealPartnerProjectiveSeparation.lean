import InfoGeometry.Canonical.HestenesRealStructures
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! A square-minus-one real phase partner cannot lie on the same nonzero
real projective line.  This is separate from conjugate-linear Kramers data. -/
noncomputable section
namespace InfoGeometry.Canonical.RealPartnerProjectiveSeparation

theorem squareMinusOne_eigenvector_zero
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (T : M →ₗ[ℝ] M) (hT : T.comp T = -LinearMap.id)
    (x : M) (c : ℝ) (heigen : T x = c • x) : x = 0 := by
  have hs := congrArg (fun F : M →ₗ[ℝ] M => F x) hT
  change T (T x) = -x at hs
  rw [heigen, map_smul, heigen, smul_smul] at hs
  have hz : (c*c + 1) • x = 0 := by
    rw [add_smul, one_smul, hs]
    exact neg_add_cancel x
  have hpos : 0 < c*c + 1 := by nlinarith [sq_nonneg c]
  exact (smul_eq_zero.mp hz).resolve_left hpos.ne'

section OwnedDoubledCarrier
open InfoGeometry.Krein
open HestenesKramersBridge HestenesRealStructures OperatorDictionary
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
local notation "H₂" => DoubledSpace E

theorem phasePartner_ne_real_smul {x : H₂} (hx : x ≠ 0) (c : ℝ) :
    phasePartner x ≠ c • x := by
  intro h
  have hsq : (phaseAxisK (E := E)).toLinearMap.comp
      (phaseAxisK (E := E)).toLinearMap = -LinearMap.id := by
    apply LinearMap.ext
    intro y
    have h := phaseAxisK_sq_eq_neg_id (E := E)
    have hy := congrArg (fun F : H₂ →L[ℝ] H₂ => F y) h
    simpa [ContinuousLinearMap.comp_apply] using hy
  exact hx (squareMinusOne_eigenvector_zero
    (phaseAxisK (E := E)).toLinearMap hsq x c h)

theorem phasePartner_not_mem_real_line {x : H₂} (hx : x ≠ 0) :
    phasePartner x ∉ Submodule.span ℝ ({x} : Set H₂) := by
  intro h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  exact phasePartner_ne_real_smul hx c hc.symm

theorem kramersSymmetry_ne_real_smul (S : KramersSymmetry (E := E))
    {x : H₂} (hx : x ≠ 0) (c : ℝ) : S.Θ x ≠ c • x := by
  intro h
  have hsq : S.Θ.toLinearMap.comp S.Θ.toLinearMap = -LinearMap.id := by
    apply LinearMap.ext
    intro y
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun F : H₂ →L[ℝ] H₂ => F y) S.square_neg
  exact hx (squareMinusOne_eigenvector_zero S.Θ.toLinearMap hsq x c h)

theorem phasePartner_eigenvalue_of_commuting
    (D : H₂ →L[ℝ] H₂)
    (hcomm : D.comp (phaseAxisK (E := E)) = (phaseAxisK (E := E)).comp D)
    (x : H₂) (a : ℝ) (hx : D x = a • x) :
    D (phasePartner x) = a • phasePartner x := by
  have h := congrArg (fun F : H₂ →L[ℝ] H₂ => F x) hcomm
  change D (phasePartner x) = phasePartner (D x) at h
  rw [hx] at h
  simpa only [phasePartner, map_smul] using h

end OwnedDoubledCarrier
end InfoGeometry.Canonical.RealPartnerProjectiveSeparation
