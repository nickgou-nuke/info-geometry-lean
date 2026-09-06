import Mathlib
import InfoGeometry.Canonical.RealCl55FiniteModuleEndBridge

/-!
# Finite compact-equivariant Kasparov-cycle certificate

This owner records the genuine finite-dimensional part of the proposed
`SO(4)`-equivariant direction.  The compact group and its unitary action are
parameters: no integration of `𝔤₂(2)` and no identification of a parameter
group with `SO(4)` is inferred here.

The coefficient representation is deliberately explicit.  It is a native
operator-valued `*`-representation datum on the real finite carrier, while
the resulting object is called a *cycle certificate*: this file does not
claim a `KKO` class, a completion, or a non-trivial index.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealCl55SO4EquivariantKasparovCycleBridge

open InfoGeometry.Canonical.RealCl55FiniteModuleEndBridge

abbrev NativeEnd := NativeSpinorCLM
abbrev Mat32 := RealCl55FiniteModuleEndBridge.Mat32

structure NativeStarRepresentation (A : Type*) [Ring A] [StarRing A] where
  pi : A → NativeEnd
  pi_add : ∀ a b, pi (a + b) = pi a + pi b
  pi_mul : ∀ a b, pi (a * b) = (pi a).comp (pi b)
  pi_one : pi 1 = ContinuousLinearMap.id ℝ NativeSpinorCarrier
  pi_star : ∀ a,
    ContinuousLinearMap.adjoint (pi (star a)) = pi a

noncomputable def canonicalMat32StarRepresentation :
    NativeStarRepresentation Mat32 where
  pi := nativeContinuous
  pi_add := nativeContinuous_add
  pi_mul := nativeContinuous_mul
  pi_one := nativeContinuous_one
  pi_star := by
    intro a
    simpa using (nativeContinuous_adjoint_eq_transpose (Matrix.transpose a))

structure NativeUnitaryAction (K : Type*) [Group K] where
  U : K → NativeEnd
  U_one : U 1 = ContinuousLinearMap.id ℝ NativeSpinorCarrier
  U_mul : ∀ g h, U (g * h) = (U g).comp (U h)
  U_adjoint : ∀ g,
    ContinuousLinearMap.adjoint (U g) = U g⁻¹

structure RealCl55SO4EquivariantKasparovCycleDatum
    (K A : Type*) [Group K] [Ring A] [StarRing A] where
  coefficient : NativeStarRepresentation A
  action : NativeUnitaryAction K
  alpha : K → A → A
  alpha_one : ∀ a, alpha 1 a = a
  alpha_mul : ∀ g h a, alpha (g * h) a = alpha g (alpha h a)
  covariance : ∀ g a,
    (action.U g).comp ((coefficient.pi a).comp (action.U g⁻¹)) =
      coefficient.pi (alpha g a)
  commutes_gamma : ∀ g,
    (action.U g).comp nativeChirality =
      nativeChirality.comp (action.U g)
  commutes_F : ∀ g,
    (action.U g).comp nativeNormalizedDirac =
      nativeNormalizedDirac.comp (action.U g)

/-! The native compact orthogonal group carrier used for the restricted direction.

Mathlib supplies the group structure. This owner does not add topology, a Lie
group structure, or a spin double cover. -/
abbrev SO4 := Matrix.specialOrthogonalGroup (Fin 4) ℝ

/-! The identity action gives a concrete finite certificate for any parameter
group. It is a witness of inhabitation, not a nontrivial spin representation,
and it does not assert a `KKO` class. -/

noncomputable def identityUnitaryAction (K : Type*) [Group K] :
    NativeUnitaryAction K where
  U := fun _ => ContinuousLinearMap.id ℝ NativeSpinorCarrier
  U_one := by rfl
  U_mul := by intros; rfl
  U_adjoint := by
    intro g
    simp

noncomputable def identityFiniteCycleDatum (K : Type*) [Group K] :
    RealCl55SO4EquivariantKasparovCycleDatum K Mat32 where
  coefficient := canonicalMat32StarRepresentation
  action := identityUnitaryAction K
  alpha := fun _ a => a
  alpha_one := by intros; rfl
  alpha_mul := by intros; rfl
  covariance := by
    intro g a
    change (ContinuousLinearMap.id ℝ NativeSpinorCarrier).comp
        ((canonicalMat32StarRepresentation.pi a).comp
          (ContinuousLinearMap.id ℝ NativeSpinorCarrier)) =
      canonicalMat32StarRepresentation.pi a
    simp
  commutes_gamma := by
    intro g
    change (ContinuousLinearMap.id ℝ NativeSpinorCarrier).comp nativeChirality =
      nativeChirality.comp (ContinuousLinearMap.id ℝ NativeSpinorCarrier)
    simp
  commutes_F := by
    intro g
    change (ContinuousLinearMap.id ℝ NativeSpinorCarrier).comp nativeNormalizedDirac =
      nativeNormalizedDirac.comp (ContinuousLinearMap.id ℝ NativeSpinorCarrier)
    simp

noncomputable def trivialUnitaryAction : NativeUnitaryAction PUnit :=
  identityUnitaryAction PUnit

noncomputable def trivialFiniteCycleDatum :
    RealCl55SO4EquivariantKasparovCycleDatum PUnit Mat32 :=
  identityFiniteCycleDatum PUnit

theorem trivialFiniteCycleDatum_exists :
    Nonempty (RealCl55SO4EquivariantKasparovCycleDatum PUnit Mat32) := by
  exact ⟨trivialFiniteCycleDatum⟩

noncomputable def trivialSO4FiniteCycleDatum :
    RealCl55SO4EquivariantKasparovCycleDatum SO4 Mat32 :=
  identityFiniteCycleDatum SO4

theorem trivialSO4FiniteCycleDatum_exists :
    Nonempty (RealCl55SO4EquivariantKasparovCycleDatum SO4 Mat32) := by
  exact ⟨trivialSO4FiniteCycleDatum⟩

theorem coefficient_representation_add
    {K A : Type*} [Group K] [Ring A] [StarRing A]
    (D : RealCl55SO4EquivariantKasparovCycleDatum K A)
    (a b : A) :
    D.coefficient.pi (a + b) =
      D.coefficient.pi a + D.coefficient.pi b := by
  exact D.coefficient.pi_add a b

theorem coefficient_representation_mul
    {K A : Type*} [Group K] [Ring A] [StarRing A]
    (D : RealCl55SO4EquivariantKasparovCycleDatum K A)
    (a b : A) :
    D.coefficient.pi (a * b) =
      (D.coefficient.pi a).comp (D.coefficient.pi b) := by
  exact D.coefficient.pi_mul a b

theorem coefficient_representation_star
    {K A : Type*} [Group K] [Ring A] [StarRing A]
    (D : RealCl55SO4EquivariantKasparovCycleDatum K A)
    (a : A) :
    ContinuousLinearMap.adjoint (D.coefficient.pi (star a)) =
      D.coefficient.pi a := by
  exact D.coefficient.pi_star a

theorem unitary_action_inverse
    {K A : Type*} [Group K] [Ring A] [StarRing A]
    (D : RealCl55SO4EquivariantKasparovCycleDatum K A)
    (g : K) :
    ContinuousLinearMap.adjoint (D.action.U g) = D.action.U g⁻¹ := by
  exact D.action.U_adjoint g

theorem unitary_action_comp_inverse
    {K A : Type*} [Group K] [Ring A] [StarRing A]
    (D : RealCl55SO4EquivariantKasparovCycleDatum K A) (g : K) :
    (D.action.U g).comp (D.action.U g⁻¹) =
      ContinuousLinearMap.id ℝ NativeSpinorCarrier := by
  rw [← D.action.U_mul g g⁻¹, mul_inv_cancel g, D.action.U_one]

theorem unitary_action_inverse_comp
    {K A : Type*} [Group K] [Ring A] [StarRing A]
    (D : RealCl55SO4EquivariantKasparovCycleDatum K A) (g : K) :
    (D.action.U g⁻¹).comp (D.action.U g) =
      ContinuousLinearMap.id ℝ NativeSpinorCarrier := by
  rw [← D.action.U_mul g⁻¹ g, inv_mul_cancel, D.action.U_one]

theorem normalized_dirac_is_self_adjoint :
    ContinuousLinearMap.adjoint nativeNormalizedDirac =
      nativeNormalizedDirac := by
  exact nativeNormalizedDirac_hilbert_self_adjoint

theorem normalized_dirac_is_odd :
    nativeChirality.comp nativeNormalizedDirac +
        nativeNormalizedDirac.comp nativeChirality = 0 := by
  exact nativeNormalizedDirac_anticomm_chirality

theorem normalized_dirac_defect_is_compact :
    IsCompactOperator
      (nativeNormalizedDirac.comp nativeNormalizedDirac -
        ContinuousLinearMap.id ℝ NativeSpinorCarrier) := by
  have hF2 : IsCompactOperator
      (nativeNormalizedDirac.comp nativeNormalizedDirac) :=
    nativeNormalizedDirac_is_compact_operator.clm_comp nativeNormalizedDirac
  have hI : IsCompactOperator
      (ContinuousLinearMap.id ℝ NativeSpinorCarrier) := by
    rw [← nativeContinuous_one]
    exact nativeContinuous_is_compact_operator (1 : Mat32)
  exact hF2.sub hI

theorem normalized_dirac_is_compact :
    IsCompactOperator nativeNormalizedDirac := by
  exact nativeNormalizedDirac_is_compact_operator

theorem kasparov_defect_compact_after_coefficient
    {K A : Type*} [Group K] [Ring A] [StarRing A]
    (D : RealCl55SO4EquivariantKasparovCycleDatum K A) (a : A) :
    IsCompactOperator
      ((nativeNormalizedDirac.comp nativeNormalizedDirac -
        ContinuousLinearMap.id ℝ NativeSpinorCarrier).comp
          (D.coefficient.pi a)) := by
         exact normalized_dirac_defect_is_compact.comp_clm (D.coefficient.pi a)

theorem kasparov_commutator_compact_after_coefficient
    {K A : Type*} [Group K] [Ring A] [StarRing A]
    (D : RealCl55SO4EquivariantKasparovCycleDatum K A) (a : A) :
    IsCompactOperator
      (nativeNormalizedDirac.comp (D.coefficient.pi a) -
        (D.coefficient.pi a).comp nativeNormalizedDirac) := by
  exact (normalized_dirac_is_compact.comp_clm (D.coefficient.pi a)).sub
    (normalized_dirac_is_compact.clm_comp (D.coefficient.pi a))

theorem equivariant_cycle_gamma_covariance
    {K A : Type*} [Group K] [Ring A] [StarRing A]
    (D : RealCl55SO4EquivariantKasparovCycleDatum K A) (g : K) :
    (D.action.U g).comp nativeChirality =
      nativeChirality.comp (D.action.U g) := by
  exact D.commutes_gamma g

theorem equivariant_cycle_F_covariance
    {K A : Type*} [Group K] [Ring A] [StarRing A]
    (D : RealCl55SO4EquivariantKasparovCycleDatum K A) (g : K) :
    (D.action.U g).comp nativeNormalizedDirac =
      nativeNormalizedDirac.comp (D.action.U g) := by
  exact D.commutes_F g

theorem equivariant_cycle_coefficient_covariance
    {K A : Type*} [Group K] [Ring A] [StarRing A]
    (D : RealCl55SO4EquivariantKasparovCycleDatum K A)
    (g : K) (a : A) :
    (D.action.U g).comp ((D.coefficient.pi a).comp (D.action.U g⁻¹)) =
      D.coefficient.pi (D.alpha g a) := by
  exact D.covariance g a

theorem equivariant_cycle_coefficient_covariance_comp
    {K A : Type*} [Group K] [Ring A] [StarRing A]
    (D : RealCl55SO4EquivariantKasparovCycleDatum K A)
    (g : K) (a : A) :
    (D.action.U g).comp (D.coefficient.pi a) =
      (D.coefficient.pi (D.alpha g a)).comp (D.action.U g) := by
  apply ContinuousLinearMap.ext
  intro x
  have hcov := D.covariance g a
  have hinv := unitary_action_inverse_comp D g
  have harg : D.action.U g⁻¹ ((D.action.U g) x) = x := by
    have harg' := congrArg (fun T => T x) hinv
    simpa [ContinuousLinearMap.comp_apply] using harg'
  have h := congrArg (fun T => T ((D.action.U g) x)) hcov
  simpa [ContinuousLinearMap.comp_apply, harg] using h

end InfoGeometry.Canonical.RealCl55SO4EquivariantKasparovCycleBridge
