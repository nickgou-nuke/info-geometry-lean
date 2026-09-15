import InfoGeometry.Canonical.HodgeGreenProjectorConstruction
import InfoGeometry.HodgeCohomology.KreinHodgeObstruction

namespace InfoGeometry.Canonical.HodgeGreenProjectorConstruction.Tests

open HodgeHelmholtzKreinDecomposition Drazin

noncomputable section

abbrev Triple := ℝ × ℝ × ℝ

def differential : Module.End ℝ Triple :=
  ((LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).smulRight (1, 0, 0)

def codifferential : Module.End ℝ Triple :=
  (LinearMap.fst ℝ ℝ (ℝ × ℝ)).smulRight (0, 1, 0)

def tripleSystem : HodgePacket (R := ℝ) (V := Triple) where
  d := differential
  δ := codifferential
  d_sq := by
    apply LinearMap.ext
    intro state
    simp [differential]
  δ_sq := by
    apply LinearMap.ext
    intro state
    simp [codifferential]
  Δ := differential * codifferential + codifferential * differential
  Δ_def := rfl

theorem triple_laplacian_idempotent : tripleSystem.Δ * tripleSystem.Δ = tripleSystem.Δ := by
  apply LinearMap.ext
  intro state
  simp [tripleSystem, differential, codifferential, Module.End.mul_apply]

theorem triple_green_inverse : IsDrazinInverse tripleSystem.Δ tripleSystem.Δ 1 :=
  IsDrazinInverse.of_idempotent triple_laplacian_idempotent

theorem triple_green_commutes_d : tripleSystem.Δ * tripleSystem.d = tripleSystem.d * tripleSystem.Δ := by
  apply LinearMap.ext
  intro state
  simp [tripleSystem, differential, codifferential, Module.End.mul_apply]

theorem triple_green_commutes_cod : tripleSystem.Δ * tripleSystem.δ = tripleSystem.δ * tripleSystem.Δ := by
  apply LinearMap.ext
  intro state
  simp [tripleSystem, differential, codifferential, Module.End.mul_apply]

def tripleDecomposition : HodgePacket.DecompositionPacket (R := ℝ) (V := Triple) :=
  decompositionFromGreen tripleSystem tripleSystem.Δ triple_green_inverse
    triple_green_commutes_d triple_green_commutes_cod

example (state : Triple) : tripleDecomposition.Pex state = (state.1, 0, 0) := by
  simp [tripleDecomposition, decompositionFromGreen, tripleSystem,
    differential, codifferential, Module.End.mul_apply]

example (state : Triple) : tripleDecomposition.Pcoex state = (0, state.2.1, 0) := by
  simp [tripleDecomposition, decompositionFromGreen, tripleSystem,
    differential, codifferential, Module.End.mul_apply]

example (state : Triple) : tripleDecomposition.Pharm state = (0, 0, state.2.2) := by
  rcases state with ⟨first, second, third⟩
  simp [tripleDecomposition, decompositionFromGreen, tripleSystem,
    differential, codifferential, Module.End.mul_apply]

example : LinearMap.range tripleDecomposition.Pharm = LinearMap.ker tripleSystem.Δ :=
  harmonic_projector_range_eq_kernel tripleSystem tripleSystem.Δ
    triple_green_commutes_d triple_green_commutes_cod triple_green_inverse

example (state : Triple) :
    state = tripleDecomposition.Pex state + tripleDecomposition.Pcoex state +
      tripleDecomposition.Pharm state := tripleDecomposition.decompose state

open InfoGeometry.HodgeCohomology.KreinHodgeObstruction

def nullSystem : HodgePacket (R := ℝ) (V := Plane) where
  d := nullDirac.toLinearMap
  δ := nullDirac.toLinearMap
  d_sq := congrArg ContinuousLinearMap.toLinearMap nullDirac_square
  δ_sq := congrArg ContinuousLinearMap.toLinearMap nullDirac_square
  Δ := 0
  Δ_def := by
    have square_zero := congrArg ContinuousLinearMap.toLinearMap nullDirac_square
    change 0 = nullDirac.toLinearMap * nullDirac.toLinearMap +
      nullDirac.toLinearMap * nullDirac.toLinearMap
    change nullDirac.toLinearMap * nullDirac.toLinearMap = 0 at square_zero
    rw [square_zero, add_zero]

def nullDecomposition : HodgePacket.DecompositionPacket (R := ℝ) (V := Plane) :=
  decompositionFromGreen nullSystem 0 (IsDrazinInverse.of_idempotent (by simp [nullSystem]))
    (by simp) (by simp)

example : nullDecomposition.Pex = 0 ∧ nullDecomposition.Pcoex = 0 ∧
    nullDecomposition.Pharm = 1 := by
  simp [nullDecomposition, decompositionFromGreen]

example : LinearMap.range nullDecomposition.Pharm = ⊤ := by
  simp [nullDecomposition, decompositionFromGreen]
  exact LinearMap.range_eq_top.mpr (fun state => ⟨state, rfl⟩)

#print axioms exact_coexact_product_zero
#print axioms exact_projector_idempotent
#print axioms decompositionFromGreen
#print axioms harmonic_projector_eq_drazin
#print axioms exact_component_mem_range
#print axioms coexact_component_mem_range
#print axioms harmonic_component_mem_power_kernel
#print axioms harmonic_projector_range_eq_power_kernel
#print axioms harmonic_projector_range_eq_kernel
#print axioms tripleDecomposition
#print axioms nullDecomposition

end

end InfoGeometry.Canonical.HodgeGreenProjectorConstruction.Tests
