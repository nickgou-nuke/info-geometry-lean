import InfoGeometry.HodgeCohomology.KreinGreenEnergyTests

namespace InfoGeometry.HodgeCohomology.KreinNilpotentGreen.Tests

open InfoGeometry.Canonical
open HodgeHelmholtzKreinDecomposition HodgeGreenProjectorConstruction Drazin
open HodgeGreenProjectorConstruction.Tests

noncomputable section

def pairing : LinearMap.BilinForm ℝ Triple :=
  let first := LinearMap.fst ℝ ℝ (ℝ × ℝ)
  let second := (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))
  let third := (LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))
  first.smulRight third + second.smulRight second + third.smulRight first

theorem pairing_apply (left right : Triple) :
    pairing left right = left.1 * right.2.2 + left.2.1 * right.2.1 + left.2.2 * right.1 :=
  rfl

theorem pairing_symmetric : pairing.IsSymm := by
  constructor
  intro left right
  simp only [pairing_apply]
  ring

theorem pairing_nondegenerate : pairing.Nondegenerate := by
  constructor <;> intro state orthogonal
  all_goals
    have first : state.1 = 0 := by simpa [pairing_apply] using orthogonal (0, 0, 1)
    have second : state.2.1 = 0 := by simpa [pairing_apply] using orthogonal (0, 1, 0)
    have third : state.2.2 = 0 := by simpa [pairing_apply] using orthogonal (1, 0, 0)
    exact Prod.ext first (Prod.ext second third)

def symmetry (state : Triple) : Triple := (state.2.2, state.2.1, state.1)

example (state : Triple) : symmetry (symmetry state) = state := rfl

example (state : Triple) :
    pairing state (symmetry state) = state.1 ^ 2 + state.2.1 ^ 2 + state.2.2 ^ 2 := by
  simp only [pairing_apply, symmetry]
  ring

example : pairing (1, 0, 1) (1, 0, 1) = 2 ∧
    pairing (1, 0, -1) (1, 0, -1) = -2 := by
  norm_num [pairing_apply]

def codifferential : Module.End ℝ Triple :=
  ((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).smulRight (0, 1, 0)

def system : HodgePacket (R := ℝ) (V := Triple) where
  d := differential
  δ := codifferential
  d_sq := tripleSystem.d_sq
  δ_sq := by
    apply LinearMap.ext
    intro state
    simp [codifferential]
  Δ := differential * codifferential + codifferential * differential
  Δ_def := rfl

theorem adjunction : LinearMap.IsAdjointPair pairing pairing system.d system.δ := by
  intro left right
  simp [pairing_apply, system, differential, codifferential]

theorem laplacian_apply (state : Triple) : system.Δ state = (state.2.2, 0, 0) := by
  simp [system, differential, codifferential, Module.End.mul_apply]

theorem laplacian_square : system.Δ ^ 2 = 0 := by
  apply LinearMap.ext
  intro state
  simp [pow_two, Module.End.mul_apply, laplacian_apply]

theorem green_inverse : IsDrazinInverse system.Δ 0 2 := by
  exact IsDrazinInverse.mk (by simp) (by simp) (by simp [laplacian_square])

def decomposition : HodgePacket.DecompositionPacket (R := ℝ) (V := Triple) :=
  decompositionFromGreen system 0 green_inverse (by simp) (by simp)

example : LinearMap.range decomposition.Pharm = LinearMap.ker (system.Δ ^ 2) :=
  harmonic_projector_range_eq_power_kernel system 0 green_inverse (by simp) (by simp)

theorem generalized_sector_not_harmonic :
    LinearMap.range decomposition.Pharm ≠ LinearMap.ker system.Δ := by
  intro equality
  have membership : (0, 0, 1) ∈ LinearMap.range decomposition.Pharm := by
    refine ⟨(0, 0, 1), ?_⟩
    simp [decomposition, decompositionFromGreen]
  rw [equality] at membership
  have impossible : ((1, 0, 0) : Triple) = 0 := by
    simpa only [LinearMap.mem_ker, laplacian_apply] using membership
  have first := congrArg Prod.fst impossible
  norm_num at first

#print axioms pairing_nondegenerate
#print axioms adjunction
#print axioms laplacian_square
#print axioms green_inverse
#print axioms generalized_sector_not_harmonic

end

end InfoGeometry.HodgeCohomology.KreinNilpotentGreen.Tests
