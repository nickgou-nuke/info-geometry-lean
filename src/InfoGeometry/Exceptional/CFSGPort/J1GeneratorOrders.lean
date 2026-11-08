/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

module

public import InfoGeometry.Exceptional.CFSGPort.SporadicGroups

/-!
# J₁ seed orders on the local matrix carrier

The external J₁ simplicity proof uses two generators of orders 2 and 3 whose
product has order 7. This file transports those concrete seed power relations
to the locally owned J₁ carrier through its proved equivalence with the
generated subgroup of `GL (Fin 7) (ZMod 11)`.
-/

public noncomputable section

namespace InfoGeometry.Exceptional.CFSGPort.Sporadic

open Matrix

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem j1Seed1_sq : J1SeedMatrix1 ^ 2 = 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem j1Seed2_cube : J1SeedMatrix2 ^ 3 = 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem j1SeedProduct_seven :
    (J1SeedMatrix1 * J1SeedMatrix2) ^ 7 = 1 := by
  decide +kernel

private theorem j1Seed1_ne_one : J1SeedMatrix1 ≠ 1 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num [J1SeedMatrix1] at h00
  exact (by decide : (0 : ZMod 11) ≠ 1) h00

private theorem j1Seed2_ne_one : J1SeedMatrix2 ≠ 1 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num [J1SeedMatrix2] at h00
  exact (by decide : (5 : ZMod 11) ≠ 1) h00

private theorem j1SeedProduct_ne_one : J1SeedMatrix1 * J1SeedMatrix2 ≠ 1 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num [J1SeedMatrix1, J1SeedMatrix2, Matrix.mul_apply,
    Fin.sum_univ_succ] at h00
  exact (by decide : (251 : ZMod 11) ≠ 1) h00

private noncomputable def j1SeedA [Fact (Nat.Prime 11)] :
    Subgroup.closure
      ({Matrix.GeneralLinearGroup.mkOfDetNeZero J1SeedMatrix1 j1Seed1_det_ne_zero,
        Matrix.GeneralLinearGroup.mkOfDetNeZero J1SeedMatrix2 j1Seed2_det_ne_zero} :
        Set (Matrix.GeneralLinearGroup (Fin 7) (ZMod 11))) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero J1SeedMatrix1 j1Seed1_det_ne_zero,
    Subgroup.subset_closure (Set.mem_insert _ _)⟩

private noncomputable def j1SeedB [Fact (Nat.Prime 11)] :
    Subgroup.closure
      ({Matrix.GeneralLinearGroup.mkOfDetNeZero J1SeedMatrix1 j1Seed1_det_ne_zero,
        Matrix.GeneralLinearGroup.mkOfDetNeZero J1SeedMatrix2 j1Seed2_det_ne_zero} :
        Set (Matrix.GeneralLinearGroup (Fin 7) (ZMod 11))) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero J1SeedMatrix2 j1Seed2_det_ne_zero,
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

/-- First canonical J₁ generator, transported to the local seed carrier. -/
noncomputable def j1GeneratorA [Fact (Nat.Prime 11)] : J1 :=
  (j1GLSeedEquiv).symm j1SeedA

/-- Second canonical J₁ generator, transported to the local seed carrier. -/
noncomputable def j1GeneratorB [Fact (Nat.Prime 11)] : J1 :=
  (j1GLSeedEquiv).symm j1SeedB

/-- The first local J₁ generator maps to the exact first seed operator in
`GL(7, 𝔽₁₁)`. -/
theorem j1GeneratorA_gl_matrix [Fact (Nat.Prime 11)] :
    (j1GLSeedEquiv (j1GeneratorA : J1)).val.val = J1SeedMatrix1 := by
  simp [j1GeneratorA, j1SeedA]

/-- The second local J₁ generator maps to the exact second seed operator in
`GL(7, 𝔽₁₁)`. -/
theorem j1GeneratorB_gl_matrix [Fact (Nat.Prime 11)] :
    (j1GLSeedEquiv (j1GeneratorB : J1)).val.val = J1SeedMatrix2 := by
  simp [j1GeneratorB, j1SeedB]

private theorem j1GLSeedA_sq [Fact (Nat.Prime 11)] : j1SeedA ^ 2 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change J1SeedMatrix1 ^ 2 = 1
  exact j1Seed1_sq

private theorem j1GLSeedB_cube [Fact (Nat.Prime 11)] : j1SeedB ^ 3 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change J1SeedMatrix2 ^ 3 = 1
  exact j1Seed2_cube

private theorem j1GLSeedAB_seven [Fact (Nat.Prime 11)] :
    (j1SeedA * j1SeedB) ^ 7 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change (J1SeedMatrix1 * J1SeedMatrix2) ^ 7 = 1
  exact j1SeedProduct_seven

private theorem j1GLSeedA_ne_one [Fact (Nat.Prime 11)] : j1SeedA ≠ 1 := by
  intro h
  have hv := congrArg Subtype.val h
  have hm := congrArg (fun u : Matrix.GeneralLinearGroup (Fin 7) (ZMod 11) =>
    (u : Matrix (Fin 7) (Fin 7) (ZMod 11))) hv
  exact j1Seed1_ne_one (by simpa [j1SeedA] using hm)

private theorem j1GLSeedB_ne_one [Fact (Nat.Prime 11)] : j1SeedB ≠ 1 := by
  intro h
  have hv := congrArg Subtype.val h
  have hm := congrArg (fun u : Matrix.GeneralLinearGroup (Fin 7) (ZMod 11) =>
    (u : Matrix (Fin 7) (Fin 7) (ZMod 11))) hv
  exact j1Seed2_ne_one (by simpa [j1SeedB] using hm)

private theorem j1GLSeedAB_ne_one [Fact (Nat.Prime 11)] : j1SeedA * j1SeedB ≠ 1 := by
  intro h
  have hv := congrArg Subtype.val h
  have hm := congrArg (fun u : Matrix.GeneralLinearGroup (Fin 7) (ZMod 11) =>
    (u : Matrix (Fin 7) (Fin 7) (ZMod 11))) hv
  exact j1SeedProduct_ne_one (by simpa [j1SeedA, j1SeedB] using hm)

theorem j1GeneratorA_sq [Fact (Nat.Prime 11)] : j1GeneratorA ^ 2 = 1 := by
  apply (j1GLSeedEquiv).injective
  simpa [j1GeneratorA] using j1GLSeedA_sq

theorem j1GeneratorB_cube [Fact (Nat.Prime 11)] : j1GeneratorB ^ 3 = 1 := by
  apply (j1GLSeedEquiv).injective
  simpa [j1GeneratorB] using j1GLSeedB_cube

theorem j1GeneratorAB_seven [Fact (Nat.Prime 11)] :
    (j1GeneratorA * j1GeneratorB) ^ 7 = 1 := by
  apply (j1GLSeedEquiv).injective
  simpa [j1GeneratorA, j1GeneratorB] using j1GLSeedAB_seven

theorem j1GeneratorA_ne_one [Fact (Nat.Prime 11)] : j1GeneratorA ≠ 1 := by
  intro h
  have hSeed : j1SeedA = 1 := by
    simpa [j1GeneratorA] using congrArg j1GLSeedEquiv h
  exact j1GLSeedA_ne_one hSeed

theorem j1GeneratorB_ne_one [Fact (Nat.Prime 11)] : j1GeneratorB ≠ 1 := by
  intro h
  have hSeed : j1SeedB = 1 := by
    simpa [j1GeneratorB] using congrArg j1GLSeedEquiv h
  exact j1GLSeedB_ne_one hSeed

theorem j1GeneratorAB_ne_one [Fact (Nat.Prime 11)] :
    j1GeneratorA * j1GeneratorB ≠ 1 := by
  intro h
  have hSeed : j1SeedA * j1SeedB = 1 := by
    simpa [j1GeneratorA, j1GeneratorB] using congrArg j1GLSeedEquiv h
  exact j1GLSeedAB_ne_one hSeed

theorem j1GeneratorA_order [Fact (Nat.Prime 11)] : orderOf j1GeneratorA = 2 :=
  orderOf_eq_prime j1GeneratorA_sq j1GeneratorA_ne_one

theorem j1GeneratorB_order [Fact (Nat.Prime 11)] : orderOf j1GeneratorB = 3 :=
  orderOf_eq_prime j1GeneratorB_cube j1GeneratorB_ne_one

theorem j1GeneratorAB_order [Fact (Nat.Prime 11)] :
    orderOf (j1GeneratorA * j1GeneratorB) = 7 := by
  let _ : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime j1GeneratorAB_seven j1GeneratorAB_ne_one

/-- The actual J₁ seed operators do not commute: their orders are 2 and 3,
while their product has order 7. -/
theorem j1GeneratorA_not_commute_B [Fact (Nat.Prime 11)] :
    ¬ Commute j1GeneratorA j1GeneratorB := by
  intro hcomm
  have hdiv := hcomm.orderOf_mul_dvd_lcm
  rw [j1GeneratorA_order, j1GeneratorB_order, j1GeneratorAB_order] at hdiv
  norm_num at hdiv

end InfoGeometry.Exceptional.CFSGPort.Sporadic
