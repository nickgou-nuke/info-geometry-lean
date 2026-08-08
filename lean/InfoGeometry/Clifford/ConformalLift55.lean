import InfoGeometry.Clifford.BottPeriodicity

open scoped TensorProduct

/-!
# Split Clifford Bott step: `Cl(4,4)` to `Cl(5,5)`

This file records the honest real split-Bott architecture used in the repo:

`Cl(5,5) ≃ Cl(1,1) ᵍ⊗ Cl(4,4)`

It is not a complexification claim.
-/

namespace InfoGeometry.Clifford.ConformalLift55

open InfoGeometry.CliffordTower
open BottPeriodicity

/-- The repo-owned split `Cl(4,4)` stage. -/
abbrev Cl44 := SplitBottClifford 4

/-- The repo-owned split `Cl(5,5)` stage. -/
abbrev Cl55 := SplitBottClifford 5

/--
The `Cl(4,4) → Cl(5,5)` structural move is the split Bott step, i.e. adjoining
one split `Cl(1,1)` tensor factor over `ℝ`.
-/
noncomputable def cl55_as_split_step :=
  cl55_as_splitBottStep

/-- Owner-equality readback for the `Cl(5,5)` split Bott step. -/
theorem cl55_as_split_step_eq_owner :
    cl55_as_split_step = cl55_as_splitBottStep :=
  rfl

/--
Structural property for a null vector pair spanning the adjoined split `Cl(1,1)`
hyperbolic plane inside `Cl(5,5)`.

The normalization of the pairing is intentionally left as theorem debt; the
file only records the existence shape of the conformal null pair.
-/
structure ConformalNullPair where
  u : Cl55
  v : Cl55
  u_square : u ^ 2 = 0
  v_square : v ^ 2 = 0
  anticomm : u * v + v * u = 1

/--
HONEST THEOREM DEBT.

Construct the conformal null pair inside the extra `Cl(1,1)` factor of
`Cl(5,5) ≃ Cl(4,4) ⊗̂ Cl(1,1)`.

This is not complexification of `Cl(4,4)`.
-/
theorem conformalNullPair_exists :
    Nonempty ConformalNullPair := by
  let e0Vec : SplitSpace 5 := ((1, 1), (0 : SplitSpace 4))
  let eInfVec : SplitSpace 5 := ((1, -1), (0 : SplitSpace 4))
  let u0 : Cl55 := CliffordAlgebra.ι (Qsplit 5) e0Vec
  let v0 : Cl55 := CliffordAlgebra.ι (Qsplit 5) eInfVec
  let u : Cl55 := u0
  let v : Cl55 := (1 / 4 : ℝ) • v0
  have hq0 : Qsplit 5 e0Vec = 0 := by
    change Q11 (1, 1) + Qsplit 4 (0 : SplitSpace 4) = 0
    simp [Q11_apply]
  have hqInf : Qsplit 5 eInfVec = 0 := by
    change Q11 (1, -1) + Qsplit 4 (0 : SplitSpace 4) = 0
    simp [Q11_apply]
  have hu0_sq : u0 * u0 = 0 := by
    simpa [u0, hq0] using (CliffordAlgebra.ι_sq_scalar (Q := Qsplit 5) e0Vec)
  have hv0_sq : v0 * v0 = 0 := by
    simpa [v0, hqInf] using (CliffordAlgebra.ι_sq_scalar (Q := Qsplit 5) eInfVec)
  have hpolar : u0 * v0 + v0 * u0 = (algebraMap ℝ Cl55 4) := by
    have hpolarQ : QuadraticMap.polar (Qsplit 5) e0Vec eInfVec = 4 := by
      dsimp [e0Vec, eInfVec, Qsplit, QuadraticMap.polar]
      norm_num [Q11_apply, hq0, hqInf]
    simpa [u0, v0, hpolarQ] using
      (CliffordAlgebra.ι_mul_ι_add_swap (Q := Qsplit 5) e0Vec eInfVec)
  refine ⟨⟨u, v, ?_, ?_, ?_⟩⟩
  · simpa [u, u0, pow_two] using hu0_sq
  · simpa [v, v0, pow_two, smul_mul_assoc, mul_smul] using hv0_sq
  · have hpair : u * v + v * u = (1 / 4 : ℝ) • (u0 * v0 + v0 * u0) := by
      simp [u, v]
    have hnorm : (1 / 4 : ℝ) • (u0 * v0 + v0 * u0) = 1 := by
      rw [hpolar]
      rw [Algebra.smul_def]
      rw [← map_mul]
      norm_num
    exact hpair.trans hnorm

end InfoGeometry.Clifford.ConformalLift55
