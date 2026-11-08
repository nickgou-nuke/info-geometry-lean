import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import InfoGeometry.Clifford.SplitQ11
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Clifford.SplitQ11PhaseFlip

Mathlib-canonical split `Cl(1,1)` null pair and phase-flip automorphism.

This file works only with the quadratic space `ℝ × ℝ`, its split form
`splitQ11`, and the induced Clifford algebra. It does not mention spacetime,
BdG, DIII, or the Bott tower.
-/

namespace InfoGeometry.Clifford.SplitQ11PhaseFlip

open InfoGeometry.Clifford

/-- The canonical split `Cl(1,1)` algebra. -/
abbrev Alg := CliffordAlgebra splitQ11

/-- The `J` generator of the split `Cl(1,1)` atom. -/
@[rep_depth krein]
noncomputable def jGen : Alg :=
  CliffordAlgebra.ι splitQ11 (1, 0)

/-- The `K` generator of the split `Cl(1,1)` atom. -/
@[rep_depth krein]
noncomputable def kGen : Alg :=
  CliffordAlgebra.ι splitQ11 (0, 1)

/-- The pseudoscalar `ε = JK`. -/
@[rep_depth krein]
noncomputable def epsGen : Alg :=
  jGen * kGen

/-- The lightlike `u_-` vector in the split head factor. -/
@[rep_depth krein]
noncomputable def nullMinusVec : ℝ × ℝ :=
  ((1 / 2 : ℝ), (1 / 2 : ℝ))

/-- The lightlike `u_+` vector in the split head factor. -/
@[rep_depth krein]
noncomputable def nullPlusVec : ℝ × ℝ :=
  ((1 / 2 : ℝ), (-(1 / 2 : ℝ)))

/-- The lifted `u_-` Clifford generator. -/
@[rep_depth krein]
noncomputable def nullMinus : Alg :=
  CliffordAlgebra.ι splitQ11 nullMinusVec

/-- The lifted `u_+` Clifford generator. -/
@[rep_depth krein]
noncomputable def nullPlus : Alg :=
  CliffordAlgebra.ι splitQ11 nullPlusVec

@[rep_depth krein, simp] theorem jGen_sq :
    jGen * jGen = 1 := by
  simp [jGen, splitQ11_apply]

@[rep_depth krein, simp] theorem kGen_sq :
    kGen * kGen = -(1 : Alg) := by
  simp [kGen, splitQ11_apply]

@[rep_depth krein, simp] theorem jGen_mul_kGen_add_swap :
    jGen * kGen + kGen * jGen = 0 := by
  have hpolar : QuadraticMap.polar splitQ11 ((1 : ℝ), 0) ((0 : ℝ), 1) = 0 := by
    simp [QuadraticMap.polar, splitQ11_apply]
  simpa [jGen, kGen, hpolar] using
    (CliffordAlgebra.ι_mul_ι_add_swap
      (Q := splitQ11) ((1 : ℝ), 0) ((0 : ℝ), 1))

@[rep_depth krein, simp] theorem kGen_mul_jGen :
    kGen * jGen = -epsGen := by
  exact eq_neg_of_add_eq_zero_left (by
    simp [epsGen, add_comm, jGen_mul_kGen_add_swap])

@[rep_depth krein, simp] theorem nullMinus_eq_half_jGen_add_kGen :
    nullMinus = (1 / 2 : ℝ) • (jGen + kGen) := by
  have hvec :
      nullMinusVec = (1 / 2 : ℝ) • ((1 : ℝ), 0) + (1 / 2 : ℝ) • ((0 : ℝ), 1) := by
    ext <;> norm_num [nullMinusVec]
  rw [nullMinus, hvec, LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul]
  simp [jGen, kGen, smul_add]

@[rep_depth krein, simp] theorem nullPlus_eq_half_jGen_sub_kGen :
    nullPlus = (1 / 2 : ℝ) • (jGen - kGen) := by
  have hvec :
      nullPlusVec = (1 / 2 : ℝ) • ((1 : ℝ), 0) - (1 / 2 : ℝ) • ((0 : ℝ), 1) := by
    ext <;> norm_num [nullPlusVec]
  rw [nullPlus, hvec, sub_eq_add_neg, LinearMap.map_add, LinearMap.map_smul,
    LinearMap.map_neg, LinearMap.map_smul]
  simp [jGen, kGen, sub_eq_add_neg, smul_add]

@[rep_depth krein, simp] theorem nullMinus_sq :
    nullMinus * nullMinus = 0 := by
  rw [nullMinus, CliffordAlgebra.ι_sq_scalar]
  simp [nullMinusVec, splitQ11_apply]

@[rep_depth krein, simp] theorem nullPlus_sq :
    nullPlus * nullPlus = 0 := by
  rw [nullPlus, CliffordAlgebra.ι_sq_scalar]
  simp [nullPlusVec, splitQ11_apply]

@[rep_depth krein, simp] theorem nullMinus_mul_nullPlus_add_swap :
    nullMinus * nullPlus + nullPlus * nullMinus = 1 := by
  have hpolar : QuadraticMap.polar splitQ11 nullMinusVec nullPlusVec = 1 := by
    simp [QuadraticMap.polar, nullMinusVec, nullPlusVec, splitQ11_apply]
    norm_num
  simpa [nullMinus, nullPlus, hpolar] using
    (CliffordAlgebra.ι_mul_ι_add_swap
      (Q := splitQ11) nullMinusVec nullPlusVec)

/-- Linear involution fixing the `J`-axis and negating the `K`-axis. -/
@[rep_depth krein]
noncomputable def phaseFlipLinearEquiv : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) :=
  LinearEquiv.ofLinear
    { toFun := fun x => (x.1, -x.2)
      map_add' := by
        intro x y
        apply Prod.ext
        · simp
        · simpa using neg_add x.2 y.2
      map_smul' := by
        intro r x
        apply Prod.ext <;> simp }
    { toFun := fun x => (x.1, -x.2)
      map_add' := by
        intro x y
        apply Prod.ext
        · simp
        · simpa using neg_add x.2 y.2
      map_smul' := by
        intro r x
        apply Prod.ext <;> simp }
    (by
      apply LinearMap.ext
      intro x
      apply Prod.ext <;> simp)
    (by
      apply LinearMap.ext
      intro x
      apply Prod.ext <;> simp)

/-- The `K`-axis sign flip as a quadratic-form isometry of `splitQ11`. -/
@[rep_depth krein]
noncomputable def phaseFlip :
    splitQ11.IsometryEquiv splitQ11 where
  __ := phaseFlipLinearEquiv
  map_app' := by
    intro x
    rcases x with ⟨a, b⟩
    simp [phaseFlipLinearEquiv, splitQ11_apply]

@[rep_depth krein, simp] theorem phaseFlip_apply (x : ℝ × ℝ) :
    phaseFlip x = (x.1, -x.2) := rfl

@[rep_depth krein, simp] theorem phaseFlip_apply_nullMinusVec :
    phaseFlip nullMinusVec = nullPlusVec := by
  simp [phaseFlip_apply, nullMinusVec, nullPlusVec]

@[rep_depth krein, simp] theorem phaseFlip_apply_nullPlusVec :
    phaseFlip nullPlusVec = nullMinusVec := by
  simp [phaseFlip_apply, nullMinusVec, nullPlusVec]

/-- Clifford-algebra automorphism induced by the `K`-axis sign flip. -/
@[rep_depth krein]
noncomputable def phaseFlipAlg : Alg ≃ₐ[ℝ] Alg :=
  CliffordAlgebra.equivOfIsometry phaseFlip

@[rep_depth krein, simp] theorem phaseFlip_apply_jGen :
    phaseFlipAlg jGen = jGen := by
  simp [phaseFlipAlg, jGen, phaseFlip_apply]

@[rep_depth krein, simp] theorem phaseFlip_apply_kGen :
    phaseFlipAlg kGen = -kGen := by
  calc
    phaseFlipAlg kGen = CliffordAlgebra.ι splitQ11 (0, (-1 : ℝ)) := by
      simp [phaseFlipAlg, kGen, phaseFlip_apply]
    _ = CliffordAlgebra.ι splitQ11 (-((0, (1 : ℝ)) : ℝ × ℝ)) := by
      congr 1
      ext <;> norm_num
    _ = -(CliffordAlgebra.ι splitQ11 (0, (1 : ℝ))) := by
      simpa using (CliffordAlgebra.ι splitQ11).map_neg ((0, (1 : ℝ)) : ℝ × ℝ)
    _ = -kGen := by rfl

@[rep_depth krein, simp] theorem phaseFlip_apply_epsGen :
    phaseFlipAlg epsGen = -epsGen := by
  unfold epsGen
  simp [phaseFlip_apply_jGen, phaseFlip_apply_kGen]

@[rep_depth krein, simp] theorem phaseFlip_apply_nullMinus :
    phaseFlipAlg nullMinus = nullPlus := by
  simp [phaseFlipAlg, nullMinus, nullPlus, phaseFlip_apply, nullMinusVec, nullPlusVec]

@[rep_depth krein, simp] theorem phaseFlip_apply_nullPlus :
    phaseFlipAlg nullPlus = nullMinus := by
  simp [phaseFlipAlg, nullMinus, nullPlus, phaseFlip_apply, nullMinusVec, nullPlusVec]

end InfoGeometry.Clifford.SplitQ11PhaseFlip
