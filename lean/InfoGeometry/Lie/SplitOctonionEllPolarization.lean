import InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes
import InfoGeometry.Lie.SplitOctonionCliffordAction
import InfoGeometry.Lie.SplitOctonionAnnihilatorDimension
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# The distinguished split-octonion axis as an involutive left action

This owner packages only the operator statement already forced by the
canonical Zorn multiplication: left multiplication by `lUnit` is an
involution, and the existing chiral-null vectors are its `+1` and `-1`
eigenvectors. It makes no exceptional-group or Kantor-pair identification.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllPolarization

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes
open InfoGeometry.Lie.SplitOctonionImaginaryAction

abbrev CZ := CanonicalZorn
abbrev EndCZ := Module.End ℝ CZ

/-- The distinguished hyperbolic generator, regarded as an imaginary split
octonion. -/
def ellImaginary : Imaginary :=
  ⟨lUnit, by simp [mem_imaginary_iff, realZornTrace, lUnit]⟩

/-- The para-complex operator supplied internally by left multiplication with
the distinguished split generator. -/
noncomputable def ellLeftMul : EndCZ :=
  imaginaryLeftMul ellImaginary

@[simp] theorem ellLeftMul_apply (X : CZ) :
    ellLeftMul X = lUnit * X :=
  rfl

/-- Left alternativity and `lUnit² = 1` make the distinguished left action an
involution on the complete eight-dimensional split-octonion carrier. -/
theorem ellLeftMul_sq : ellLeftMul * ellLeftMul = 1 := by
  apply LinearMap.ext
  intro X
  rw [Module.End.mul_apply]
  change lUnit * (lUnit * X) = X
  have h := imaginary_leftMul_self_apply ellImaginary X
  change lUnit * (lUnit * X) = (lUnit * lUnit) * X at h
  rw [h]
  change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul
    (InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul lUnit lUnit) X = X
  rw [l_sq]
  exact one_zMul X

/-- The four existing positive chiral-null vectors belong to the `+1`
eigenspace of the involution. -/
theorem chiralNull_mem_plus_eigenspace (a : Fin 4) :
    chiralNull a 1 ∈ Module.End.eigenspace ellLeftMul 1 := by
  rw [Module.End.mem_eigenspace_iff]
  change lUnit * chiralNull a 1 = (1 : ℝ) • chiralNull a 1
  exact chiralNull_left_ell_eigenvector a 1 (by norm_num)

/-- The four existing negative chiral-null vectors belong to the `-1`
eigenspace of the involution. -/
theorem chiralNull_mem_minus_eigenspace (a : Fin 4) :
    chiralNull a (-1) ∈ Module.End.eigenspace ellLeftMul (-1) := by
  rw [Module.End.mem_eigenspace_iff]
  change lUnit * chiralNull a (-1) = (-1 : ℝ) • chiralNull a (-1)
  exact chiralNull_left_ell_eigenvector a (-1) (by norm_num)

/-! ## The three positive and negative adjoint-root channels -/

/-- Positive root channel in quaternionic direction `a`. -/
noncomputable def rootPlus (a : Fin 3) : CZ :=
  chiralNull a.succ 1

/-- Negative root channel with the sign convention
`(ellBasis - quaternionBasis) / 2`. -/
noncomputable def rootMinus (a : Fin 3) : CZ :=
  -chiralNull a.succ (-1)

/-- The commutator action of the distinguished split axis. -/
noncomputable def ellCommutator : EndCZ where
  toFun X := InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul lUnit X -
    InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul X lUnit
  map_add' X Y := by
    rw [zMul_add_right, zMul_add_left]
    abel
  map_smul' r X := by
    change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul lUnit (r • X) -
        InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul (r • X) lUnit =
      r • (InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul lUnit X -
        InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul X lUnit)
    rw [zMul_smul_right, zMul_smul_left, smul_sub]

@[simp] theorem ellCommutator_apply (X : CZ) :
    ellCommutator X = lUnit * X - X * lUnit :=
  rfl

private theorem chiralNull_right_ell_eigenvector
    (a : Fin 3) (ε : ℝ) (hε : ε ^ 2 = 1) :
    InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul
        (chiralNull a.succ ε) lUnit =
      -ε • chiralNull a.succ ε := by
  have hsmul (r : ℝ) (Z : CZ) :
      r • Z = { a := r * Z.a, b := r * Z.b, x := r • Z.x, y := r • Z.y } := by
    rw [Equiv.smul_def InfoGeometry.Canonical.ZornMatrix.coordEquiv]
    rfl
  have hmem : chiralNull a.succ ε ∈ Imaginary := by
    rw [mem_imaginary_iff]
    fin_cases a <;>
      simp [chiralNull, realZornTrace, ellBasis, quaternionBasis,
        iUnit, jUnit, kQuaternionUnit, lUnit,
        InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul, hsmul,
        realCrossProduct3,
        InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross, smul_eq_mul]
  let X : Imaginary := ⟨chiralNull a.succ ε, hmem⟩
  let L : Imaginary := ⟨lUnit, by
    simp [mem_imaginary_iff, realZornTrace, lUnit]⟩
  have hanti := imaginary_anticommutator_eq L X
  have hpol : imaginaryPolar L X = 0 := by
    unfold L X imaginaryPolar
    fin_cases a <;>
      simp [chiralNull, ellBasis, quaternionBasis, iUnit, jUnit,
        kQuaternionUnit, lUnit,
        InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul, hsmul,
        realCrossProduct3,
        InfoGeometry.Algebra.Zorn.ZornMatrix.detZ,
        InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross,
        smul_eq_mul] <;>
      nlinarith [hε]
  rw [hpol, neg_zero, zero_smul] at hanti
  rw [show L.1 = lUnit by rfl,
    show X.1 = chiralNull a.succ ε by rfl,
    chiralNull_left_ell_eigenvector a.succ ε hε] at hanti
  simpa only [one_smul, neg_smul] using
    eq_neg_of_add_eq_zero_right hanti

/-- Every positive channel has adjoint weight `+2`. -/
theorem ellCommutator_rootPlus (a : Fin 3) :
    ellCommutator (rootPlus a) = (2 : ℝ) • rootPlus a := by
  change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul lUnit
      (chiralNull a.succ 1) -
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul
        (chiralNull a.succ 1) lUnit =
      (2 : ℝ) • chiralNull a.succ 1
  rw [chiralNull_left_ell_eigenvector a.succ 1 (by norm_num),
    chiralNull_right_ell_eigenvector a 1 (by norm_num)]
  module

/-- Every negative channel has adjoint weight `-2`. -/
theorem ellCommutator_rootMinus (a : Fin 3) :
    ellCommutator (rootMinus a) = (-2 : ℝ) • rootMinus a := by
  change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul lUnit
      (-chiralNull a.succ (-1)) -
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul
        (-chiralNull a.succ (-1)) lUnit =
      (-2 : ℝ) • (-chiralNull a.succ (-1))
  rw [show -chiralNull a.succ (-1) = (-1 : ℝ) • chiralNull a.succ (-1) by module,
    zMul_smul_left, zMul_smul_right,
    chiralNull_left_ell_eigenvector a.succ (-1) (by norm_num),
    chiralNull_right_ell_eigenvector a (-1) (by norm_num)]
  module

/-- Positive root channels are square-zero in the split-octonion product. -/
theorem rootPlus_sq (a : Fin 3) : rootPlus a * rootPlus a = 0 := by
  change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul
    (chiralNull a.succ 1) (chiralNull a.succ 1) = 0
  have h : chiralNull a.succ 1 = imaginarySplitPlaneNullPlus a := by
    simp [chiralNull, imaginarySplitPlaneNullPlus]
  rw [h]
  exact imaginarySplitPlaneNullPlus_sq a

/-- Negative root channels are square-zero in the split-octonion product. -/
theorem rootMinus_sq (a : Fin 3) : rootMinus a * rootMinus a = 0 := by
  change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul
    (-chiralNull a.succ (-1)) (-chiralNull a.succ (-1)) = 0
  rw [show -chiralNull a.succ (-1) = (-1 : ℝ) • chiralNull a.succ (-1) by module,
    zMul_smul_left, zMul_smul_right]
  norm_num
  have hc : chiralNull a.succ (-1) = imaginarySplitPlaneNullMinus a := by
    unfold chiralNull imaginarySplitPlaneNullMinus
    module
  rw [hc]
  exact imaginarySplitPlaneNullMinus_sq a

/-! ## The complete real weight basis -/

@[simp] def ellWeightBasis : Fin 8 → CZ
  | 0 => rootMinus 0
  | 1 => rootMinus 1
  | 2 => rootMinus 2
  | 3 => 1
  | 4 => lUnit
  | 5 => rootPlus 0
  | 6 => rootPlus 1
  | 7 => rootPlus 2
  | _ => 0

private theorem canonicalZorn_smul_coordinates (r : ℝ) (Z : CZ) :
    r • Z = { a := r * Z.a, b := r * Z.b, x := r • Z.x, y := r • Z.y } := by
  rw [Equiv.smul_def InfoGeometry.Canonical.ZornMatrix.coordEquiv]
  rfl

set_option maxHeartbeats 1000000 in
theorem ellWeightBasis_linearIndependent :
    LinearIndependent ℝ ellWeightBasis := by
  rw [Fintype.linearIndependent_iff]
  intro g h i
  let e : CZ ≃ₗ[ℝ] (ℝ × ℝ × (Fin 3 → ℝ) × (Fin 3 → ℝ)) :=
    InfoGeometry.Canonical.ZornMatrix.coordEquiv.linearEquiv ℝ
  have he : ∑ j, g j • e (ellWeightBasis j) = 0 := by
    simpa [e] using congrArg e h
  have ha := congrArg (fun C => C.1) he
  have hb := congrArg (fun C => C.2.1) he
  have hx0 := congrArg (fun C => C.2.2.1 0) he
  have hy0 := congrArg (fun C => C.2.2.2 0) he
  have hx1 := congrArg (fun C => C.2.2.1 1) he
  have hy1 := congrArg (fun C => C.2.2.2 1) he
  have hx2 := congrArg (fun C => C.2.2.1 2) he
  have hy2 := congrArg (fun C => C.2.2.2 2) he
  all_goals try
    simp [e, Equiv.linearEquiv, ellWeightBasis, rootPlus, rootMinus,
      chiralNull, ellBasis, quaternionBasis, iUnit, jUnit, kQuaternionUnit,
      lUnit, InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross,
      canonicalZorn_smul_coordinates,
      InfoGeometry.Canonical.ZornMatrix.coordEquiv, Fin.sum_univ_succ]
      at ha hb hx0 hy0 hx1 hy1 hx2 hy2
  fin_cases i
  · have hg : g 0 = 0 := by linarith [ha, hb, hx0, hy0]
    exact hg
  · have hg : g 1 = 0 := by linarith [hx1, hy1, hx2, hy2]
    exact hg
  · have hg : g 2 = 0 := by linarith [hx1, hy1, hx2, hy2]
    exact hg
  · have hg : g 3 = 0 := by linarith [ha, hb, hx0, hy0]
    exact hg
  · have hg : g 4 = 0 := by linarith [ha, hb, hx0, hy0]
    exact hg
  · have hg : g 5 = 0 := by linarith [ha, hb, hx0, hy0]
    exact hg
  · have hg : g 6 = 0 := by linarith [hx1, hy1, hx2, hy2]
    exact hg
  · have hg : g 7 = 0 := by linarith [hx1, hy1, hx2, hy2]
    exact hg

noncomputable def ellWeightBasisReal : Module.Basis (Fin 8) ℝ CZ :=
  Module.Basis.mk ellWeightBasis_linearIndependent (by
    have hcard : Fintype.card (Fin 8) = Module.finrank ℝ CZ := by
      rw [Fintype.card_fin]
      exact canonicalZorn_finrank.symm
    have hspan :=
      ellWeightBasis_linearIndependent.span_eq_top_of_card_eq_finrank hcard
    simp [hspan])

@[simp] theorem ellWeightBasisReal_apply (i : Fin 8) :
    ellWeightBasisReal i = ellWeightBasis i := by
  unfold ellWeightBasisReal
  apply Module.Basis.mk_apply

end InfoGeometry.Lie.SplitOctonionEllPolarization
