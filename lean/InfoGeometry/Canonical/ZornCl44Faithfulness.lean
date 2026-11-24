/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornCliffordRepresentation
import InfoGeometry.Clifford.Cl11SplitTowerMatrixEquiv
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Faithfulness of the real Zorn Clifford representation

The canonical Zorn coordinate equivalence is followed by four explicit
half-sum/half-difference pairs to identify the unnegated Zorn norm with the
existing split-tower quadratic form. The scalar pair is
`((a + b) / 2, (a - b) / 2)` and each spatial pair is
`((x i - y i) / 2, (x i + y i) / 2)`.

The coordinate map in `Lie.SplitOctonionNonmultiplicativity` uses a different
sign convention and identifies the tower form with the negative Zorn norm.
The norm-preserving map here is constructed directly from
`ZornMatrix.coordLinearEquiv`, keeping this finite classification bridge
independent of the nonmultiplicativity owner's larger import graph.

Simplicity of this source algebra makes the already defined Zorn Dirac
representation injective. Both its source and its endomorphism target have
real dimension 256, so this same representation is an algebra equivalence.
Its Clifford-generator action remains the existing Zorn multiplication
action; the matrix classification is used only to prove simplicity and
compute dimension.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornCl44Faithfulness

open InfoGeometry.Canonical.ZornClifford
open InfoGeometry.CliffordTower

/-- A norm-preserving choice of four split pairs on the existing Zorn
coordinate module. -/
private def zornCoordToSplitFour : ZornMatrix.Coord ℝ ≃ₗ[ℝ] SplitSpace 4 where
  toFun c :=
    (((c.1 + c.2.1) / 2, (c.1 - c.2.1) / 2),
      ((c.2.2.1 0 - c.2.2.2 0) / 2, (c.2.2.1 0 + c.2.2.2 0) / 2),
      ((c.2.2.1 1 - c.2.2.2 1) / 2, (c.2.2.1 1 + c.2.2.2 1) / 2),
      ((c.2.2.1 2 - c.2.2.2 2) / 2, (c.2.2.1 2 + c.2.2.2 2) / 2),
      fun _ => (0, 0))
  invFun v :=
    (v.1.1 + v.1.2, v.1.1 - v.1.2,
      ![v.2.1.1 + v.2.1.2,
        v.2.2.1.1 + v.2.2.1.2,
        v.2.2.2.1.1 + v.2.2.2.1.2],
      ![v.2.1.2 - v.2.1.1,
        v.2.2.1.2 - v.2.2.1.1,
        v.2.2.2.1.2 - v.2.2.2.1.1])
  map_add' z w := by
    dsimp
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
    · apply Prod.ext <;> dsimp <;> ring
    · apply Prod.ext <;> dsimp <;> ring
    · apply Prod.ext <;> dsimp <;> ring
    · apply Prod.ext <;> dsimp <;> ring
    · funext i
      nomatch i
  map_smul' r z := by
    dsimp
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
    · apply Prod.ext <;> dsimp <;> ring
    · apply Prod.ext <;> dsimp <;> ring
    · apply Prod.ext <;> dsimp <;> ring
    · apply Prod.ext <;> dsimp <;> ring
    · funext i
      nomatch i
  left_inv z := by
    rcases z with ⟨a, b, x, y⟩
    dsimp
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · ring
    · ring
    · funext i
      fin_cases i <;> dsimp <;> ring
    · funext i
      fin_cases i <;> dsimp <;> ring
  right_inv v := by
    rcases v with ⟨⟨p₀, n₀⟩, ⟨p₁, n₁⟩, ⟨p₂, n₂⟩, ⟨p₃, n₃⟩, tail⟩
    dsimp
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
    · apply Prod.ext <;> dsimp <;> ring
    · apply Prod.ext <;> dsimp <;> ring
    · apply Prod.ext <;> dsimp <;> ring
    · apply Prod.ext <;> dsimp <;> ring
    · funext i
      nomatch i

/-- The norm-preserving Zorn coordinates in the existing four-plane split tower. -/
def zornToSplitFour : ZornMatrix ℝ ≃ₗ[ℝ] SplitSpace 4 :=
  (ZornMatrix.coordLinearEquiv (R := ℝ)).trans zornCoordToSplitFour

@[simp] theorem zornToSplitFour_apply (z : ZornMatrix ℝ) :
    zornToSplitFour z =
      (((z.a + z.b) / 2, (z.a - z.b) / 2),
        ((z.x 0 - z.y 0) / 2, (z.x 0 + z.y 0) / 2),
        ((z.x 1 - z.y 1) / 2, (z.x 1 + z.y 1) / 2),
        ((z.x 2 - z.y 2) / 2, (z.x 2 + z.y 2) / 2),
        fun _ => (0, 0)) := rfl

theorem qsplit_zornToSplitFour (z : ZornMatrix ℝ) :
    Qsplit 4 (zornToSplitFour z) = zornNorm z := by
  rw [zornToSplitFour_apply, Qsplit_succ_apply 3, Qsplit_succ_apply 2,
    Qsplit_succ_apply 1, Qsplit_succ_apply 0, Qsplit_zero_apply]
  simp only [Q11_apply, zornNorm_apply, zornNormFun, ZornMatrix.dot]
  ring

/-- An isometry from the canonical unnegated Zorn norm to four split planes. -/
def zornNormSplitFourIsometry :
    (zornNorm (R := ℝ)).IsometryEquiv (Qsplit 4) where
  toLinearEquiv := zornToSplitFour
  map_app' := qsplit_zornToSplitFour

/-- Transport the existing split-tower classification along the native
norm-preserving Zorn isometry. -/
def zornCliffordMatrixEquiv :
    CliffordAlgebra (zornNorm (R := ℝ)) ≃ₐ[ℝ]
      Matrix (Fin 16) (Fin 16) ℝ :=
  (CliffordAlgebra.equivOfIsometry zornNormSplitFourIsometry).trans
    (InfoGeometry.Clifford.Cl11SplitTowerMatrixEquiv.splitTowerEquivMatrix 4)

/-- The full existing Clifford-algebra representation is faithful. -/
theorem zornCliffordRepresentation_injective :
    Function.Injective (zornCliffordRepresentation (R := ℝ)) := by
  letI : Nontrivial (ZornMatrix ℝ) :=
    Function.Injective.nontrivial
      (ZornMatrix.coordLinearEquiv (R := ℝ)).symm.injective
  letI : IsSimpleRing (CliffordAlgebra (zornNorm (R := ℝ))) :=
    IsSimpleRing.of_ringEquiv zornCliffordMatrixEquiv.toRingEquiv.symm inferInstance
  exact (zornCliffordRepresentation (R := ℝ)).toRingHom.injective

theorem zorn_finrank : Module.finrank ℝ (ZornMatrix ℝ) = 8 := by
  calc
    Module.finrank ℝ (ZornMatrix ℝ) =
        Module.finrank ℝ (ZornMatrix.Coord ℝ) :=
      (ZornMatrix.coordLinearEquiv (R := ℝ)).finrank_eq
    _ = 8 := by
      norm_num [ZornMatrix.Coord, Module.finrank_prod, Module.finrank_pi]

theorem diracSpinor_finrank :
    Module.finrank ℝ (DiracSpinor16 (R := ℝ)) = 16 := by
  letI : FiniteDimensional ℝ (ZornMatrix ℝ) :=
    (ZornMatrix.coordLinearEquiv (R := ℝ)).symm.finiteDimensional
  change Module.finrank ℝ (ZornMatrix ℝ × ZornMatrix ℝ) = 16
  norm_num [Module.finrank_prod, zorn_finrank]

theorem zornClifford_finrank :
    Module.finrank ℝ (CliffordAlgebra (zornNorm (R := ℝ))) = 256 := by
  calc
    Module.finrank ℝ (CliffordAlgebra (zornNorm (R := ℝ))) =
        Module.finrank ℝ (Matrix (Fin 16) (Fin 16) ℝ) :=
      zornCliffordMatrixEquiv.toLinearEquiv.finrank_eq
    _ = 256 := by norm_num [Module.finrank_matrix]

theorem diracEnd_finrank :
    Module.finrank ℝ (Module.End ℝ (DiracSpinor16 (R := ℝ))) = 256 := by
  letI : FiniteDimensional ℝ (ZornMatrix ℝ) :=
    (ZornMatrix.coordLinearEquiv (R := ℝ)).symm.finiteDimensional
  change Module.finrank ℝ
    (DiracSpinor16 (R := ℝ) →ₗ[ℝ] DiracSpinor16 (R := ℝ)) = 256
  norm_num [Module.finrank_linearMap, diracSpinor_finrank]

/-- Equal finite dimensions upgrade the faithful representation to surjectivity. -/
theorem zornCliffordRepresentation_surjective :
    Function.Surjective (zornCliffordRepresentation (R := ℝ)) := by
  letI : FiniteDimensional ℝ (ZornMatrix ℝ) :=
    (ZornMatrix.coordLinearEquiv (R := ℝ)).symm.finiteDimensional
  letI : FiniteDimensional ℝ (CliffordAlgebra (zornNorm (R := ℝ))) :=
    zornCliffordMatrixEquiv.toLinearEquiv.symm.finiteDimensional
  have hdim :
      Module.finrank ℝ (CliffordAlgebra (zornNorm (R := ℝ))) =
        Module.finrank ℝ (Module.End ℝ (DiracSpinor16 (R := ℝ))) :=
    zornClifford_finrank.trans diracEnd_finrank.symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
    (show Function.Injective (zornCliffordRepresentation (R := ℝ)).toLinearMap from
      zornCliffordRepresentation_injective)

/-- The original Zorn Dirac representation, now as an algebra equivalence. -/
def zornCliffordEndEquiv :
    CliffordAlgebra (zornNorm (R := ℝ)) ≃ₐ[ℝ]
      Module.End ℝ (DiracSpinor16 (R := ℝ)) :=
  AlgEquiv.ofBijective (zornCliffordRepresentation (R := ℝ))
    ⟨zornCliffordRepresentation_injective, zornCliffordRepresentation_surjective⟩

@[simp] theorem zornCliffordEndEquiv_apply
    (x : CliffordAlgebra (zornNorm (R := ℝ))) :
    zornCliffordEndEquiv x = zornCliffordRepresentation x := rfl

@[simp] theorem zornCliffordEndEquiv_toAlgHom :
    zornCliffordEndEquiv.toAlgHom = zornCliffordRepresentation (R := ℝ) := rfl

@[simp] theorem zornCliffordEndEquiv_ι (z : ZornMatrix ℝ) :
    zornCliffordEndEquiv (CliffordAlgebra.ι (zornNorm (R := ℝ)) z) =
      diracGammaLinear z :=
  zornCliffordRepresentation_ι z

end InfoGeometry.Canonical.ZornCl44Faithfulness
