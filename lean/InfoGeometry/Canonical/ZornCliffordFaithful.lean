/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.CanonicalZornWittRegularBridge
import InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
import InfoGeometry.Clifford.Cl11SplitTowerMatrixEquiv
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Faithfulness of the existing real doubled Zorn Clifford action

The existing Cartesian Witt equivalence and vector/covector duality identify
the native reduced Zorn norm with the unscaled neutral evaluation form.
The existing neutral-to-split isometry and split Clifford matrix classification
then identify its Clifford algebra with `Matrix (Fin 16) (Fin 16) ℝ`.

Simplicity of that matrix algebra proves injectivity of the already defined
`ZornClifford.zornCliffordRepresentation`. Equal dimensions are used only
after injectivity, to prove surjectivity onto the existing doubled-spinor
endomorphism algebra. No new Zorn carrier, multiplication, or gamma map is
introduced, and the left regular map on one Zorn copy is not treated as an
algebra homomorphism.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornCliffordFaithful

open InfoGeometry.Canonical.ZornClifford
open InfoGeometry.Lie.CanonicalZornWittRegularBridge
open InfoGeometry.Lie.SplitOctonionWittVectorCovectorBridge
open InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
open InfoGeometry.Clifford.NeutralPhaseSpaceCore

/-- Compose the existing Zorn/Witt coordinate equivalence with the actual
Witt duality on its second factor. -/
def zornToNeutral :
    ZornMatrix ℝ ≃ₗ[ℝ] Neutral 4 :=
  wittZornEquiv.symm.trans
    ((LinearEquiv.refl ℝ (Fin 4 → ℝ)).prodCongr wittDualityEquiv)

@[simp] theorem zornToNeutral_wittZornEquiv (x p : Fin 4 → ℝ) :
    zornToNeutral (wittZornEquiv (x, p)) = (x, wittDualityEquiv p) := by
  simp only [zornToNeutral, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply]

/-- The existing reduced Zorn norm has exactly the unscaled neutral
normalization: evaluation of the covector on the vector. -/
theorem zornToNeutral_norm (Z : ZornMatrix ℝ) :
    InfoGeometry.Clifford.Qsplit (Fin 4 → ℝ) (zornToNeutral Z) =
      zornNorm Z := by
  obtain ⟨⟨x, p⟩, rfl⟩ := wittZornEquiv.surjective Z
  simpa only [zornToNeutral_wittZornEquiv,
    chevelleyQsplit_eq_neutralForm, canonicalNeutralFormUnscaled_apply,
    zornNorm_apply] using (zornNormFun_wittZornEquiv x p).symm

/-- Native quadratic isometry from canonical real Zorn matrices to the
existing neutral Chevalley space of rank four. -/
def zornToNeutralIsometry :
    (zornNorm (R := ℝ)).IsometryEquiv
      (InfoGeometry.Clifford.Qsplit (Fin 4 → ℝ)) where
  toLinearEquiv := zornToNeutral
  map_app' := zornToNeutral_norm

/-- The Zorn norm is carried to the existing recursive split `(4,4)` form. -/
def zornToSplitIsometry :
    (zornNorm (R := ℝ)).IsometryEquiv
      (InfoGeometry.CliffordTower.Qsplit 4) :=
  zornToNeutralIsometry.trans (neutralToSplitIsometry 4)

/-- Matrix classification obtained by transporting the existing split tower
classification through the proved norm isometry. -/
def zornCliffordMatrixEquiv :
    CliffordAlgebra (zornNorm (R := ℝ)) ≃ₐ[ℝ]
      Matrix (Fin 16) (Fin 16) ℝ :=
  (CliffordAlgebra.equivOfIsometry zornToSplitIsometry).trans
    (InfoGeometry.Clifford.Cl11SplitTowerMatrixEquiv.splitTowerEquivMatrix 4)

/-- The native real Zorn Clifford algebra is simple because its actual
matrix model is simple. -/
theorem zornClifford_isSimpleRing :
    IsSimpleRing (CliffordAlgebra (zornNorm (R := ℝ))) :=
  IsSimpleRing.of_ringEquiv zornCliffordMatrixEquiv.symm.toRingEquiv inferInstance

/-- The already defined doubled real Zorn Clifford representation is faithful
on the full Clifford algebra. This follows from simplicity, not dimension. -/
theorem zornCliffordRepresentation_injective :
    Function.Injective (zornCliffordRepresentation (R := ℝ)) := by
  letI : IsSimpleRing (CliffordAlgebra (zornNorm (R := ℝ))) :=
    zornClifford_isSimpleRing
  letI : Nontrivial (ZornMatrix ℝ) :=
    (ZornMatrix.coordEquiv (R := ℝ)).nontrivial
  exact (zornCliffordRepresentation (R := ℝ)).toRingHom.injective

/-- The native real Zorn carrier has dimension eight by its existing Witt
coordinate equivalence. -/
theorem zorn_finrank : Module.finrank ℝ (ZornMatrix ℝ) = 8 := by
  rw [wittZornEquiv.symm.finrank_eq, Module.finrank_prod]
  norm_num

/-- The existing doubled real spinor carrier has dimension sixteen. -/
theorem diracSpinor_finrank :
    Module.finrank ℝ (DiracSpinor16 (R := ℝ)) = 16 := by
  letI : FiniteDimensional ℝ (ZornMatrix ℝ) := wittZornEquiv.finiteDimensional
  change Module.finrank ℝ (ZornMatrix ℝ × ZornMatrix ℝ) = 16
  rw [Module.finrank_prod, zorn_finrank]

/-- The dimension of the full native Zorn Clifford algebra is certified by
the matrix algebra equivalence. -/
theorem zornClifford_finrank :
    Module.finrank ℝ (CliffordAlgebra (zornNorm (R := ℝ))) = 256 := by
  rw [zornCliffordMatrixEquiv.toLinearEquiv.finrank_eq, Module.finrank_matrix]
  norm_num

/-- The endomorphism algebra of the doubled real carrier has dimension 256. -/
theorem diracEnd_finrank :
    Module.finrank ℝ (Module.End ℝ (DiracSpinor16 (R := ℝ))) = 256 := by
  letI : FiniteDimensional ℝ (ZornMatrix ℝ) := wittZornEquiv.finiteDimensional
  rw [Module.finrank_linearMap, diracSpinor_finrank]

/-- Faithfulness together with the proved equal dimensions makes the existing
representation surjective onto the full endomorphism algebra. -/
theorem zornCliffordRepresentation_surjective :
    Function.Surjective (zornCliffordRepresentation (R := ℝ)) := by
  letI : FiniteDimensional ℝ (CliffordAlgebra (zornNorm (R := ℝ))) :=
    zornCliffordMatrixEquiv.symm.toLinearEquiv.finiteDimensional
  letI : FiniteDimensional ℝ (ZornMatrix ℝ) := wittZornEquiv.finiteDimensional
  have hdim : Module.finrank ℝ (CliffordAlgebra (zornNorm (R := ℝ))) =
      Module.finrank ℝ (Module.End ℝ (DiracSpinor16 (R := ℝ))) :=
    zornClifford_finrank.trans diracEnd_finrank.symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
    (show Function.Injective (zornCliffordRepresentation (R := ℝ)).toLinearMap
      from zornCliffordRepresentation_injective)

/-- The existing doubled Zorn representation itself, upgraded to an algebra
equivalence using its proved injectivity and surjectivity. -/
def zornCliffordEndEquiv :
    CliffordAlgebra (zornNorm (R := ℝ)) ≃ₐ[ℝ]
      Module.End ℝ (DiracSpinor16 (R := ℝ)) :=
  AlgEquiv.ofBijective (zornCliffordRepresentation (R := ℝ))
    ⟨zornCliffordRepresentation_injective, zornCliffordRepresentation_surjective⟩

/-- The upgrade has exactly the already defined action on every algebra
element, not only on Clifford generators. -/
@[simp] theorem zornCliffordEndEquiv_apply
    (a : CliffordAlgebra (zornNorm (R := ℝ))) :
    zornCliffordEndEquiv a = zornCliffordRepresentation a := rfl

end InfoGeometry.Canonical.ZornCliffordFaithful
