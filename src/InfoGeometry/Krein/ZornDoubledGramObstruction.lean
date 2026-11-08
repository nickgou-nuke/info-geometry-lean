/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.SplitOctonionZornRegularH4Bridge
import InfoGeometry.Canonical.SplitOctonion1331ExteriorDiracSouriauBridge
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

/-!
# The actual Zorn-to-doubled map's Gram coordinates

Ground-truth contract: expand the existing doubled Krein form along the existing
`zornToDoubleKrein`. Its coordinates are those of `fockBdGEquiv.symm` in
`exterior3PeirceBasis`, not an unproved identification with another Peirce map.
The first four coordinates enter positively and the last four negatively.
No split-octonion norm isometry is asserted.
-/

noncomputable section

open InfoGeometry.Canonical.MajoranaKitaevSpinor8DClifford
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner
open InfoGeometry.Canonical.RealifiedDoubledKreinHodgeBridge

namespace InfoGeometry.Krein.MajoranaBdGSheetBridge

theorem nambuDoubledEquiv_kreinForm (x y : Vec8R) :
    kreinForm (E := E4) (nambuDoubledEquiv x) (nambuDoubledEquiv y) =
      (∑ i : Fin 4, x ⟨i.val, by omega⟩ * y ⟨i.val, by omega⟩) -
        ∑ i : Fin 4, x ⟨i.val + 4, by omega⟩ * y ⟨i.val + 4, by omega⟩ := by
  rw [nambuDoubledEquiv_apply, nambuDoubledEquiv_apply, kreinForm_apply]
  simp [EuclideanSpace.inner_toLp_toLp, dotProduct, mul_comm]

end InfoGeometry.Krein.MajoranaBdGSheetBridge

namespace InfoGeometry.Krein.SplitOctonionZornRegularH4Bridge

open InfoGeometry.Krein.MajoranaBdGSheetBridge

theorem zornToDoubleKrein_fock (ψ : InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.Exterior3) :
    zornToDoubleKrein (fockBdGEquiv ψ) =
      nambuDoubledEquiv (exterior3PeirceBasis.equivFun ψ) := by
  simp only [zornToDoubleKrein, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

theorem zornToDoubleKrein_kreinForm (X Y : CZ) :
    kreinForm (E := E4) (zornToDoubleKrein X) (zornToDoubleKrein Y) =
      (∑ i : Fin 4,
        exterior3PeirceBasis.equivFun (fockBdGEquiv.symm X) ⟨i.val, by omega⟩ *
        exterior3PeirceBasis.equivFun (fockBdGEquiv.symm Y) ⟨i.val, by omega⟩) -
      ∑ i : Fin 4,
        exterior3PeirceBasis.equivFun (fockBdGEquiv.symm X) ⟨i.val + 4, by omega⟩ *
        exterior3PeirceBasis.equivFun (fockBdGEquiv.symm Y) ⟨i.val + 4, by omega⟩ := by
  exact nambuDoubledEquiv_kreinForm _ _

theorem zornToDoubleKrein_fock_basis_zero :
    zornToDoubleKrein (fockBdGEquiv (exterior3PeirceBasis 0)) =
      nambuDoubledEquiv (Pi.single 0 1) := by
  rw [zornToDoubleKrein_fock]
  congr 1
  ext i
  simp [Pi.single_apply, eq_comm]

theorem zornToDoubleKrein_fock_vacuum_krein_self :
    kreinForm (E := E4) (zornToDoubleKrein (fockBdGEquiv (1 : InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.Exterior3)))
      (zornToDoubleKrein (fockBdGEquiv (1 : InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.Exterior3))) = 1 := by
  rw [← InfoGeometry.Canonical.SplitOctonion1331ExteriorDiracSouriauBridge.exterior3PeirceBasis_zero,
    zornToDoubleKrein_fock_basis_zero, nambuDoubledEquiv_kreinForm]
  norm_num [Fin.sum_univ_four, Pi.single_apply]

open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

theorem zornToDoubleKrein_uPlus_krein_self :
    kreinForm (E := E4) (zornToDoubleKrein uPlus) (zornToDoubleKrein uPlus) = 1 := by
  simpa only [fockBdGEquiv_apply, fockToZorn_one] using
    zornToDoubleKrein_fock_vacuum_krein_self

theorem native_uPlus_norm_zero :
    InfoGeometry.Algebra.ZornVectorMatrix.norm (canonicalVectorEquiv uPlus) = 0 := by
  norm_num [InfoGeometry.Algebra.ZornVectorMatrix.norm,
    InfoGeometry.Algebra.ZornVec3.dot, Fin.sum_univ_three,
    canonicalVectorEquiv_apply, uPlus,
    InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit]

/-- The actual carrier equivalence does not preserve the split norm. -/
theorem zornToDoubleKrein_not_norm_isometry :
    ¬ (∀ X : CZ,
      kreinForm (E := E4) (zornToDoubleKrein X) (zornToDoubleKrein X) =
        InfoGeometry.Algebra.ZornVectorMatrix.norm (canonicalVectorEquiv X)) := by
  intro h
  have hbad := h uPlus
  rw [zornToDoubleKrein_uPlus_krein_self, native_uPlus_norm_zero] at hbad
  norm_num at hbad

end InfoGeometry.Krein.SplitOctonionZornRegularH4Bridge
