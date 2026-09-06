import InfoGeometry.Lie.CanonicalZornSemisimple
import InfoGeometry.Lie.MathlibBackportCartanCriterion
import InfoGeometry.Lie.CanonicalZornCartanRootSystem
import InfoGeometry.Lie.CanonicalZornMathlibBridge
import Mathlib.FieldTheory.Finiteness

/-!
# Native semisimplicity and Killing-form bridge for canonical Zorn derivations

The abelian-ideal argument is owned by `CanonicalZornSemisimple`.  This file
only installs the resulting radical instance and exposes the pinned-cache
compatible Cartan-criterion consequence.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornIsKilling

open InfoGeometry.Lie.CanonicalZornCartanRootSystem
open InfoGeometry.Lie.CanonicalZornSemisimple

abbrev Der := CanonicalZornMathlibBridge.Der
abbrev Cartan := InfoGeometry.Lie.SplitOctonionAxialCartanErlangen.axialCartanLieSubalgebra

instance der_hasTrivialRadical : LieAlgebra.HasTrivialRadical ℝ Der := by
  rw [LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals]
  intro I hI
  letI : IsLieAbelian I := hI
  exact InfoGeometry.Lie.CanonicalZornSemisimple.no_nonzero_abelian_ideal I

instance der_isKilling : LieAlgebra.IsKilling ℝ Der := by
  letI : IsNoetherian ℝ Der := (IsNoetherian.iff_fg).2 inferInstance
  exact inferInstance

noncomputable def canonicalZornRootSystem :
    RootPairing (Cartan : LieSubalgebra ℝ Der).root
      ℝ (Module.Dual ℝ Cartan) Cartan :=
  letI : LieSubalgebra.IsCartanSubalgebra
      (Cartan : LieSubalgebra ℝ Der) :=
    InfoGeometry.Lie.CanonicalZornMathlibBridge.axialCartan_isCartanSubalgebra
  letI : LieModule.IsTriangularizable ℝ Cartan Der :=
    InfoGeometry.Lie.CanonicalZornMathlibBridge.cartanIsTriangularizable
  LieAlgebra.IsKilling.rootSystem
    (Cartan : LieSubalgebra ℝ Der)

end InfoGeometry.Lie.CanonicalZornIsKilling
