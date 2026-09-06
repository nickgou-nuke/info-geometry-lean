import InfoGeometry.Algebra.RealSplitOctZornAlignment

/-!
# Stable `RealSplitOct`/Zorn transport API

The older G₂ closure proofs mixed structure-level operations with overloaded
notation.  This owner exposes the transport laws in the exact application
shapes used by downstream proofs.
-/

namespace InfoGeometry.Canonical.RealSplitOctZornAPI

open InfoGeometry.Algebra.RealSplitOctZornAlignment
open InfoGeometry.Algebra

abbrev Zorn := ZornVectorMatrix ℝ

theorem fromZorn_add_apply (X Y : Zorn) :
    fromZorn (X + Y) = fromZorn X + fromZorn Y :=
  fromZorn_add X Y

theorem fromZorn_smul_apply (r : ℝ) (X : Zorn) :
    fromZorn (r • X) = r • fromZorn X :=
  fromZorn_smul r X

theorem fromZorn_mul_apply (X Y : Zorn) :
    fromZorn (ZornVectorMatrix.mul X Y) = RealSplitOct.mul (fromZorn X) (fromZorn Y) :=
  fromZorn_mul X Y

theorem fromZorn_conj_apply (X : Zorn) :
    fromZorn (ZornVectorMatrix.conj X) =
      RealSplitOct.conj (fromZorn X) :=
  fromZorn_conj X

theorem toZorn_add_apply (X Y : RealSplitOct) :
    toZorn (X + Y) = toZorn X + toZorn Y :=
  toZorn_add X Y

theorem toZorn_smul_apply (r : ℝ) (X : RealSplitOct) :
    toZorn (r • X) = r • toZorn X :=
  toZorn_smul r X

theorem toZorn_mul_apply (X Y : RealSplitOct) :
    toZorn (RealSplitOct.mul X Y) = ZornVectorMatrix.mul (toZorn X) (toZorn Y) :=
  toZorn_mul X Y

theorem toZorn_conj_apply (X : RealSplitOct) :
    toZorn (RealSplitOct.conj X) = ZornVectorMatrix.conj (toZorn X) :=
  toZorn_conj X

end InfoGeometry.Canonical.RealSplitOctZornAPI
