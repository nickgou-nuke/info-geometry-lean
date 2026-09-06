import InfoGeometry.QuantumAlgebra.ThreePlaneChiralCarrier

/-!
# Six-generator chiral multiplication re-export

The canonical multiplication table is owned by `ThreePlaneChiralCarrier`.
This module provides stable six-generator names without duplicating the Zorn
carrier or reproving its closure laws.
-/

namespace InfoGeometry.QuantumAlgebra.SixGeneratorChiralMultiplication

open InfoGeometry.QuantumAlgebra.ThreePlaneChiralCarrier
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Canonical.ZornVectorMatrixExplicit

theorem upper_upper_mul_basis (i j : Fin 3) :
    zornMul (upperChiralBasis i) (upperChiralBasis j) =
      lowerVectorZorn
        (cross3 (InfoGeometry.Algebra.ZornMatrix.Vec3.basis i)
          (InfoGeometry.Algebra.ZornMatrix.Vec3.basis j)) :=
  upperChiralBasis_mul_upperChiralBasis i j

theorem lower_lower_mul_basis (i j : Fin 3) :
    zornMul (lowerChiralBasis i) (lowerChiralBasis j) =
      upperVectorZorn
        (-(cross3 (InfoGeometry.Algebra.ZornMatrix.Vec3.basis i)
          (InfoGeometry.Algebra.ZornMatrix.Vec3.basis j))) :=
  lowerChiralBasis_mul_lowerChiralBasis i j

theorem upper_lower_mul_basis (i j : Fin 3) :
    zornMul (upperChiralBasis i) (lowerChiralBasis j) =
      zornMk
        (dot3 (InfoGeometry.Algebra.ZornMatrix.Vec3.basis i)
          (InfoGeometry.Algebra.ZornMatrix.Vec3.basis j)) 0 0 0 :=
  upperChiralBasis_mul_lowerChiralBasis i j

theorem lower_upper_mul_basis (i j : Fin 3) :
    zornMul (lowerChiralBasis i) (upperChiralBasis j) =
      zornMk 0
        (dot3 (InfoGeometry.Algebra.ZornMatrix.Vec3.basis i)
          (InfoGeometry.Algebra.ZornMatrix.Vec3.basis j)) 0 0 :=
  lowerChiralBasis_mul_upperChiralBasis i j

theorem upper_upper_antisymm (i j : Fin 3) :
    zornMul (upperChiralBasis i) (upperChiralBasis j) =
      -zornMul (upperChiralBasis j) (upperChiralBasis i) :=
  upperChiralBasis_mul_upperChiralBasis_antisymm i j

theorem lower_lower_antisymm (i j : Fin 3) :
    zornMul (lowerChiralBasis i) (lowerChiralBasis j) =
      -zornMul (lowerChiralBasis j) (lowerChiralBasis i) :=
  lowerChiralBasis_mul_lowerChiralBasis_antisymm i j

theorem triple_upper_contraction (i j k : Fin 3) :
    zornMul (zornMul (upperChiralBasis i) (upperChiralBasis j))
        (upperChiralBasis k) =
      zornMk 0
        (dot3 (cross3 (InfoGeometry.Algebra.ZornMatrix.Vec3.basis i)
          (InfoGeometry.Algebra.ZornMatrix.Vec3.basis j))
          (InfoGeometry.Algebra.ZornMatrix.Vec3.basis k)) 0 0 :=
  upperChiralBasis_triple_left i j k

theorem triple_lower_contraction (i j k : Fin 3) :
    zornMul (zornMul (lowerChiralBasis i) (lowerChiralBasis j))
        (lowerChiralBasis k) =
      zornMk
        (dot3 (-(cross3 (InfoGeometry.Algebra.ZornMatrix.Vec3.basis i)
          (InfoGeometry.Algebra.ZornMatrix.Vec3.basis j)))
          (InfoGeometry.Algebra.ZornMatrix.Vec3.basis k)) 0 0 0 :=
  lowerChiralBasis_triple_left i j k

theorem fourfold_upper_saturation (i j k l : Fin 3) :
    zornMul
        (zornMul (zornMul (upperChiralBasis i) (upperChiralBasis j))
          (upperChiralBasis k)) (upperChiralBasis l) =
      zornMk 0 0 0 0 :=
  upperChiralBasis_fourfold_left i j k l

theorem fourfold_lower_saturation (i j k l : Fin 3) :
    zornMul
        (zornMul (zornMul (lowerChiralBasis i) (lowerChiralBasis j))
          (lowerChiralBasis k)) (lowerChiralBasis l) =
      zornMk 0 0 0 0 :=
  lowerChiralBasis_fourfold_left i j k l

end InfoGeometry.QuantumAlgebra.SixGeneratorChiralMultiplication
