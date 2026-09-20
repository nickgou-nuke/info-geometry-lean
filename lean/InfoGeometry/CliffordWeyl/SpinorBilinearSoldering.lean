import InfoGeometry.Physics.KreinDiracKasparovSpinorBilinear
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Data.Complex.Basic

namespace InfoGeometry.CliffordWeyl.SpinorBilinearSoldering

section AdjointIdeals

variable {Carrier : Type*} [Ring Carrier] [StarRing Carrier]
variable (krein : InfoGeometry.Physics.KasparovKreinData Carrier)

def idealBilinear (left right : Carrier) : Carrier := left * krein.diracAdjoint right

theorem adjoint_exchanges_support (projection spinor : Carrier)
    (support : spinor * projection = spinor) :
    krein.diracAdjoint projection * krein.diracAdjoint spinor = krein.diracAdjoint spinor := by
  rw [← krein.diracAdjoint_mul, support]

theorem adjoint_support_iff (projection spinor : Carrier) :
    spinor * projection = spinor ↔
      krein.diracAdjoint projection * krein.diracAdjoint spinor = krein.diracAdjoint spinor := by
  constructor
  · exact adjoint_exchanges_support krein projection spinor
  · intro support
    have reflected := congrArg krein.diracAdjoint support
    simpa only [krein.diracAdjoint_mul, krein.diracAdjoint_involution] using reflected

theorem adjoint_idealBilinear (left right : Carrier) :
    krein.diracAdjoint (idealBilinear krein left right) = idealBilinear krein right left := by
  simp only [idealBilinear, krein.diracAdjoint_mul, krein.diracAdjoint_involution]

end AdjointIdeals

section FiniteSpinors

open Matrix

variable {Scalar Index : Type*} [CommRing Scalar] [StarRing Scalar] [Fintype Index]

def diracRow (metric : Matrix Index Index Scalar) (spinor : Index → Scalar) : Index → Scalar :=
  star spinor ᵥ* metric

def solder (metric : Matrix Index Index Scalar) (left right : Index → Scalar) :
    Matrix Index Index Scalar :=
  vecMulVec left (diracRow metric right)

def bilinear (metric operator : Matrix Index Index Scalar) (left right : Index → Scalar) : Scalar :=
  diracRow metric left ⬝ᵥ (operator *ᵥ right)

theorem solder_trace_readout (metric operator : Matrix Index Index Scalar)
    (left right : Index → Scalar) :
    trace (operator * solder metric left right) = bilinear metric operator right left := by
  rw [solder, mul_vecMulVec, trace_vecMulVec]
  exact dotProduct_comm _ _

theorem solder_fierz_product (metric : Matrix Index Index Scalar)
    (first second third fourth : Index → Scalar) :
    solder metric first second * solder metric third fourth =
      (diracRow metric second ⬝ᵥ third) • solder metric first fourth := by
  simp only [solder, vecMulVec_mul_vecMulVec, vecMulVec_smul]

theorem solder_quadratic (metric : Matrix Index Index Scalar) (spinor : Index → Scalar) :
    solder metric spinor spinor * solder metric spinor spinor =
      (diracRow metric spinor ⬝ᵥ spinor) • solder metric spinor spinor :=
  solder_fierz_product metric spinor spinor spinor spinor

variable {Channel : Type*} [Fintype Channel]

theorem solder_basis_reconstruction
    (basis : Module.Basis Channel Scalar (Matrix Index Index Scalar))
    (metric : Matrix Index Index Scalar) (left right : Index → Scalar) :
    ∑ channel, basis.repr (solder metric left right) channel • basis channel =
      solder metric left right :=
  basis.sum_repr _

theorem fierz_coefficient_relation
    (basis : Module.Basis Channel Scalar (Matrix Index Index Scalar))
    (metric : Matrix Index Index Scalar) (first second third fourth : Index → Scalar)
    (channel : Channel) :
    basis.repr (solder metric first second * solder metric third fourth) channel =
      (diracRow metric second ⬝ᵥ third) *
        basis.repr (solder metric first fourth) channel := by
  rw [solder_fierz_product, map_smul]
  rfl

end FiniteSpinors

end InfoGeometry.CliffordWeyl.SpinorBilinearSoldering
