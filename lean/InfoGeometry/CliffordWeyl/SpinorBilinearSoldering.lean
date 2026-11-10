/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.KreinDiracKasparovSpinorBilinear
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Basic.Complex.Basic

namespace InfoGeometry.CliffordWeyl.SpinorBilinearSoldering

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem spinorBilinearSoldering_exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

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

variable {Scalar Index : Type*} [Ring Scalar] [StarRing Scalar] [Fintype Index]

def diracRow (metric : Matrix Index Index Scalar) (spinor : Index → Scalar) : Index → Scalar :=
  star spinor ᵥ* metric

def solder (metric : Matrix Index Index Scalar) (left right : Index → Scalar) :
    Matrix Index Index Scalar :=
  vecMulVec left (diracRow metric right)

def bilinear (metric operator : Matrix Index Index Scalar) (left right : Index → Scalar) : Scalar :=
  diracRow metric left ⬝ᵥ (operator *ᵥ right)

variable {Channel : Type*}

theorem solder_basis_reconstruction [Fintype Channel]
    (basis : Module.Basis Channel Scalar (Matrix Index Index Scalar))
    (metric : Matrix Index Index Scalar) (left right : Index → Scalar) :
    ∑ channel, basis.repr (solder metric left right) channel • basis channel =
      solder metric left right :=
  basis.sum_repr _

variable {Scalar : Type*} [CommRing Scalar] [StarRing Scalar]

theorem solder_trace_readout
    (metric operator : Matrix Index Index Scalar)
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
