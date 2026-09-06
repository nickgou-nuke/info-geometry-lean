import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix
import InfoGeometry.Canonical.ChiralStokesPauliBasis

noncomputable section

namespace InfoGeometry.Canonical.TwoSheetStokesTopological

open InfoGeometry.Canonical.TwoSheetOperatorCoordinates
open InfoGeometry.Canonical.TwoSheetStokesCoordinates

def operatorStokesContinuousLinearEquiv : M6C ≃L[ℂ] StokesQuad :=
  operatorStokesLinearEquiv.toContinuousLinearEquiv

def operatorStokesHomeomorph : M6C ≃ₜ StokesQuad :=
  operatorStokesContinuousLinearEquiv.toHomeomorph

theorem operatorStokesContinuousLinearEquiv_apply (A : M6C) :
    operatorStokesContinuousLinearEquiv A = operatorStokesLinearEquiv A := rfl

theorem operatorStokesHomeomorph_apply (A : M6C) :
    operatorStokesHomeomorph A = operatorStokesLinearEquiv A := rfl

theorem operatorStokesContinuousLinearEquiv_symm_apply (q : StokesQuad) :
    operatorStokesContinuousLinearEquiv.symm q =
      operatorStokesLinearEquiv.symm q := rfl

theorem operatorStokesHomeomorph_symm_apply (q : StokesQuad) :
    operatorStokesHomeomorph.symm q = operatorStokesLinearEquiv.symm q := rfl

end InfoGeometry.Canonical.TwoSheetStokesTopological
