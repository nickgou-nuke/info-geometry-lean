import DAG.ChiralDiracAnticommutation
import InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit

noncomputable section

namespace InfoGeometry.Canonical.DAGCellDoubledExterior3Bridge

open DAG.ChiralDiracAnticommutation
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit

noncomputable def cellEightEightDoubledExterior3Equiv :
    (Cell 8 8 0 → ℝ) ≃ₗ[ℝ] DoubledExterior3 :=
  (DAG.ChiralDiracAnticommutation.cellEightEightFunctionEquiv).trans
    (LinearEquiv.prodCongr
      exterior3SplitOctonionCoordinateEquiv.symm
      exterior3SplitOctonionCoordinateEquiv.symm)

@[simp] theorem cellEightEightDoubledExterior3Equiv_apply
    (f : Cell 8 8 0 → ℝ) :
    cellEightEightDoubledExterior3Equiv f =
      (exterior3SplitOctonionCoordinateEquiv.symm
        (fun i => f (Cell.zero i)),
       exterior3SplitOctonionCoordinateEquiv.symm
        (fun i => f (Cell.one i))) := by
  rfl

noncomputable def transportCellEnd
    (T : Module.End ℝ (Cell 8 8 0 → ℝ)) :
    Module.End ℝ DoubledExterior3 :=
  (cellEightEightDoubledExterior3Equiv.conjAlgEquiv ℝ) T

theorem transportCellEnd_intertwines
    (T : Module.End ℝ (Cell 8 8 0 → ℝ))
    (x : Cell 8 8 0 → ℝ) :
    transportCellEnd T (cellEightEightDoubledExterior3Equiv x) =
      cellEightEightDoubledExterior3Equiv (T x) := by
  rw [transportCellEnd, LinearEquiv.conjAlgEquiv_apply]
  change cellEightEightDoubledExterior3Equiv
      (T (cellEightEightDoubledExterior3Equiv.symm
        (cellEightEightDoubledExterior3Equiv x))) =
    cellEightEightDoubledExterior3Equiv (T x)
  rw [cellEightEightDoubledExterior3Equiv.symm_apply_apply]

theorem transportCellEnd_mul_intertwines
    (T U : Module.End ℝ (Cell 8 8 0 → ℝ))
    (x : Cell 8 8 0 → ℝ) :
    transportCellEnd (T * U) (cellEightEightDoubledExterior3Equiv x) =
      transportCellEnd T (transportCellEnd U
        (cellEightEightDoubledExterior3Equiv x)) := by
  rw [transportCellEnd_intertwines]
  rw [transportCellEnd_intertwines]
  rw [transportCellEnd_intertwines]
  rfl

theorem transportCellEnd_trace
    (T : Module.End ℝ (Cell 8 8 0 → ℝ)) :
    LinearMap.trace ℝ DoubledExterior3 (transportCellEnd T) =
      LinearMap.trace ℝ (Cell 8 8 0 → ℝ) T := by
  exact LinearMap.trace_conj' T cellEightEightDoubledExterior3Equiv

theorem linearMap_trace_mul_zero_of_anticommute
    {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
    (A B : Module.End ℝ M)
    (h : A * B + B * A = 0) :
    LinearMap.trace ℝ M (A * B) = 0 := by
  have hanti : B * A = -(A * B) := by
    apply eq_neg_of_add_eq_zero_left
    simpa [add_comm] using h
  have htrace : LinearMap.trace ℝ M (B * A) =
      LinearMap.trace ℝ M (A * B) :=
    LinearMap.trace_mul_comm ℝ B A
  rw [hanti] at htrace
  have htrace' : -(LinearMap.trace ℝ M (A * B)) =
      LinearMap.trace ℝ M (A * B) := by
    simpa using htrace
  linarith

theorem transportCellEnd_anticommutation
    (A B : Module.End ℝ (Cell 8 8 0 → ℝ))
    (h : A * B + B * A = 0) :
    transportCellEnd A * transportCellEnd B +
        transportCellEnd B * transportCellEnd A = 0 := by
  change (cellEightEightDoubledExterior3Equiv.conjAlgEquiv ℝ) A *
      (cellEightEightDoubledExterior3Equiv.conjAlgEquiv ℝ) B +
      (cellEightEightDoubledExterior3Equiv.conjAlgEquiv ℝ) B *
        (cellEightEightDoubledExterior3Equiv.conjAlgEquiv ℝ) A = 0
  rw [← map_mul, ← map_mul, ← map_add, h, map_zero]

theorem transportCellEnd_trace_mul_zero_of_anticommute
    (A B : Module.End ℝ (Cell 8 8 0 → ℝ))
    (h : A * B + B * A = 0) :
    LinearMap.trace ℝ DoubledExterior3
      (transportCellEnd A * transportCellEnd B) = 0 := by
  apply linearMap_trace_mul_zero_of_anticommute
  exact transportCellEnd_anticommutation A B h

noncomputable def dagChiralEnd :
    Module.End ℝ (Cell 8 8 0 → ℝ) :=
  (chiralGamma (n0 := 8) (n1 := 8) (n2 := 0)).mulVecLin

noncomputable def dagDiracEnd
    (B1 : Matrix (Fin 8) (Fin 8) ℝ)
    (B2 : Matrix (Fin 8) (Fin 0) ℝ) :
    Module.End ℝ (Cell 8 8 0 → ℝ) :=
  (diracOp B1 B2).mulVecLin

theorem dagChiralEnd_sq :
    dagChiralEnd * dagChiralEnd = 1 := by
  have h := congrArg Matrix.mulVecLin
    (chiralGamma_sq (n0 := 8) (n1 := 8) (n2 := 0))
  simpa [dagChiralEnd, Matrix.mulVecLin_mul] using h

theorem dagChiralEnd_anticommutes_dagDiracEnd
    (B1 : Matrix (Fin 8) (Fin 8) ℝ)
    (B2 : Matrix (Fin 8) (Fin 0) ℝ) :
    dagChiralEnd * dagDiracEnd B1 B2 +
        dagDiracEnd B1 B2 * dagChiralEnd = 0 := by
  have h := congrArg Matrix.mulVecLin
    (dirac_anticommutes_gamma B1 B2)
  simpa [dagChiralEnd, dagDiracEnd, Matrix.mulVecLin_add,
    Matrix.mulVecLin_mul] using h

theorem transported_dagChiralEnd_trace_mul_zero
    (B1 : Matrix (Fin 8) (Fin 8) ℝ)
    (B2 : Matrix (Fin 8) (Fin 0) ℝ) :
    LinearMap.trace ℝ DoubledExterior3
      (transportCellEnd dagChiralEnd *
        transportCellEnd (dagDiracEnd B1 B2)) = 0 := by
  apply transportCellEnd_trace_mul_zero_of_anticommute
  exact dagChiralEnd_anticommutes_dagDiracEnd B1 B2

theorem dagChiralEnd_trace_mul_zero
    (B1 : Matrix (Fin 8) (Fin 8) ℝ)
    (B2 : Matrix (Fin 8) (Fin 0) ℝ) :
    LinearMap.trace ℝ (Cell 8 8 0 → ℝ)
      (dagChiralEnd * dagDiracEnd B1 B2) = 0 := by
  apply linearMap_trace_mul_zero_of_anticommute
  exact dagChiralEnd_anticommutes_dagDiracEnd B1 B2

end InfoGeometry.Canonical.DAGCellDoubledExterior3Bridge
