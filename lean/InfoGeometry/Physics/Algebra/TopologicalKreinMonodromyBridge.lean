import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.Algebra.TopologicalBraidMonodromyOperator

/-!
# Topological Krein monodromy bridge

This owner packages the bounded square-zero monodromy lane into the existing
Krein-adjoint calculus.  It proves only transport of the self-adjointness
property through the scalar-plus-nilpotent operator and its unipotent shadow.
It does not introduce a spectral triple, KMS analyticity, or any unitary
one-parameter group.
-/

namespace InfoGeometry.Physics.Algebra

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The scalar-plus-nilpotent monodromy operator as a bounded endomorphism. -/
def scalarJordanMonodromy (M : ContinuousMonodromyOperator H) : H →L[ℝ] H :=
  M.lambda • (1 : H →L[ℝ] H) + M.N

omit [CompleteSpace H] in
theorem continuous_scalarJordanMonodromy_data :
    Continuous (fun p : ℝ × (H →L[ℝ] H) =>
      p.1 • (1 : H →L[ℝ] H) + p.2) := by
  refine Continuous.add ?_ continuous_snd
  exact Continuous.smul continuous_fst continuous_const

theorem scalarJordanMonodromy_krein_self_adjoint
    (M : ContinuousMonodromyOperator H)
    (hN : InfoGeometry.Krein.KreinSpace.IsKreinSelfAdjoint (H := H) M.N) :
    InfoGeometry.Krein.KreinSpace.IsKreinSelfAdjoint (H := H) (scalarJordanMonodromy M) := by
  dsimp [InfoGeometry.Krein.KreinSpace.IsKreinSelfAdjoint, scalarJordanMonodromy]
  rw [InfoGeometry.Krein.KreinSpace.kreinAdjoint_add,
    InfoGeometry.Krein.KreinSpace.kreinAdjoint_smul]
  have hid : InfoGeometry.Krein.KreinSpace.kreinAdjoint (1 : H →L[ℝ] H) = 1 := by
    exact InfoGeometry.Krein.KreinSpace.kreinAdjoint_id (H := H)
  rw [hid, hN]

/-- The unipotent shadow is Krein-self-adjoint whenever the nilpotent part is. -/
theorem continuousUnipotentFlow_krein_self_adjoint
    (M : ContinuousMonodromyOperator H)
    (hN : InfoGeometry.Krein.KreinSpace.IsKreinSelfAdjoint (H := H) M.N)
    (t : ℝ) :
    InfoGeometry.Krein.KreinSpace.IsKreinSelfAdjoint (H := H) (continuousUnipotentFlow M t) := by
  dsimp [InfoGeometry.Krein.KreinSpace.IsKreinSelfAdjoint, continuousUnipotentFlow]
  rw [InfoGeometry.Krein.KreinSpace.kreinAdjoint_add,
    InfoGeometry.Krein.KreinSpace.kreinAdjoint_smul]
  have hid : InfoGeometry.Krein.KreinSpace.kreinAdjoint (1 : H →L[ℝ] H) = 1 := by
    exact InfoGeometry.Krein.KreinSpace.kreinAdjoint_id (H := H)
  rw [hid, hN]

end InfoGeometry.Physics.Algebra
