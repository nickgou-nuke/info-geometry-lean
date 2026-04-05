import InfoGeometry.Quantum.GeometricTensor
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Krein.SplitQuadratic

open scoped InnerProductSpace

namespace InfoGeometry.Quantum

open InfoGeometry.Krein
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Canonical.BogoliubovTransport

namespace GeometricQuantumTensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Positive Cartan-side lift of a doubled-carrier operator to a bilinear form.
This is the Hilbert-side QGT seed associated to the local involution split.
-/
noncomputable def metricOfOperator (A : EndH) : LinearMap.BilinForm ℝ H₂ :=
  LinearMap.mk₂ ℝ
    (fun u v => ⟪A u, v⟫_ℝ)
    (by
      intro u₁ u₂ v
      simp [map_add, inner_add_left])
    (by
      intro c u v
      simp [map_smul, real_inner_smul_left, smul_eq_mul, mul_add])
    (by
      intro u v₁ v₂
      simp [inner_add_right])
    (by
      intro c u v
      simp [real_inner_smul_right, smul_eq_mul, mul_add])

omit [CompleteSpace E] in
@[simp] theorem metricOfOperator_apply
    (A : EndH) (u v : H₂) :
    metricOfOperator A u v = ⟪A u, v⟫_ℝ := rfl

/-- A Hilbert-self-adjoint seed induces a symmetric metric on the doubled carrier. -/
theorem metricOfOperator_isSymm_of_selfAdjoint
    (A : EndH)
    (hA : IsSelfAdjoint A) :
    (metricOfOperator A).IsSymm := by
  refine ⟨?_⟩
  intro u v
  calc
    metricOfOperator A u v = ⟪A u, v⟫_ℝ := rfl
    _ = ⟪u, A.adjoint v⟫_ℝ := by rw [ContinuousLinearMap.adjoint_inner_right]
    _ = ⟪u, A v⟫_ℝ := by rw [IsSelfAdjoint.adjoint_eq hA]
    _ = ⟪A v, u⟫_ℝ := by rw [real_inner_comm]
    _ = metricOfOperator A v u := rfl

/--
If `A` commutes with the local Cartan phase axis `K = Jε`, then the induced
metric satisfies the exact `K`-skew law required by `QGT.ofMajorana`.
-/
theorem metricOfOperator_K_skew_of_commutesWithK
    (A : EndH)
    (hComm :
      A.comp (modularComplexI (E := E))
        =
      (modularComplexI (E := E)).comp A) :
    ∀ u v,
      metricOfOperator A (modularComplexI (E := E) u) v
        =
      -metricOfOperator A u (modularComplexI (E := E) v) := by
  intro u v
  have hCommEval : A (modularComplexI (E := E) u) = modularComplexI (E := E) (A u) := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun T : EndH => T u) hComm
  rw [metricOfOperator_apply, metricOfOperator_apply, hCommEval]
  exact modularComplexI_inner_skew (E := E) (A u) v

/--
Operatorial lift of the doubled real QGT from a Hilbert-self-adjoint operator
commuting with the local Cartan phase axis `K = Jε`.
-/
noncomputable def qgtOfOperator
    (A : EndH)
    (hA : IsSelfAdjoint A)
    (hComm :
      A.comp (modularComplexI (E := E))
        =
      (modularComplexI (E := E)).comp A) : QGT E :=
  ofMajorana
    (metricOfOperator A)
    (metricOfOperator_isSymm_of_selfAdjoint (A := A) hA)
    (metricOfOperator_K_skew_of_commutesWithK (E := E) (A := A) hComm)

/--
Krein-side lift of a doubled-carrier operator to a bilinear form.
This is the indefinite-metric seed on the Cartan-odd branch.
-/
noncomputable def kreinMetricOfOperator (A : EndH) : LinearMap.BilinForm ℝ H₂ :=
  (KreinSpace.kreinBilin (H := H₂)).compLeft A.toLinearMap

@[simp] theorem kreinMetricOfOperator_apply
    (A : EndH) (u v : H₂) :
    kreinMetricOfOperator A u v = KreinSpace.kreinInner (H := H₂) (A u) v := rfl

/-- A Krein-self-adjoint seed induces a symmetric Krein-side metric on the doubled carrier. -/
theorem kreinMetricOfOperator_isSymm_of_kreinSelfAdjoint
    (A : EndH)
    (hA : KreinSpace.IsKreinSelfAdjoint (H := H₂) A) :
    (kreinMetricOfOperator A).IsSymm := by
  refine ⟨?_⟩
  intro u v
  rw [kreinMetricOfOperator_apply, kreinMetricOfOperator_apply,
    KreinSpace.kreinInner_kreinAdjoint, hA]
  exact KreinSpace.kreinInner_symm (H := H₂) u (A v)

/--
If `A` lies in the Cartan-odd / phase-antilinear branch relative to `K = Jε`,
then the induced Krein metric satisfies the exact `K`-skew law required by
`QGT.ofMajorana`.
-/
theorem kreinMetricOfOperator_K_skew_of_IsPhaseAntilinear
    (A : EndH)
    (hAnti : IsPhaseAntilinear (E := E) A) :
    ∀ u v,
      kreinMetricOfOperator A (modularComplexI (E := E) u) v
        =
      -kreinMetricOfOperator A u (modularComplexI (E := E) v) := by
  intro u v
  have hAntiEval :
      A (modularComplexI (E := E) u)
        =
      -((modularComplexI (E := E)) (A u)) := by
    have h := congrArg (fun T : EndH => T u) hAnti
    simpa [IsPhaseAntilinear, ContinuousLinearMap.comp_apply] using h
  rw [kreinMetricOfOperator_apply, kreinMetricOfOperator_apply, hAntiEval]
  calc
    KreinSpace.kreinInner (H := H₂) (-((modularComplexI (E := E)) (A u))) v
      = -KreinSpace.kreinInner (H := H₂) ((modularComplexI (E := E)) (A u)) v := by
          simp
    _ = -KreinSpace.kreinInner (H := H₂) (A u) ((modularComplexI (E := E)) v) := by
          rw [modularComplexI_kreinInner_swap]
    _ = -kreinMetricOfOperator A u (modularComplexI (E := E) v) := by
          rw [kreinMetricOfOperator_apply]

/--
The Krein-side operator metric is exactly the Hilbert-side operator metric after
transporting the seed by the doubled fundamental symmetry `ε`.
-/
theorem metricOfOperator_modularSignEpsilon_comp_eq_kreinMetricOfOperator
    (A : EndH) :
    metricOfOperator ((modularSignEpsilon (E := E)).comp A)
      =
    kreinMetricOfOperator A := by
  ext u v
  rw [metricOfOperator_apply, kreinMetricOfOperator_apply, krein_inner_prod_l2]
  simp [modularSignEpsilon, spectral_epsilon, WithLp.prod_inner_apply, sub_eq_add_neg]

@[simp] theorem inner_modularSignEpsilon_apply_eq_kreinInner
    (u v : H₂) :
    ⟪(modularSignEpsilon (E := E)) u, v⟫_ℝ
      =
    KreinSpace.kreinInner (H := H₂) u v := by
  rw [krein_inner_prod_l2]
  simp [modularSignEpsilon, spectral_epsilon, WithLp.prod_inner_apply, sub_eq_add_neg]

@[simp] theorem inner_apply_modularSignEpsilon_eq_kreinInner
    (u v : H₂) :
    ⟪u, (modularSignEpsilon (E := E)) v⟫_ℝ
      =
    KreinSpace.kreinInner (H := H₂) u v := by
  calc
    ⟪u, (modularSignEpsilon (E := E)) v⟫_ℝ
      =
    ⟪(modularSignEpsilon (E := E)) u, v⟫_ℝ := by
          rw [modularSignEpsilon]
          rw [InfoGeometry.Krein.SplitQuadratic.spectral_epsilon_selfAdj (E := E) u v]
    _ = KreinSpace.kreinInner (H := H₂) u v := by
          simpa using inner_modularSignEpsilon_apply_eq_kreinInner (E := E) u v

/--
Transport by the doubled fundamental symmetry `ε` sends a Krein-self-adjoint
seed to a Hilbert-self-adjoint seed.
-/
theorem isSelfAdjoint_modularSignEpsilon_comp_of_kreinSelfAdjoint
    (A : EndH)
    (hA : KreinSpace.IsKreinSelfAdjoint (H := H₂) A) :
    IsSelfAdjoint ((modularSignEpsilon (E := E)).comp A) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  calc
    ⟪((modularSignEpsilon (E := E)).comp A) u, v⟫_ℝ
        = KreinSpace.kreinInner (H := H₂) (A u) v := by
            simpa [ContinuousLinearMap.comp_apply] using
              (inner_modularSignEpsilon_apply_eq_kreinInner (E := E) (A u) v)
    _ = KreinSpace.kreinInner (H := H₂) u (A v) := by
          rw [KreinSpace.kreinInner_kreinAdjoint, hA]
    _ = ⟪u, ((modularSignEpsilon (E := E)).comp A) v⟫_ℝ := by
          simpa [ContinuousLinearMap.comp_apply] using
            (inner_apply_modularSignEpsilon_eq_kreinInner (E := E) u (A v)).symm

/--
Transport by the doubled fundamental symmetry `ε` sends the Cartan-odd /
phase-antilinear branch to the phase-linear branch.
-/
theorem isPhaseLinear_modularSignEpsilon_comp_of_IsPhaseAntilinear
    (A : EndH)
    (hAnti : IsPhaseAntilinear (E := E) A) :
    IsPhaseLinear (E := E) ((modularSignEpsilon (E := E)).comp A) := by
  have hEpsK :
      (modularSignEpsilon (E := E)).comp (modularComplexI (E := E))
        =
      -(modularConjugationJ (E := E)) := by
    simpa [modularConjugationJ, modularSignEpsilon, modularComplexI] using
      (InfoGeometry.Krein.spectral_epsilon_comp_complex_i (E := E))
  have hKEps :
      (modularComplexI (E := E)).comp (modularSignEpsilon (E := E))
        =
      modularConjugationJ (E := E) := by
    simpa [modularConjugationJ, modularSignEpsilon, modularComplexI] using
      (InfoGeometry.Krein.complex_i_comp_spectral_epsilon (E := E))
  unfold IsPhaseLinear IsPhaseAntilinear at *
  calc
    (((modularSignEpsilon (E := E)).comp A).comp (modularComplexI (E := E)))
        = (modularSignEpsilon (E := E)).comp (A.comp (modularComplexI (E := E))) := by
            simp [ContinuousLinearMap.comp_assoc]
    _ = (modularSignEpsilon (E := E)).comp (-((modularComplexI (E := E)).comp A)) := by
          rw [hAnti]
    _ = -(((modularSignEpsilon (E := E)).comp (modularComplexI (E := E))).comp A) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = -((-(modularConjugationJ (E := E))).comp A) := by rw [hEpsK]
    _ = (modularConjugationJ (E := E)).comp A := by
          simp
    _ = ((modularComplexI (E := E)).comp (modularSignEpsilon (E := E))).comp A := by rw [hKEps]
    _ = (modularComplexI (E := E)).comp ((modularSignEpsilon (E := E)).comp A) := by
          simp [ContinuousLinearMap.comp_assoc]

/--
Operatorial lift of the doubled real QGT from a Krein-self-adjoint operator in
the Cartan-odd / phase-antilinear branch of the local `K`-involution.
-/
noncomputable def kreinQgtOfOperator
    (A : EndH)
    (hA : KreinSpace.IsKreinSelfAdjoint (H := H₂) A)
    (hAnti : IsPhaseAntilinear (E := E) A) : QGT E :=
  ofMajorana
    (kreinMetricOfOperator A)
    (kreinMetricOfOperator_isSymm_of_kreinSelfAdjoint (A := A) hA)
    (kreinMetricOfOperator_K_skew_of_IsPhaseAntilinear (E := E) (A := A) hAnti)

/--
The Hilbert-side and Krein-side QGT lifts agree on the metric after transport
by the doubled fundamental symmetry `ε`.
-/
theorem qgtOfOperator_modularSignEpsilon_comp_metric_eq_kreinQgtOfOperator_metric
    (A : EndH)
    (hA : KreinSpace.IsKreinSelfAdjoint (H := H₂) A)
    (hAnti : IsPhaseAntilinear (E := E) A) :
    (qgtOfOperator
        (E := E)
        ((modularSignEpsilon (E := E)).comp A)
        (isSelfAdjoint_modularSignEpsilon_comp_of_kreinSelfAdjoint
          (E := E) (A := A) hA)
        (isPhaseLinear_modularSignEpsilon_comp_of_IsPhaseAntilinear
          (E := E) (A := A) hAnti)).metric
      =
    (kreinQgtOfOperator (E := E) A hA hAnti).metric := by
  simp [qgtOfOperator, kreinQgtOfOperator,
    GeometricQuantumTensor.ofMajorana,
    metricOfOperator_modularSignEpsilon_comp_eq_kreinMetricOfOperator]

/--
The Hilbert-side and Krein-side QGT lifts agree on the Berry form after
transport by the doubled fundamental symmetry `ε`.
-/
theorem qgtOfOperator_modularSignEpsilon_comp_berry_eq_kreinQgtOfOperator_berry
    (A : EndH)
    (hA : KreinSpace.IsKreinSelfAdjoint (H := H₂) A)
    (hAnti : IsPhaseAntilinear (E := E) A) :
    (qgtOfOperator
        (E := E)
        ((modularSignEpsilon (E := E)).comp A)
        (isSelfAdjoint_modularSignEpsilon_comp_of_kreinSelfAdjoint
          (E := E) (A := A) hA)
        (isPhaseLinear_modularSignEpsilon_comp_of_IsPhaseAntilinear
          (E := E) (A := A) hAnti)).berry
      =
    (kreinQgtOfOperator (E := E) A hA hAnti).berry := by
  simp [qgtOfOperator, kreinQgtOfOperator,
    GeometricQuantumTensor.ofMajorana,
    metricOfOperator_modularSignEpsilon_comp_eq_kreinMetricOfOperator]

end GeometricQuantumTensor

end InfoGeometry.Quantum
