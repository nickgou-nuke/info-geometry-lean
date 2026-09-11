import InfoGeometry.Quantum.GeometricTensor
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Canonical.EinsteinAnomalyOperator
import InfoGeometry.Canonical.MoorePenrose
import InfoGeometry.Krein.SplitQuadratic
import InfoGeometry.Volume.ConnesInfinitesimal

open scoped InnerProductSpace

namespace InfoGeometry.Quantum

open InfoGeometry.Krein
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.ConformalUnification

namespace GeometricQuantumTensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

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

omit [CompleteSpace E] in
@[simp] theorem metricOfOperator_zero :
    metricOfOperator (E := E) (0 : EndH) = 0 := by
  ext u v
  simp [metricOfOperator_apply]

omit [CompleteSpace E] in
@[simp] theorem metricOfOperator_add
    (A B : EndH) :
    metricOfOperator (E := E) (A + B)
      = metricOfOperator (E := E) A + metricOfOperator (E := E) B := by
  ext u v
  simp [metricOfOperator_apply, inner_add_left]

omit [CompleteSpace E] in
@[simp] theorem metricOfOperator_neg
    (A : EndH) :
    metricOfOperator (E := E) (-A)
      = -metricOfOperator (E := E) A := by
  ext u v
  simp [metricOfOperator_apply]

omit [CompleteSpace E] in
@[simp] theorem metricOfOperator_smul
    (c : ℝ) (A : EndH) :
    metricOfOperator (E := E) (c • A)
      = c • metricOfOperator (E := E) A := by
  ext u v
  simp [metricOfOperator_apply, real_inner_smul_left, smul_eq_mul]
  ring

/--
If an operator commutes with the modular Hamiltonian, then its operatorial metric
seed is fixed by the modular flow.
-/
@[simp] theorem metricOfOperator_modularHamiltonianAction_eq_self_of_commute
    (K A : EndH) (t : ℝ) (hComm : Commute A K) :
    metricOfOperator (E := E)
      (InfoGeometry.Volume.ConnesInfinitesimal.modularHamiltonianAction (H := E) K A t)
      = metricOfOperator (E := E) A := by
  rw [InfoGeometry.Volume.ConnesInfinitesimal.modularHamiltonianAction_eq_self_of_commute
    (H := E) K A t hComm]

/--
Operatorial Berry 2-form seed on doubled space, induced from the operatorial
metric seed via the local phase axis `K = Jε`.
-/
noncomputable def berryOfOperator (A : EndH) : LinearMap.BilinForm ℝ H₂ :=
  (metricOfOperator A).compLeft (InfoGeometry.Canonical.TomitaTakesaki.clockAxis).toLinearMap

/--
Explicit split-`Cl(1,1)` Berry 2-form seed:
the phase axis is written as `J ∘ ε` on doubled real space.
-/
noncomputable def berryTwoFormJEpsOfOperator (A : EndH) : LinearMap.BilinForm ℝ H₂ :=
  (metricOfOperator A).compLeft
    (((modularConjugationJ (E := E)).comp (modularSignEpsilon (E := E))).toLinearMap)

omit [CompleteSpace E] in
@[simp] theorem berryTwoFormJEpsOfOperator_apply
    (A : EndH) (u v : H₂) :
    berryTwoFormJEpsOfOperator (E := E) A u v
      =
    metricOfOperator A
      (((modularConjugationJ (E := E)).comp (modularSignEpsilon (E := E))) u) v := rfl

-- Root-name form of the explicit split-`Cl(1,1)` Berry 2-form seed.
omit [CompleteSpace E] in
@[simp] theorem berryTwoFormJEpsOfOperator_apply_root
    (A : EndH) (u v : H₂) :
    berryTwoFormJEpsOfOperator (E := E) A u v
      =
    metricOfOperator A
      (((InfoGeometry.Krein.modular_j (E := E)).comp
          (InfoGeometry.Krein.spectral_epsilon (E := E))) u) v := by
  exact berryTwoFormJEpsOfOperator_apply (E := E) A u v

omit [CompleteSpace E] in
@[simp] theorem berryTwoFormJEpsOfOperator_eq_berryOfOperator
    (A : EndH) :
    berryTwoFormJEpsOfOperator (E := E) A = berryOfOperator (E := E) A := by
  ext u v
  simp [berryTwoFormJEpsOfOperator, berryOfOperator,
    modularConjugationJ, modularSignEpsilon]

omit [CompleteSpace E] in
@[simp] theorem berryTwoFormJEpsOfOperator_apply_eq_berryOfOperator
    (A : EndH) (u v : H₂) :
    berryTwoFormJEpsOfOperator (E := E) A u v
      =
    berryOfOperator (E := E) A u v := by
  rw [berryTwoFormJEpsOfOperator_eq_berryOfOperator (E := E) A]

omit [CompleteSpace E] in
@[simp] theorem berryTwoFormJEpsOfOperator_neg
    (A : EndH) :
    berryTwoFormJEpsOfOperator (E := E) (-A)
      =
    -berryTwoFormJEpsOfOperator (E := E) A := by
  ext u v
  change
    metricOfOperator (-A)
        (((modularConjugationJ (E := E)).comp (modularSignEpsilon (E := E))) u) v
      =
    -metricOfOperator A
        (((modularConjugationJ (E := E)).comp (modularSignEpsilon (E := E))) u) v
  simp [metricOfOperator_apply]

omit [CompleteSpace E] in
@[simp] theorem berryOfOperator_apply
    (A : EndH) (u v : H₂) :
    berryOfOperator (E := E) A u v
      =
    metricOfOperator A (InfoGeometry.Canonical.TomitaTakesaki.clockAxis u) v := rfl

-- Root-name form of the operatorial Berry readout.
omit [CompleteSpace E] in
@[simp] theorem berryOfOperator_apply_complex_i
    (A : EndH) (u v : H₂) :
    berryOfOperator (E := E) A u v
      =
    metricOfOperator A (InfoGeometry.Krein.complex_i (E := E) u) v := by
  exact berryOfOperator_apply (E := E) A u v

omit [CompleteSpace E] in
@[simp] theorem berryOfOperator_add
    (A B : EndH) :
    berryOfOperator (E := E) (A + B)
      =
    berryOfOperator (E := E) A + berryOfOperator (E := E) B := by
  ext u v
  simp [berryOfOperator_apply, metricOfOperator_add]

omit [CompleteSpace E] in
@[simp] theorem berryOfOperator_smul
    (c : ℝ) (A : EndH) :
    berryOfOperator (E := E) (c • A)
      =
    c • berryOfOperator (E := E) A := by
  ext u v
  simp [berryOfOperator_apply, metricOfOperator_smul, smul_eq_mul]

/--
For a phase-linear doubled-carrier operator `A`, the Hestenes-twisted Berry
seed of `K ∘ A` is exactly minus the untwisted operator metric seed of `A`.
-/
theorem berryOfOperator_modularComplexI_comp_eq_neg_metricOfOperator_of_IsPhaseLinear
    (A : EndH)
    (hComm :
      A.comp (InfoGeometry.Canonical.TomitaTakesaki.clockAxis)
        =
      (InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp A) :
    berryOfOperator (E := E) ((InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp A)
      =
    -metricOfOperator (E := E) A := by
  ext u v
  have hCommEval :
      A ((InfoGeometry.Canonical.TomitaTakesaki.clockAxis) u)
        =
      (InfoGeometry.Canonical.TomitaTakesaki.clockAxis) (A u) := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun T : EndH => T u) hComm
  have hK2 :
      (InfoGeometry.Canonical.TomitaTakesaki.clockAxis) ((InfoGeometry.Canonical.TomitaTakesaki.clockAxis) (A u))
        =
      -(A u) := by
    change
      (((InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp (InfoGeometry.Canonical.TomitaTakesaki.clockAxis)) (A u))
        =
      (-(ContinuousLinearMap.id ℝ H₂)) (A u)
    rw [modularComplexI_sq (E := E)]
  calc
    berryOfOperator (E := E) ((InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp A) u v
        = ⟪((InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp A) ((InfoGeometry.Canonical.TomitaTakesaki.clockAxis) u), v⟫_ℝ := by
            rw [berryOfOperator_apply, metricOfOperator_apply]
    _ = ⟪(InfoGeometry.Canonical.TomitaTakesaki.clockAxis) (A ((InfoGeometry.Canonical.TomitaTakesaki.clockAxis) u)), v⟫_ℝ := by
          rfl
    _ = ⟪(InfoGeometry.Canonical.TomitaTakesaki.clockAxis) ((InfoGeometry.Canonical.TomitaTakesaki.clockAxis) (A u)), v⟫_ℝ := by
          rw [hCommEval]
    _ = ⟪-(A u), v⟫_ℝ := by rw [hK2]
    _ = (-metricOfOperator (E := E) A) u v := by
          simp [metricOfOperator_apply]

/--
Infinitesimal transport law for the operatorial metric seed under exponential
conjugation: the derivative at `t = 0` is the metric readout of the commutator.
-/
theorem hasDerivAt_metricOfOperator_expTransport_at_zero
    (X A : EndH) (u v : H₂) :
    HasDerivAt
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport (A := EndH) X A t) u v)
      (metricOfOperator (transportCommutator (E := E) X A) u v)
      0 := by
  let ω : EndH →L[ℝ] ℝ :=
    (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ H₂ u)
  have hω : HasDerivAt (fun _ : ℝ => ω) (0 : EndH →L[ℝ] ℝ) 0 := by
    simpa using (hasDerivAt_const (x := (0 : ℝ)) (c := ω))
  have hExp :
      HasDerivAt
        (fun t : ℝ => InfoGeometry.Canonical.expTransport (A := EndH) X A t)
        ⁅X, A⁆
        0 := by
    simpa using
      (InfoGeometry.Canonical.hasDerivAt_expTransport_at_zero (A := EndH) X A)
  have hApply :
      HasDerivAt
        (fun t : ℝ =>
          (fun _ : ℝ => ω) t
            (InfoGeometry.Canonical.expTransport (A := EndH) X A t))
        ((0 : EndH →L[ℝ] ℝ)
          (InfoGeometry.Canonical.expTransport (A := EndH) X A 0) + ω ⁅X, A⁆)
        0 :=
    hω.clm_apply hExp
  have hωEval :
      ω ⁅X, A⁆ = metricOfOperator (transportCommutator (E := E) X A) u v := by
    rw [← lieBracket_eq_transportCommutator (E := E) X A]
    simp [ω, metricOfOperator_apply, real_inner_comm]
  have hMain :
      HasDerivAt
        (fun t : ℝ =>
          metricOfOperator
            (InfoGeometry.Canonical.expTransport (A := EndH) X A t) u v)
        (ω ⁅X, A⁆)
        0 := by
    simpa [ω, metricOfOperator_apply, real_inner_comm] using hApply
  exact hωEval ▸ hMain

/--
Derivative form of `hasDerivAt_metricOfOperator_expTransport_at_zero`.
-/
theorem deriv_metricOfOperator_expTransport_at_zero
    (X A : EndH) (u v : H₂) :
    deriv
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport (A := EndH) X A t) u v)
      0
      =
    metricOfOperator (transportCommutator (E := E) X A) u v := by
  exact (hasDerivAt_metricOfOperator_expTransport_at_zero (E := E) X A u v).deriv

/--
Global transport law for the operatorial metric seed under exponential
conjugation at arbitrary `t`.
-/
theorem hasDerivAt_metricOfOperator_expTransport
    (X A : EndH) (u v : H₂) (t : ℝ) :
    HasDerivAt
      (fun s =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport (A := EndH) X A s) u v)
      (metricOfOperator
        (InfoGeometry.Canonical.expTransport
          (A := EndH)
          X
          (transportCommutator (E := E) X A)
          t) u v)
      t := by
  let ω : EndH →L[ℝ] ℝ :=
    (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ H₂ u)
  have hω : HasDerivAt (fun _ : ℝ => ω) (0 : EndH →L[ℝ] ℝ) t := by
    simpa using (hasDerivAt_const (x := t) (c := ω))
  have hExp :
      HasDerivAt
        (fun s : ℝ => InfoGeometry.Canonical.expTransport (A := EndH) X A s)
        (InfoGeometry.Canonical.expTransport (A := EndH) X ⁅X, A⁆ t)
        t := by
    simpa using
      (InfoGeometry.Canonical.hasDerivAt_expTransport (A := EndH) X A t)
  have hApply :
      HasDerivAt
        (fun s : ℝ =>
          (fun _ : ℝ => ω) s
            (InfoGeometry.Canonical.expTransport (A := EndH) X A s))
        ((0 : EndH →L[ℝ] ℝ)
          (InfoGeometry.Canonical.expTransport (A := EndH) X A t)
            + ω (InfoGeometry.Canonical.expTransport (A := EndH) X ⁅X, A⁆ t))
        t :=
    hω.clm_apply hExp
  have hωEval :
      ω (InfoGeometry.Canonical.expTransport (A := EndH) X ⁅X, A⁆ t)
        =
      metricOfOperator
        (InfoGeometry.Canonical.expTransport
          (A := EndH)
          X
          (transportCommutator (E := E) X A)
          t) u v := by
    rw [← lieBracket_eq_transportCommutator (E := E) X A]
    simp [ω, metricOfOperator_apply, real_inner_comm]
  have hMain :
      HasDerivAt
        (fun s : ℝ =>
          metricOfOperator
            (InfoGeometry.Canonical.expTransport (A := EndH) X A s) u v)
        (ω (InfoGeometry.Canonical.expTransport (A := EndH) X ⁅X, A⁆ t))
        t := by
    simpa [ω, metricOfOperator_apply, real_inner_comm] using hApply
  exact hωEval ▸ hMain

/--
Derivative form of `hasDerivAt_metricOfOperator_expTransport` at arbitrary `t`.
-/
theorem deriv_metricOfOperator_expTransport
    (X A : EndH) (u v : H₂) (t : ℝ) :
    deriv
      (fun s =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport (A := EndH) X A s) u v)
      t
      =
    metricOfOperator
      (InfoGeometry.Canonical.expTransport
        (A := EndH)
        X
        (transportCommutator (E := E) X A)
        t) u v := by
  exact (hasDerivAt_metricOfOperator_expTransport (E := E) X A u v t).deriv

/--
Global Berry transport law under exponential conjugation at arbitrary `t`.
-/
theorem deriv_berryOfOperator_expTransport
    (X A : EndH) (u v : H₂) (t : ℝ) :
    deriv
      (fun s =>
        berryOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport (A := EndH) X A s) u v)
      t
      =
    berryOfOperator
      (E := E)
      (InfoGeometry.Canonical.expTransport
        (A := EndH)
        X
        (transportCommutator (E := E) X A)
        t) u v := by
  simpa [berryOfOperator] using
    deriv_metricOfOperator_expTransport
      (E := E) X A (InfoGeometry.Canonical.TomitaTakesaki.clockAxis u) v t

/--
Infinitesimal modular-conjugation transport law for the QGT operatorial metric
seed: derivative at `t = 0` equals the metric readout of the true modular
transport commutator.
-/
theorem deriv_metricOfOperator_modularTransport_conjugation_at_zero
    (hMod A : EndH) (u v : H₂) :
    deriv
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (modularTransportGenerator (E := E) hMod)
            A
            t)
          u v)
      0
      =
    metricOfOperator
      (transportCommutator (E := E) (modularTransportGenerator (E := E) hMod) A)
      u v := by
  simpa using
    deriv_metricOfOperator_expTransport_at_zero
      (E := E) (X := modularTransportGenerator (E := E) hMod) (A := A) u v

/--
Modular-derivation form of infinitesimal metric-seed transport at `t = 0`.
-/
theorem deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_modularDeriv
    (hMod A : EndH) (u v : H₂) :
    deriv
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (modularTransportGenerator (E := E) hMod)
            A
            t)
          u v)
      0
      =
    metricOfOperator (modularDeriv (E := E) hMod A) u v := by
  simpa [modularDeriv] using
    deriv_metricOfOperator_modularTransport_conjugation_at_zero (E := E) hMod A u v

/--
Relative-modular form: infinitesimal QGT metric-seed transport equals the metric
readout of the relative-modular derivation.
-/
theorem deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_relativeModularDeriv
    (hMod A : EndH) (u v : H₂) :
    deriv
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            A
            t)
          u v)
      0
      =
    metricOfOperator (relativeModularDeriv (E := E) hMod A) u v := by
  simpa [relativeModularKGenerator, relativeModularDeriv] using
    deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_modularDeriv
      (E := E) hMod A u v

/--
The infinitesimal metric-seed transport splits into volume-preserving
(gauge/phase-linear) and dissipative (scaling/phase-antilinear) channels.
-/
theorem deriv_metricOfOperator_modularTransport_conjugation_at_zero_split
    (hMod A : EndH) (u v : H₂) :
    deriv
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (modularTransportGenerator (E := E) hMod)
            A
            t)
          u v)
      0
      =
    metricOfOperator
      (modularGaugeDeriv (E := E) hMod A)
      u v
      +
    metricOfOperator
      (modularScaleDeriv (E := E) hMod A)
      u v := by
  rw [deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_modularDeriv
      (E := E) hMod A u v]
  rw [modularDeriv_split (E := E) hMod A]
  rw [metricOfOperator_add]
  simp

/--
Relative-modular form of the infinitesimal split:
gauge channel plus source channel.
-/
theorem deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_modularGaugeDeriv_add_metricOf_relativeModularSourceDeriv
    (hMod A : EndH) (u v : H₂) :
    deriv
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            A
            t)
          u v)
      0
      =
    metricOfOperator
      (modularGaugeDeriv (E := E) hMod A)
      u v
      +
    metricOfOperator
      (relativeModularSourceDeriv (E := E) hMod A)
      u v := by
  simpa [relativeModularKGenerator, relativeModularSourceDeriv] using
    deriv_metricOfOperator_modularTransport_conjugation_at_zero_split
      (E := E) hMod A u v

/--
If the transported operator commutes with the gauge sector of the modular
generator, the infinitesimal metric-seed transport is purely scaling.
-/
theorem deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_modularScaleDeriv_of_commute_gaugePart
    (hMod A : EndH)
    (hCommGauge : Commute A (modularGeneratorGaugePart (E := E) hMod))
    (u v : H₂) :
    deriv
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (modularTransportGenerator (E := E) hMod)
            A
            t)
          u v)
      0
      =
    metricOfOperator (modularScaleDeriv (E := E) hMod A) u v := by
  rw [deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_modularDeriv
      (E := E) hMod A u v]
  rw [modularDeriv_eq_modularScaleDeriv_of_commute_gaugePart (E := E) hMod A hCommGauge]

/--
Relative-modular source-channel form:
if gauge commutes, the infinitesimal QGT metric-seed transport is purely source.
-/
theorem deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_relativeModularSourceDeriv_of_commute_gaugePart
    (hMod A : EndH)
    (hCommGauge : Commute A (modularGeneratorGaugePart (E := E) hMod))
    (u v : H₂) :
    deriv
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            A
            t)
          u v)
      0
      =
    metricOfOperator (relativeModularSourceDeriv (E := E) hMod A) u v := by
  simpa [relativeModularKGenerator, relativeModularSourceDeriv] using
    deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_modularScaleDeriv_of_commute_gaugePart
      (E := E) hMod A hCommGauge u v

/--
Berry-form relative-modular transport law:
the infinitesimal transport derivative is the Berry readout of the
relative-modular derivation.
-/
theorem deriv_berryOfOperator_modularTransport_conjugation_at_zero_eq_berryOf_relativeModularDeriv
    (hMod A : EndH) (u v : H₂) :
    deriv
      (fun t =>
        berryOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            A
            t)
          u v)
      0
      =
    berryOfOperator (E := E) (relativeModularDeriv (E := E) hMod A) u v := by
  simpa [berryOfOperator] using
    deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_relativeModularDeriv
      (E := E) hMod A (InfoGeometry.Canonical.TomitaTakesaki.clockAxis u) v

/--
Split-`Cl(1,1)` (`J ∘ ε`) form of the infinitesimal Berry transport law:
the derivative equals the Berry readout of the relative-modular derivation.
-/
theorem deriv_berryTwoFormJEpsOfOperator_modularTransport_conjugation_at_zero_eq_berryTwoFormJEpsOf_relativeModularDeriv
    (hMod A : EndH) (u v : H₂) :
    deriv
      (fun t =>
        berryTwoFormJEpsOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            A
            t)
          u v)
      0
      =
    berryTwoFormJEpsOfOperator (E := E) (relativeModularDeriv (E := E) hMod A) u v := by
  rw [berryTwoFormJEpsOfOperator_eq_berryOfOperator (E := E) (A := relativeModularDeriv (E := E) hMod A)]
  conv_lhs =>
    arg 1
    intro t
    rw [berryTwoFormJEpsOfOperator_eq_berryOfOperator (E := E)
      (A := InfoGeometry.Canonical.expTransport
        (A := EndH)
        (relativeModularKGenerator (E := E) hMod)
        A
        t)]
  exact deriv_berryOfOperator_modularTransport_conjugation_at_zero_eq_berryOf_relativeModularDeriv
    (E := E) hMod A u v

/--
Global relative-modular Berry transport law at arbitrary `t`:
the derivative equals the Berry readout of the exponentially transported
relative-modular derivation seed.
-/
theorem deriv_berryOfOperator_modularTransport_conjugation_eq_berryOfOperator_expTransport_relativeModularDeriv
    (hMod A : EndH) (u v : H₂) (t : ℝ) :
    deriv
      (fun s =>
        berryOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            A
            s)
          u v)
      t
      =
    berryOfOperator
      (E := E)
      (InfoGeometry.Canonical.expTransport
        (A := EndH)
        (relativeModularKGenerator (E := E) hMod)
        (relativeModularDeriv (E := E) hMod A)
        t) u v := by
  simpa [relativeModularDeriv, modularDeriv, relativeModularKGenerator] using
    deriv_berryOfOperator_expTransport
      (E := E)
      (X := relativeModularKGenerator (E := E) hMod)
      (A := A)
      u v t

/--
Split-`Cl(1,1)` (`J ∘ ε`) form of the global relative-modular Berry transport
law at arbitrary `t`.
-/
theorem deriv_berryTwoFormJEpsOfOperator_modularTransport_conjugation_eq_berryTwoFormJEpsOf_expTransport_relativeModularDeriv
    (hMod A : EndH) (u v : H₂) (t : ℝ) :
    deriv
      (fun s =>
        berryTwoFormJEpsOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            A
            s)
          u v)
      t
      =
    berryTwoFormJEpsOfOperator
      (E := E)
      (InfoGeometry.Canonical.expTransport
        (A := EndH)
        (relativeModularKGenerator (E := E) hMod)
        (relativeModularDeriv (E := E) hMod A)
        t) u v := by
  rw [berryTwoFormJEpsOfOperator_eq_berryOfOperator (E := E)
    (A := InfoGeometry.Canonical.expTransport
      (A := EndH)
      (relativeModularKGenerator (E := E) hMod)
      (relativeModularDeriv (E := E) hMod A)
      t)]
  conv_lhs =>
    arg 1
    intro s
    rw [berryTwoFormJEpsOfOperator_eq_berryOfOperator (E := E)
      (A := InfoGeometry.Canonical.expTransport
        (A := EndH)
        (relativeModularKGenerator (E := E) hMod)
        A
        s)]
  exact deriv_berryOfOperator_modularTransport_conjugation_eq_berryOfOperator_expTransport_relativeModularDeriv
    (E := E) hMod A u v t

/--
Global Berry transport split at arbitrary `t`:
the noncommuting channel decomposes into gauge and source seeds under
exponential transport.
-/
theorem deriv_berryOfOperator_modularTransport_conjugation_eq_berryOfOperator_expTransport_modularGaugeDeriv_add_berryOfOperator_expTransport_relativeModularSourceDeriv
    (hMod A : EndH) (u v : H₂) (t : ℝ) :
    deriv
      (fun s =>
        berryOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            A
            s)
          u v)
      t
      =
    berryOfOperator
      (E := E)
      (InfoGeometry.Canonical.expTransport
        (A := EndH)
        (relativeModularKGenerator (E := E) hMod)
        (modularGaugeDeriv (E := E) hMod A)
        t) u v
      +
    berryOfOperator
      (E := E)
      (InfoGeometry.Canonical.expTransport
        (A := EndH)
        (relativeModularKGenerator (E := E) hMod)
        (relativeModularSourceDeriv (E := E) hMod A)
        t) u v := by
  rw [deriv_berryOfOperator_modularTransport_conjugation_eq_berryOfOperator_expTransport_relativeModularDeriv
    (E := E) hMod A u v t]
  rw [relativeModularDeriv_eq_modularGaugeDeriv_add_relativeModularSourceDeriv
    (E := E) hMod A]
  rw [InfoGeometry.Canonical.expTransport_add_seed (A := EndH)
    (X := relativeModularKGenerator (E := E) hMod)
    (A₁ := modularGaugeDeriv (E := E) hMod A)
    (A₂ := relativeModularSourceDeriv (E := E) hMod A)]
  rw [berryOfOperator_add]
  simp [LinearMap.add_apply]

/--
Global gauge-commuting Berry-source law at arbitrary `t`:
if the gauge part commutes with the seed, the transported noncommuting channel
is purely source-driven.
-/
theorem deriv_berryOfOperator_modularTransport_conjugation_eq_berryOfOperator_expTransport_relativeModularSourceDeriv_of_commute_gaugePart
    (hMod A : EndH)
    (hCommGauge : Commute A (modularGeneratorGaugePart (E := E) hMod))
    (u v : H₂) (t : ℝ) :
    deriv
      (fun s =>
        berryOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            A
            s)
          u v)
      t
      =
    berryOfOperator
      (E := E)
      (InfoGeometry.Canonical.expTransport
        (A := EndH)
        (relativeModularKGenerator (E := E) hMod)
        (relativeModularSourceDeriv (E := E) hMod A)
        t) u v := by
  rw [deriv_berryOfOperator_modularTransport_conjugation_eq_berryOfOperator_expTransport_relativeModularDeriv
    (E := E) hMod A u v t]
  rw [relativeModularDeriv_eq_relativeModularSourceDeriv_of_commute_gaugePart
    (E := E) hMod A hCommGauge]

/--
Split-`Cl(1,1)` (`J ∘ ε`) form of the global gauge-commuting source-channel law
at arbitrary `t`.
-/
theorem deriv_berryTwoFormJEpsOfOperator_modularTransport_conjugation_eq_berryTwoFormJEpsOf_expTransport_relativeModularSourceDeriv_of_commute_gaugePart
    (hMod A : EndH)
    (hCommGauge : Commute A (modularGeneratorGaugePart (E := E) hMod))
    (u v : H₂) (t : ℝ) :
    deriv
      (fun s =>
        berryTwoFormJEpsOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            A
            s)
          u v)
      t
      =
    berryTwoFormJEpsOfOperator
      (E := E)
      (InfoGeometry.Canonical.expTransport
        (A := EndH)
        (relativeModularKGenerator (E := E) hMod)
        (relativeModularSourceDeriv (E := E) hMod A)
        t) u v := by
  rw [berryTwoFormJEpsOfOperator_eq_berryOfOperator (E := E)
    (A := InfoGeometry.Canonical.expTransport
      (A := EndH)
      (relativeModularKGenerator (E := E) hMod)
      (relativeModularSourceDeriv (E := E) hMod A)
      t)]
  conv_lhs =>
    arg 1
    intro s
    rw [berryTwoFormJEpsOfOperator_eq_berryOfOperator (E := E)
      (A := InfoGeometry.Canonical.expTransport
        (A := EndH)
        (relativeModularKGenerator (E := E) hMod)
        A
        s)]
  exact
    deriv_berryOfOperator_modularTransport_conjugation_eq_berryOfOperator_expTransport_relativeModularSourceDeriv_of_commute_gaugePart
      (E := E) hMod A hCommGauge u v t

/--
Berry-form relative-modular split law:
infinitesimal transport decomposes into gauge and source channels.
-/
theorem deriv_berryOfOperator_modularTransport_conjugation_at_zero_eq_berryOf_modularGaugeDeriv_add_berryOf_relativeModularSourceDeriv
    (hMod A : EndH) (u v : H₂) :
    deriv
      (fun t =>
        berryOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            A
            t)
          u v)
      0
      =
    berryOfOperator (E := E) (modularGaugeDeriv (E := E) hMod A) u v
      +
    berryOfOperator (E := E) (relativeModularSourceDeriv (E := E) hMod A) u v := by
  simpa [berryOfOperator] using
    deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_modularGaugeDeriv_add_metricOf_relativeModularSourceDeriv
      (E := E) hMod A (InfoGeometry.Canonical.TomitaTakesaki.clockAxis u) v

/--
Gauge-commuting Berry-source law:
if the transported operator commutes with the gauge channel, infinitesimal
Berry transport is purely source-driven.
-/
theorem deriv_berryOfOperator_modularTransport_conjugation_at_zero_eq_berryOf_relativeModularSourceDeriv_of_commute_gaugePart
    (hMod A : EndH)
    (hCommGauge : Commute A (modularGeneratorGaugePart (E := E) hMod))
    (u v : H₂) :
    deriv
      (fun t =>
        berryOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            A
            t)
          u v)
      0
      =
    berryOfOperator (E := E) (relativeModularSourceDeriv (E := E) hMod A) u v := by
  simpa [berryOfOperator] using
    deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_relativeModularSourceDeriv_of_commute_gaugePart
      (E := E) hMod A hCommGauge (InfoGeometry.Canonical.TomitaTakesaki.clockAxis u) v

/--
Split-`Cl(1,1)` (`J ∘ ε`) source-channel law:
if the gauge part commutes, infinitesimal Berry transport is purely
relative-modular source transport.
-/
theorem deriv_berryTwoFormJEpsOfOperator_modularTransport_conjugation_at_zero_eq_berryTwoFormJEpsOf_relativeModularSourceDeriv_of_commute_gaugePart
    (hMod A : EndH)
    (hCommGauge : Commute A (modularGeneratorGaugePart (E := E) hMod))
    (u v : H₂) :
    deriv
      (fun t =>
        berryTwoFormJEpsOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            A
            t)
          u v)
      0
      =
    berryTwoFormJEpsOfOperator (E := E)
      (relativeModularSourceDeriv (E := E) hMod A) u v := by
  rw [berryTwoFormJEpsOfOperator_eq_berryOfOperator (E := E)
    (A := relativeModularSourceDeriv (E := E) hMod A)]
  conv_lhs =>
    arg 1
    intro t
    rw [berryTwoFormJEpsOfOperator_eq_berryOfOperator (E := E)
      (A := InfoGeometry.Canonical.expTransport
        (A := EndH)
        (relativeModularKGenerator (E := E) hMod)
        A
        t)]
  exact
    deriv_berryOfOperator_modularTransport_conjugation_at_zero_eq_berryOf_relativeModularSourceDeriv_of_commute_gaugePart
      (E := E) hMod A hCommGauge u v

/--
Canonical obstruction-seed specialization of the split-`Cl(1,1)` source law:
for the certified projector obstruction operator, gauge-sector commutation
forces infinitesimal `Jε`-Berry transport into the relative-modular source
channel.
-/
theorem deriv_berryTwoFormJEpsOfOperator_projectorObstructionOperator_relativeModularTransport_at_zero_eq_berryTwoFormJEpsOf_relativeModularSourceDeriv_of_commute_gaugePart
    (CCI : CertifiedConformalInference E)
    (hMod : EndH)
    (hCommGauge :
      Commute CCI.liftedProjectorObstructionOperator
        (modularGeneratorGaugePart (E := E) hMod))
    (u v : H₂) :
    deriv
      (fun t =>
        berryTwoFormJEpsOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            CCI.liftedProjectorObstructionOperator
            t)
          u v)
      0
      =
    berryTwoFormJEpsOfOperator
      (E := E)
      (relativeModularSourceDeriv (E := E) hMod CCI.liftedProjectorObstructionOperator)
      u v := by
  exact
    deriv_berryTwoFormJEpsOfOperator_modularTransport_conjugation_at_zero_eq_berryTwoFormJEpsOf_relativeModularSourceDeriv_of_commute_gaugePart
      (E := E) hMod CCI.liftedProjectorObstructionOperator hCommGauge u v

/--
Global canonical obstruction-seed specialization at arbitrary `t`:
under gauge-sector commutation, the transported `Jε`-Berry channel is the
exponentially transported relative-modular source seed.
-/
theorem deriv_berryTwoFormJEpsOfOperator_projectorObstructionOperator_relativeModularTransport_eq_berryTwoFormJEpsOf_expTransport_relativeModularSourceDeriv_of_commute_gaugePart
    (CCI : CertifiedConformalInference E)
    (hMod : EndH)
    (hCommGauge :
      Commute CCI.liftedProjectorObstructionOperator
        (modularGeneratorGaugePart (E := E) hMod))
    (u v : H₂) (t : ℝ) :
    deriv
      (fun s =>
        berryTwoFormJEpsOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            CCI.liftedProjectorObstructionOperator
            s)
          u v)
      t
      =
    berryTwoFormJEpsOfOperator
      (E := E)
      (InfoGeometry.Canonical.expTransport
        (A := EndH)
        (relativeModularKGenerator (E := E) hMod)
        (relativeModularSourceDeriv (E := E) hMod CCI.liftedProjectorObstructionOperator)
        t) u v := by
  exact
    deriv_berryTwoFormJEpsOfOperator_modularTransport_conjugation_eq_berryTwoFormJEpsOf_expTransport_relativeModularSourceDeriv_of_commute_gaugePart
      (E := E) hMod CCI.liftedProjectorObstructionOperator hCommGauge u v t

/--
Direct weld closure at the `Jε` Berry-seed level:
under projector agreement, the lifted Einstein-anomaly seed is exactly the
negative of the lifted canonical projector-obstruction seed.
-/
theorem berryTwoFormJEpsOfOperator_liftedEinsteinAnomalyOperator_eq_neg_liftedProjectorObstructionOperator_of_projectorAgreement
    (CCI : CertifiedConformalInference E)
    (hProj :
      InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.rightProjector CCI.A CCI.A_MP =
        InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.leftProjector CCI.A CCI.A_MP) :
    berryTwoFormJEpsOfOperator (E := E) CCI.liftedEinsteinAnomalyOperator
      =
    -berryTwoFormJEpsOfOperator (E := E) CCI.liftedProjectorObstructionOperator := by
  rw [CCI.liftedEinsteinAnomalyOperator_eq_neg_liftedProjectorObstructionOperator_of_projectorAgreement hProj]
  simpa using
    (berryTwoFormJEpsOfOperator_neg (E := E) CCI.liftedProjectorObstructionOperator)

/--
For the certified doubled Einstein anomaly operator, gauge-sector commutation
forces the infinitesimal QGT transport entirely into the relative-modular
source channel.
-/
theorem deriv_metricOfOperator_liftedEinsteinAnomalyOperator_relativeModularTransport_at_zero_eq_metricOf_relativeModularSourceDeriv_of_commute_gaugePart
    (CCI : CertifiedConformalInference E)
    (hMod : EndH)
    (hCommGauge :
      Commute CCI.liftedEinsteinAnomalyOperator
        (modularGeneratorGaugePart (E := E) hMod))
    (u v : H₂) :
    deriv
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            CCI.liftedEinsteinAnomalyOperator
            t)
          u v)
      0
      =
    metricOfOperator
      (relativeModularSourceDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator)
      u v := by
  exact
    deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_relativeModularSourceDeriv_of_commute_gaugePart
      (E := E) hMod CCI.liftedEinsteinAnomalyOperator hCommGauge u v

/--
Berry-form specialization of the lifted Einstein-anomaly source law:
under gauge-sector commutation, infinitesimal Berry transport is entirely
carried by the relative-modular source channel.
-/
theorem deriv_berryOfOperator_liftedEinsteinAnomalyOperator_relativeModularTransport_at_zero_eq_berryOf_relativeModularSourceDeriv_of_commute_gaugePart
    (CCI : CertifiedConformalInference E)
    (hMod : EndH)
    (hCommGauge :
      Commute CCI.liftedEinsteinAnomalyOperator
        (modularGeneratorGaugePart (E := E) hMod))
    (u v : H₂) :
    deriv
      (fun t =>
        berryOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            CCI.liftedEinsteinAnomalyOperator
            t)
          u v)
      0
      =
    berryOfOperator
      (E := E)
      (relativeModularSourceDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator)
      u v := by
  simpa [berryOfOperator] using
    deriv_metricOfOperator_liftedEinsteinAnomalyOperator_relativeModularTransport_at_zero_eq_metricOf_relativeModularSourceDeriv_of_commute_gaugePart
      (E := E) CCI hMod hCommGauge (InfoGeometry.Canonical.TomitaTakesaki.clockAxis u) v

/--
Split-`Cl(1,1)` (`J ∘ ε`) specialization of the lifted Einstein-anomaly source
law: under gauge-sector commutation, infinitesimal `Jε`-Berry transport is
entirely carried by the relative-modular source channel.
-/
theorem deriv_berryTwoFormJEpsOfOperator_liftedEinsteinAnomalyOperator_relativeModularTransport_at_zero_eq_berryTwoFormJEpsOf_relativeModularSourceDeriv_of_commute_gaugePart
    (CCI : CertifiedConformalInference E)
    (hMod : EndH)
    (hCommGauge :
      Commute CCI.liftedEinsteinAnomalyOperator
        (modularGeneratorGaugePart (E := E) hMod))
    (u v : H₂) :
    deriv
      (fun t =>
        berryTwoFormJEpsOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            CCI.liftedEinsteinAnomalyOperator
            t)
          u v)
      0
      =
    berryTwoFormJEpsOfOperator
      (E := E)
      (relativeModularSourceDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator)
      u v := by
  rw [berryTwoFormJEpsOfOperator_eq_berryOfOperator (E := E)
    (A := relativeModularSourceDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator)]
  conv_lhs =>
    arg 1
    intro t
    rw [berryTwoFormJEpsOfOperator_eq_berryOfOperator (E := E)
      (A := InfoGeometry.Canonical.expTransport
        (A := EndH)
        (relativeModularKGenerator (E := E) hMod)
        CCI.liftedEinsteinAnomalyOperator
        t)]
  exact
    deriv_berryOfOperator_liftedEinsteinAnomalyOperator_relativeModularTransport_at_zero_eq_berryOf_relativeModularSourceDeriv_of_commute_gaugePart
      (E := E) CCI hMod hCommGauge u v

/--
Global Berry-form specialization of the lifted Einstein-anomaly source law:
under gauge-sector commutation, transport at arbitrary `t` is carried by the
exponentially transported relative-modular source seed.
-/
theorem deriv_berryOfOperator_liftedEinsteinAnomalyOperator_relativeModularTransport_eq_berryOfOperator_expTransport_relativeModularSourceDeriv_of_commute_gaugePart
    (CCI : CertifiedConformalInference E)
    (hMod : EndH)
    (hCommGauge :
      Commute CCI.liftedEinsteinAnomalyOperator
        (modularGeneratorGaugePart (E := E) hMod))
    (u v : H₂) (t : ℝ) :
    deriv
      (fun s =>
        berryOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            CCI.liftedEinsteinAnomalyOperator
            s)
          u v)
      t
      =
    berryOfOperator
      (E := E)
      (InfoGeometry.Canonical.expTransport
        (A := EndH)
        (relativeModularKGenerator (E := E) hMod)
        (relativeModularSourceDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator)
        t) u v := by
  exact
    deriv_berryOfOperator_modularTransport_conjugation_eq_berryOfOperator_expTransport_relativeModularSourceDeriv_of_commute_gaugePart
      (E := E) hMod CCI.liftedEinsteinAnomalyOperator hCommGauge u v t

/--
Split-`Cl(1,1)` (`J ∘ ε`) global specialization of the lifted Einstein-anomaly
source law at arbitrary `t`.
-/
theorem deriv_berryTwoFormJEpsOfOperator_liftedEinsteinAnomalyOperator_relativeModularTransport_eq_berryTwoFormJEpsOf_expTransport_relativeModularSourceDeriv_of_commute_gaugePart
    (CCI : CertifiedConformalInference E)
    (hMod : EndH)
    (hCommGauge :
      Commute CCI.liftedEinsteinAnomalyOperator
        (modularGeneratorGaugePart (E := E) hMod))
    (u v : H₂) (t : ℝ) :
    deriv
      (fun s =>
        berryTwoFormJEpsOfOperator
          (E := E)
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            CCI.liftedEinsteinAnomalyOperator
            s)
          u v)
      t
      =
    berryTwoFormJEpsOfOperator
      (E := E)
      (InfoGeometry.Canonical.expTransport
        (A := EndH)
        (relativeModularKGenerator (E := E) hMod)
        (relativeModularSourceDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator)
        t) u v := by
  exact
    deriv_berryTwoFormJEpsOfOperator_modularTransport_conjugation_eq_berryTwoFormJEpsOf_expTransport_relativeModularSourceDeriv_of_commute_gaugePart
      (E := E) hMod CCI.liftedEinsteinAnomalyOperator hCommGauge u v t

/--
Star-certified carrier form of the source-channel theorem:
for the lifted Einstein anomaly operator coming from a star-certified conformal
package, gauge-sector commutation forces infinitesimal QGT transport entirely
into the relative-modular source channel.
-/
theorem deriv_metricOfOperator_starCertified_liftedEinsteinAnomalyOperator_relativeModularTransport_at_zero_eq_metricOf_relativeModularSourceDeriv_of_commute_gaugePart
    (SCI : StarCertifiedConformalInference E)
    (hMod : EndH)
    (hCommGauge :
      Commute SCI.liftedEinsteinAnomalyOperator
        (modularGeneratorGaugePart (E := E) hMod))
    (u v : H₂) :
    deriv
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            SCI.liftedEinsteinAnomalyOperator
            t)
          u v)
      0
      =
    metricOfOperator
      (relativeModularSourceDeriv (E := E) hMod SCI.liftedEinsteinAnomalyOperator)
      u v := by
  simpa [StarCertifiedConformalInference.liftedEinsteinAnomalyOperator] using
    deriv_metricOfOperator_liftedEinsteinAnomalyOperator_relativeModularTransport_at_zero_eq_metricOf_relativeModularSourceDeriv_of_commute_gaugePart
      (E := E) SCI.toCertifiedConformalInference hMod hCommGauge u v

/--
If the transported operator commutes with the scaling sector of the modular
generator, the infinitesimal metric-seed transport is purely gauge.
-/
theorem deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_modularGaugeDeriv_of_commute_scalePart
    (hMod A : EndH)
    (hCommScale : Commute A (modularGeneratorScalePart (E := E) hMod))
    (u v : H₂) :
    deriv
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (modularTransportGenerator (E := E) hMod)
            A
            t)
          u v)
      0
      =
    metricOfOperator (modularGaugeDeriv (E := E) hMod A) u v := by
  rw [deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_modularDeriv
      (E := E) hMod A u v]
  rw [modularDeriv_eq_modularGaugeDeriv_of_commute_scalePart (E := E) hMod A hCommScale]

/--
If the transported operator commutes with the true modular transport generator,
the infinitesimal metric-seed transport vanishes at `t = 0`.
-/
theorem deriv_metricOfOperator_modularTransport_conjugation_at_zero_of_commute
    (hMod A : EndH)
    (hComm : Commute A (modularTransportGenerator (E := E) hMod))
    (u v : H₂) :
    deriv
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (modularTransportGenerator (E := E) hMod)
            A
            t)
          u v)
      0
      =
    0 := by
  rw [deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_modularDeriv
      (E := E) hMod A u v]
  rw [modularDeriv_eq_zero_of_commute_generator (E := E) hMod A hComm]
  rw [metricOfOperator_zero]
  rfl

/--
Relative-modular commuting-sector stationarity:
if `A` commutes with the relative-modular `K`-generator, the infinitesimal QGT
metric-seed transport vanishes.
-/
theorem deriv_metricOfOperator_modularTransport_conjugation_at_zero_of_commute_relativeModularKGenerator
    (hMod A : EndH)
    (hComm : Commute A (relativeModularKGenerator (E := E) hMod))
    (u v : H₂) :
    deriv
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            A
            t)
          u v)
      0
      =
    0 := by
  simpa [relativeModularKGenerator] using
    deriv_metricOfOperator_modularTransport_conjugation_at_zero_of_commute
      (E := E) hMod A hComm u v


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
      A.comp (InfoGeometry.Canonical.TomitaTakesaki.clockAxis)
        =
      (InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp A) :
    ∀ u v,
      metricOfOperator A (InfoGeometry.Canonical.TomitaTakesaki.clockAxis u) v
        =
      -metricOfOperator A u (InfoGeometry.Canonical.TomitaTakesaki.clockAxis v) := by
  intro u v
  have hCommEval : A (InfoGeometry.Canonical.TomitaTakesaki.clockAxis u) = InfoGeometry.Canonical.TomitaTakesaki.clockAxis (A u) := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun T : EndH => T u) hComm
  rw [metricOfOperator_apply, metricOfOperator_apply, hCommEval]
  exact modularComplexI_inner_skew (E := E) (A u) v

theorem metricOfOperator_complex_i_skew_of_commutesWith_complex_i
    (A : EndH)
    (hComm :
      A.comp (InfoGeometry.Krein.complex_i (E := E))
        =
      (InfoGeometry.Krein.complex_i (E := E)).comp A) :
    ∀ u v,
      metricOfOperator A (InfoGeometry.Krein.complex_i (E := E) u) v
        =
      -metricOfOperator A u (InfoGeometry.Krein.complex_i (E := E) v) := by
  intro u v
  have hComm' :
      A.comp (InfoGeometry.Canonical.TomitaTakesaki.clockAxis)
        =
      (InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp A := by
    simpa [modularComplexI_eq_complex_i] using hComm
  simpa [modularComplexI_eq_complex_i] using
    metricOfOperator_K_skew_of_commutesWithK (E := E) (A := A) hComm' u v

/--
On the positive doubled-space Hilbert metric, the local Cartan axis `K = Jε`
is skew-adjoint.
-/
theorem modularComplexI_star_eq_neg :
    star (InfoGeometry.Canonical.TomitaTakesaki.clockAxis (E := E))
      = -(InfoGeometry.Canonical.TomitaTakesaki.clockAxis (E := E)) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_left ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right]
  change
    ⟪InfoGeometry.Canonical.TomitaTakesaki.clockAxis v, u⟫_ℝ
      =
    ⟪v, -(InfoGeometry.Canonical.TomitaTakesaki.clockAxis u)⟫_ℝ
  rw [inner_neg_right]
  exact modularComplexI_inner_skew (E := E) v u

theorem complex_i_star_eq_neg :
    star (InfoGeometry.Krein.complex_i (E := E))
      =
    -(InfoGeometry.Krein.complex_i (E := E)) := by
  simpa [modularComplexI_eq_complex_i] using modularComplexI_star_eq_neg (E := E)

/--
If `A` is skew-adjoint and commutes with `K = Jε`, then the rotated seed
`K ∘ A` is Hilbert-self-adjoint.
-/
theorem isSelfAdjoint_modularComplexI_comp_of_star_eq_neg_of_commutesWithK
    (A : EndH)
    (hStar : star A = -A)
    (hComm :
      A.comp (InfoGeometry.Canonical.TomitaTakesaki.clockAxis)
        =
      (InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp A) :
    IsSelfAdjoint ((InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp A) := by
  let K : EndH := InfoGeometry.Canonical.TomitaTakesaki.clockAxis (E := E)
  have hCommMul :
      A * K = K * A := by
    simpa [K] using hComm
  change star (K * A) = K * A
  calc
    star (K * A)
        = star A * star K := by
            rw [star_mul]
    _ = (-A) * (-K) := by
          rw [hStar, modularComplexI_star_eq_neg (E := E)]
    _ = A * K := by
          simp
    _ = K * A := hCommMul

section

omit [CompleteSpace E]

/--
If `A` commutes with `K = Jε`, then the rotated seed `K ∘ A` also commutes
with `K`.
-/
theorem isPhaseLinear_modularComplexI_comp_of_IsPhaseLinear
    (A : EndH)
    (hComm :
      A.comp (InfoGeometry.Canonical.TomitaTakesaki.clockAxis)
        =
      (InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp A) :
    IsPhaseLinear (E := E) ((InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp A) := by
  unfold IsPhaseLinear at *
  calc
    ((InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp A).comp (InfoGeometry.Canonical.TomitaTakesaki.clockAxis)
        = (InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp (A.comp (InfoGeometry.Canonical.TomitaTakesaki.clockAxis)) := by
            simp [ContinuousLinearMap.comp_assoc]
    _ = (InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp ((InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp A) := by
          rw [hComm]
    _ = (InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp ((InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp A) := rfl

end

/--
Operatorial lift of the doubled real QGT from a Hilbert-self-adjoint operator
commuting with the local Cartan phase axis `K = Jε`.
-/
noncomputable def qgtOfOperator
    (A : EndH)
    (hA : IsSelfAdjoint A)
    (hComm :
      A.comp (InfoGeometry.Canonical.TomitaTakesaki.clockAxis)
        =
      (InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp A) : QGT E :=
  ofMajorana
    (metricOfOperator A)
    (metricOfOperator_isSymm_of_selfAdjoint (A := A) hA)
    (metricOfOperator_K_skew_of_commutesWithK (E := E) (A := A) hComm)

@[simp] theorem berryOfOperator_eq_qgtOfOperator_berry
    (A : EndH)
    (hA : IsSelfAdjoint A)
    (hComm :
      A.comp (InfoGeometry.Canonical.TomitaTakesaki.clockAxis)
        =
      (InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp A) :
    berryOfOperator (E := E) A
      =
    (qgtOfOperator (E := E) A hA hComm).berry := by
  simp [berryOfOperator, qgtOfOperator, GeometricQuantumTensor.ofMajorana]

/--
General doubled-carrier QGT constructor from a skew-adjoint, phase-linear seed:
rotate by the Cartan axis `K = Jε` to obtain a Hilbert-self-adjoint,
phase-linear operator, then apply `qgtOfOperator`.
-/
noncomputable def qgtOfSkewPhaseLinearOperator
    (A : EndH)
    (hSkew : star A = -A)
    (hPhase : IsPhaseLinear (E := E) A) : QGT E :=
  qgtOfOperator
    (E := E)
    ((InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp A)
    (isSelfAdjoint_modularComplexI_comp_of_star_eq_neg_of_commutesWithK
      (E := E) (A := A) hSkew hPhase)
    (isPhaseLinear_modularComplexI_comp_of_IsPhaseLinear
      (E := E) (A := A) hPhase)

/--
Berry sector readout for the general skew/phase-linear doubled-carrier QGT
constructor.
-/
@[simp] theorem qgtOfSkewPhaseLinearOperator_berry_eq_berryOfOperator
    (A : EndH)
    (hSkew : star A = -A)
    (hPhase : IsPhaseLinear (E := E) A) :
    (qgtOfSkewPhaseLinearOperator (E := E) A hSkew hPhase).berry
      =
    berryOfOperator (E := E) ((InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp A) := by
  symm
  exact berryOfOperator_eq_qgtOfOperator_berry
    (E := E)
    ((InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp A)
    (isSelfAdjoint_modularComplexI_comp_of_star_eq_neg_of_commutesWithK
      (E := E) (A := A) hSkew hPhase)
    (isPhaseLinear_modularComplexI_comp_of_IsPhaseLinear
      (E := E) (A := A) hPhase)

/--
For a skew-adjoint, phase-linear seed `A`, the Berry sector of the induced QGT
is exactly minus the operator metric seed of `A`.
-/
@[simp] theorem qgtOfSkewPhaseLinearOperator_berry_eq_neg_metricOfOperator
    (A : EndH)
    (hSkew : star A = -A)
    (hPhase : IsPhaseLinear (E := E) A) :
    (qgtOfSkewPhaseLinearOperator (E := E) A hSkew hPhase).berry
      =
    -metricOfOperator (E := E) A := by
  rw [qgtOfSkewPhaseLinearOperator_berry_eq_berryOfOperator
    (E := E) (A := A) hSkew hPhase]
  exact berryOfOperator_modularComplexI_comp_eq_neg_metricOfOperator_of_IsPhaseLinear
    (E := E) (A := A) hPhase

section StarCertifiedEinsteinAnomalyQGT

/--
The `K`-rotated lifted Einstein anomaly is Hilbert-self-adjoint on the
star-certified conformal surface.
-/
theorem isSelfAdjoint_modularComplexI_comp_liftedEinsteinAnomalyOperator
    (SCI : StarCertifiedConformalInference E) :
    IsSelfAdjoint ((InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp SCI.liftedEinsteinAnomalyOperator) := by
  exact isSelfAdjoint_modularComplexI_comp_of_star_eq_neg_of_commutesWithK
    (E := E) (A := SCI.liftedEinsteinAnomalyOperator)
    SCI.liftedEinsteinAnomalyOperator_star_eq_neg
    SCI.liftedEinsteinAnomalyOperator_isPhaseLinear

/--
The `K`-rotated lifted Einstein anomaly remains phase-linear on the doubled
carrier.
-/
theorem isPhaseLinear_modularComplexI_comp_liftedEinsteinAnomalyOperator
    (SCI : StarCertifiedConformalInference E) :
    IsPhaseLinear (E := E)
      ((InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp SCI.liftedEinsteinAnomalyOperator) := by
  exact isPhaseLinear_modularComplexI_comp_of_IsPhaseLinear
    (E := E) (A := SCI.liftedEinsteinAnomalyOperator)
    SCI.liftedEinsteinAnomalyOperator_isPhaseLinear

/--
Canonical QGT package generated by the `K`-rotated star-certified lifted Einstein
anomaly operator.
-/
noncomputable def starCertifiedEinsteinAnomalyQGT
    (SCI : StarCertifiedConformalInference E) : QGT E :=
  qgtOfSkewPhaseLinearOperator
    (E := E)
    SCI.liftedEinsteinAnomalyOperator
    SCI.liftedEinsteinAnomalyOperator_star_eq_neg
    SCI.liftedEinsteinAnomalyOperator_isPhaseLinear

/--
Berry sector readout of the canonical star-certified Einstein-anomaly QGT.
-/
@[simp] theorem starCertifiedEinsteinAnomalyQGT_berry_eq_berryOfOperator
    (SCI : StarCertifiedConformalInference E) :
    (starCertifiedEinsteinAnomalyQGT (E := E) SCI).berry
      =
    berryOfOperator
      (E := E)
      ((InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp SCI.liftedEinsteinAnomalyOperator) := by
  symm
  exact qgtOfSkewPhaseLinearOperator_berry_eq_berryOfOperator
    (E := E)
    SCI.liftedEinsteinAnomalyOperator
    SCI.liftedEinsteinAnomalyOperator_star_eq_neg
    SCI.liftedEinsteinAnomalyOperator_isPhaseLinear

/--
Hestenes/QGT weld closure on the star-certified conformal surface:
under projector agreement, the Berry sector of the `K`-twisted lifted Einstein
anomaly QGT is exactly the metric readout of the lifted projector obstruction.
-/
theorem starCertifiedEinsteinAnomalyQGT_berry_eq_metricOfOperator_liftedProjectorObstructionOperator_of_projectorAgreement
    (SCI : StarCertifiedConformalInference E)
    (hProj :
      InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.rightProjector SCI.A SCI.A_MP =
        InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.leftProjector SCI.A SCI.A_MP) :
    (starCertifiedEinsteinAnomalyQGT (E := E) SCI).berry
      =
    metricOfOperator (E := E)
      SCI.toCertifiedConformalInference.liftedProjectorObstructionOperator := by
  let CCI := SCI.toCertifiedConformalInference
  have hBerry :
      (starCertifiedEinsteinAnomalyQGT (E := E) SCI).berry
        =
      -metricOfOperator (E := E) SCI.liftedEinsteinAnomalyOperator := by
    simpa [starCertifiedEinsteinAnomalyQGT] using
      (qgtOfSkewPhaseLinearOperator_berry_eq_neg_metricOfOperator
        (E := E)
        (A := SCI.liftedEinsteinAnomalyOperator)
        SCI.liftedEinsteinAnomalyOperator_star_eq_neg
        SCI.liftedEinsteinAnomalyOperator_isPhaseLinear)
  have hEin :
      SCI.liftedEinsteinAnomalyOperator
        =
      -SCI.toCertifiedConformalInference.liftedProjectorObstructionOperator := by
    simpa [StarCertifiedConformalInference.liftedEinsteinAnomalyOperator] using
      CCI.liftedEinsteinAnomalyOperator_eq_neg_liftedProjectorObstructionOperator_of_projectorAgreement hProj
  calc
    (starCertifiedEinsteinAnomalyQGT (E := E) SCI).berry
        = -metricOfOperator (E := E) SCI.liftedEinsteinAnomalyOperator := hBerry
    _ = -metricOfOperator (E := E)
          (-SCI.toCertifiedConformalInference.liftedProjectorObstructionOperator) := by
            rw [hEin]
    _ = metricOfOperator (E := E)
          SCI.toCertifiedConformalInference.liftedProjectorObstructionOperator := by
            rw [metricOfOperator_neg]
            ext u v
            simp

end StarCertifiedEinsteinAnomalyQGT

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
      kreinMetricOfOperator A (InfoGeometry.Canonical.TomitaTakesaki.clockAxis u) v
        =
      -kreinMetricOfOperator A u (InfoGeometry.Canonical.TomitaTakesaki.clockAxis v) := by
  intro u v
  have hAntiEval :
      A (InfoGeometry.Canonical.TomitaTakesaki.clockAxis u)
        =
      -((InfoGeometry.Canonical.TomitaTakesaki.clockAxis) (A u)) := by
    have h := congrArg (fun T : EndH => T u) hAnti
    simpa [IsPhaseAntilinear, ContinuousLinearMap.comp_apply] using h
  rw [kreinMetricOfOperator_apply, kreinMetricOfOperator_apply, hAntiEval]
  calc
    KreinSpace.kreinInner (H := H₂) (-((InfoGeometry.Canonical.TomitaTakesaki.clockAxis) (A u))) v
      = -KreinSpace.kreinInner (H := H₂) ((InfoGeometry.Canonical.TomitaTakesaki.clockAxis) (A u)) v := by
          simp
    _ = -KreinSpace.kreinInner (H := H₂) (A u) ((InfoGeometry.Canonical.TomitaTakesaki.clockAxis) v) := by
          rw [modularComplexI_kreinInner_swap]
    _ = -kreinMetricOfOperator A u (InfoGeometry.Canonical.TomitaTakesaki.clockAxis v) := by
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

/-- Root-name form of the Hilbert/Krein operator metric transport by `spectral_epsilon`. -/
theorem metricOfOperator_spectral_epsilon_comp_eq_kreinMetricOfOperator
    (A : EndH) :
    metricOfOperator ((InfoGeometry.Krein.spectral_epsilon (E := E)).comp A)
      =
    kreinMetricOfOperator A := by
  simpa [modularSignEpsilon_eq_spectral_epsilon] using
    (metricOfOperator_modularSignEpsilon_comp_eq_kreinMetricOfOperator (E := E) A)

@[simp] theorem inner_modularSignEpsilon_apply_eq_kreinInner
    (u v : H₂) :
    ⟪(modularSignEpsilon (E := E)) u, v⟫_ℝ
      =
    KreinSpace.kreinInner (H := H₂) u v := by
  rw [krein_inner_prod_l2]
  simp [modularSignEpsilon, spectral_epsilon, WithLp.prod_inner_apply, sub_eq_add_neg]

/-- Root-name form of the left `spectral_epsilon` Krein-inner readout. -/
@[simp] theorem inner_spectral_epsilon_apply_eq_kreinInner
    (u v : H₂) :
    ⟪(InfoGeometry.Krein.spectral_epsilon (E := E)) u, v⟫_ℝ
      =
    KreinSpace.kreinInner (H := H₂) u v := by
  simpa [modularSignEpsilon_eq_spectral_epsilon] using
    (inner_modularSignEpsilon_apply_eq_kreinInner (E := E) u v)

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

/-- Root-name form of the right `spectral_epsilon` Krein-inner readout. -/
@[simp] theorem inner_apply_spectral_epsilon_eq_kreinInner
    (u v : H₂) :
    ⟪u, (InfoGeometry.Krein.spectral_epsilon (E := E)) v⟫_ℝ
      =
    KreinSpace.kreinInner (H := H₂) u v := by
  simpa [modularSignEpsilon_eq_spectral_epsilon] using
    (inner_apply_modularSignEpsilon_eq_kreinInner (E := E) u v)

/--
Modular-centered operator seed whose diagonal metric readout is the modular
variance.

This is the `ε`-transported square of the centered modular generator, so it
lands on the Hilbert-side operator lift while preserving the Krein variance
content on the state slice.
-/
noncomputable def modularVarianceSeed
    (ψ : H₂) (hMod : EndH) : EndH :=
  (modularSignEpsilon (E := E)).comp
    ((centeredModularGenerator (E := E) ψ hMod)
      * (centeredModularGenerator (E := E) ψ hMod))

/-- Root-name form of the modular-variance seed. -/
theorem modularVarianceSeed_eq_spectral_epsilon_comp
    (ψ : H₂) (hMod : EndH) :
    modularVarianceSeed (E := E) ψ hMod
      =
    (InfoGeometry.Krein.spectral_epsilon (E := E)).comp
      ((centeredModularGenerator (E := E) ψ hMod)
        * (centeredModularGenerator (E := E) ψ hMod)) := by
  simp [modularVarianceSeed, modularSignEpsilon_eq_spectral_epsilon]

/-- The modular-variance seed has exactly the modular variance on the diagonal metric slice. -/
theorem metricOfOperator_modularVarianceSeed_diag_eq_modularVariance
    (ψ : H₂) (hMod : EndH) :
    metricOfOperator (E := E) (modularVarianceSeed (E := E) ψ hMod) ψ ψ
      = modularVariance (E := E) ψ hMod := by
  let B : EndH :=
    (centeredModularGenerator (E := E) ψ hMod)
      * (centeredModularGenerator (E := E) ψ hMod)
  calc
    metricOfOperator (E := E) (modularVarianceSeed (E := E) ψ hMod) ψ ψ
        = ⟪(modularSignEpsilon (E := E)) (B ψ), ψ⟫_ℝ := by
            simp [metricOfOperator_apply, modularVarianceSeed, B, ContinuousLinearMap.comp_apply]
    _ = KreinSpace.kreinInner (H := H₂) (B ψ) ψ := by
          simpa using inner_modularSignEpsilon_apply_eq_kreinInner (E := E) (B ψ) ψ
    _ = KreinSpace.kreinInner (H := H₂) ψ (B ψ) := by
          simpa using (KreinSpace.kreinInner_symm (H := H₂) (B ψ) ψ)
    _ = modularVariance (E := E) ψ hMod := by
          simp [modularVariance, kreinExpectation, B]

/-- Main owner predicate: the QGT metric on a chosen state slice realizes modular variance. -/
def QGTRealizesModularVariance
    (Q : GeometricQuantumTensor E) (ψ : H₂) (hMod : EndH) : Prop :=
  Q.metric ψ ψ = modularVariance (E := E) ψ hMod

/--
Owner theorem: once the modular-variance seed is admitted by the Hilbert-side
QGT lift (`selfAdjoint` + Cartan-even commutation), the lifted QGT metric
realizes modular variance on the chosen state slice.
-/
theorem qgtOfOperator_modularVarianceSeed_realizes_modularVariance
    (ψ : H₂) (hMod : EndH)
    (hA : IsSelfAdjoint (modularVarianceSeed (E := E) ψ hMod))
    (hComm :
      (modularVarianceSeed (E := E) ψ hMod).comp (InfoGeometry.Canonical.TomitaTakesaki.clockAxis)
        =
      (InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp (modularVarianceSeed (E := E) ψ hMod)) :
    QGTRealizesModularVariance (E := E)
      (qgtOfOperator (E := E) (modularVarianceSeed (E := E) ψ hMod) hA hComm)
      ψ hMod := by
  exact metricOfOperator_modularVarianceSeed_diag_eq_modularVariance
    (E := E) ψ hMod

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

/-- Root-name form of Hilbert self-adjointness after `spectral_epsilon` transport. -/
theorem isSelfAdjoint_spectral_epsilon_comp_of_kreinSelfAdjoint
    (A : EndH)
    (hA : KreinSpace.IsKreinSelfAdjoint (H := H₂) A) :
    IsSelfAdjoint ((InfoGeometry.Krein.spectral_epsilon (E := E)).comp A) := by
  simpa [modularSignEpsilon_eq_spectral_epsilon] using
    (isSelfAdjoint_modularSignEpsilon_comp_of_kreinSelfAdjoint (E := E) (A := A) hA)

/--
Transport by the doubled fundamental symmetry `ε` sends the Cartan-odd /
phase-antilinear branch to the phase-linear branch.
-/
theorem isPhaseLinear_modularSignEpsilon_comp_of_IsPhaseAntilinear
    (A : EndH)
    (hAnti : IsPhaseAntilinear (E := E) A) :
    IsPhaseLinear (E := E) ((modularSignEpsilon (E := E)).comp A) := by
  have hAntiK :
      A.comp (InfoGeometry.Canonical.TomitaTakesaki.clockAxis)
        =
      -((InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp A) := by
    simpa [InfoGeometry.Canonical.TomitaTakesaki.clockAxis_eq_complex_i,
      InfoGeometry.Krein.clockAxis_eq_complex_i] using hAnti
  have hEpsK :
      (modularSignEpsilon (E := E)).comp (InfoGeometry.Canonical.TomitaTakesaki.clockAxis)
        =
      -(modularConjugationJ (E := E)) := by
    simpa [modularConjugationJ, modularSignEpsilon, modularComplexI] using
      (InfoGeometry.Krein.spectral_epsilon_comp_complex_i (E := E))
  have hKEps :
      (InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp (modularSignEpsilon (E := E))
        =
      modularConjugationJ (E := E) := by
    simpa [modularConjugationJ, modularSignEpsilon, modularComplexI] using
      (InfoGeometry.Krein.complex_i_comp_spectral_epsilon (E := E))
  unfold IsPhaseLinear IsPhaseAntilinear at *
  calc
    (((modularSignEpsilon (E := E)).comp A).comp (InfoGeometry.Canonical.TomitaTakesaki.clockAxis))
        = (modularSignEpsilon (E := E)).comp (A.comp (InfoGeometry.Canonical.TomitaTakesaki.clockAxis)) := by
            simp [ContinuousLinearMap.comp_assoc]
    _ = (modularSignEpsilon (E := E)).comp (-((InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp A)) := by
          rw [hAntiK]
    _ = -(((modularSignEpsilon (E := E)).comp (InfoGeometry.Canonical.TomitaTakesaki.clockAxis)).comp A) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = -((-(modularConjugationJ (E := E))).comp A) := by rw [hEpsK]
    _ = (modularConjugationJ (E := E)).comp A := by
          simp
    _ = ((InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp (modularSignEpsilon (E := E))).comp A := by rw [hKEps]
    _ = (InfoGeometry.Canonical.TomitaTakesaki.clockAxis).comp ((modularSignEpsilon (E := E)).comp A) := by
          simp [ContinuousLinearMap.comp_assoc]

/-- Root-name form of phase-linearity after `spectral_epsilon` transport. -/
theorem isPhaseLinear_spectral_epsilon_comp_of_IsPhaseAntilinear
    (A : EndH)
    (hAnti : IsPhaseAntilinear (E := E) A) :
    IsPhaseLinear (E := E) ((InfoGeometry.Krein.spectral_epsilon (E := E)).comp A) := by
  simpa [modularSignEpsilon_eq_spectral_epsilon] using
    (isPhaseLinear_modularSignEpsilon_comp_of_IsPhaseAntilinear
      (E := E) (A := A) hAnti)

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

/-- Root-name form of the Hilbert/Krein QGT metric agreement after `spectral_epsilon` transport. -/
theorem qgtOfOperator_spectral_epsilon_comp_metric_eq_kreinQgtOfOperator_metric
    (A : EndH)
    (hA : KreinSpace.IsKreinSelfAdjoint (H := H₂) A)
    (hAnti : IsPhaseAntilinear (E := E) A) :
    (qgtOfOperator
        (E := E)
        ((InfoGeometry.Krein.spectral_epsilon (E := E)).comp A)
        (isSelfAdjoint_spectral_epsilon_comp_of_kreinSelfAdjoint
          (E := E) (A := A) hA)
        (isPhaseLinear_spectral_epsilon_comp_of_IsPhaseAntilinear
          (E := E) (A := A) hAnti)).metric
      =
    (kreinQgtOfOperator (E := E) A hA hAnti).metric := by
  simpa [modularSignEpsilon_eq_spectral_epsilon] using
    (qgtOfOperator_modularSignEpsilon_comp_metric_eq_kreinQgtOfOperator_metric
      (E := E) (A := A) hA hAnti)

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

/-- Root-name form of the Hilbert/Krein QGT Berry agreement after `spectral_epsilon` transport. -/
theorem qgtOfOperator_spectral_epsilon_comp_berry_eq_kreinQgtOfOperator_berry
    (A : EndH)
    (hA : KreinSpace.IsKreinSelfAdjoint (H := H₂) A)
    (hAnti : IsPhaseAntilinear (E := E) A) :
    (qgtOfOperator
        (E := E)
        ((InfoGeometry.Krein.spectral_epsilon (E := E)).comp A)
        (isSelfAdjoint_spectral_epsilon_comp_of_kreinSelfAdjoint
          (E := E) (A := A) hA)
        (isPhaseLinear_spectral_epsilon_comp_of_IsPhaseAntilinear
          (E := E) (A := A) hAnti)).berry
      =
    (kreinQgtOfOperator (E := E) A hA hAnti).berry := by
  simpa [modularSignEpsilon_eq_spectral_epsilon] using
    (qgtOfOperator_modularSignEpsilon_comp_berry_eq_kreinQgtOfOperator_berry
      (E := E) (A := A) hA hAnti)

end GeometricQuantumTensor

end InfoGeometry.Quantum
