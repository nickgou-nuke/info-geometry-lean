import InfoGeometry.Physics.TraceJordanLieDriverBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Physics

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Conservative, Hamiltonian-style driver in the trace bimodule. -/
def conservativeDriver (H X : TraceOperatorSpace n) : TraceOperatorSpace n :=
  commutatorDriver H X

/-- Dissipative, Jordan-style driver in the trace bimodule. -/
def dissipativeDriver (S X : TraceOperatorSpace n) : TraceOperatorSpace n :=
  jordanDriver S X

/-- Combined algebraic driver. This is the trace-bimodule sum, not yet a
full density-matrix metriplectic flow law. -/
def metriplecticGenerator (H S X : TraceOperatorSpace n) : TraceOperatorSpace n :=
  conservativeDriver H X + dissipativeDriver S X

theorem conservative_driver_trace_skew (H X Y : TraceOperatorSpace n) :
    tracePairingNative (conservativeDriver H X) Y =
      - tracePairingNative X (conservativeDriver H Y) := by
  simpa [conservativeDriver] using
    commutatorDriver_tracePairing_skew (n := n) H X Y

theorem dissipative_driver_trace_symmetric (S X Y : TraceOperatorSpace n) :
    tracePairingNative (dissipativeDriver S X) Y =
      tracePairingNative X (dissipativeDriver S Y) := by
  simpa [dissipativeDriver] using
    jordanDriver_tracePairing_symmetric (n := n) S X Y

/-! The conservative and dissipative contributions remain separated at the
trace-pairing level.  This is the native noncommutative replacement for
calling the whole metriplectic generator either skew or symmetric. -/
theorem metriplectic_generator_tracePairing_decomposition
    (H S X Y : TraceOperatorSpace n) :
    tracePairingNative (metriplecticGenerator H S X) Y =
      - tracePairingNative X (conservativeDriver H Y) +
        tracePairingNative X (dissipativeDriver S Y) := by
  calc
    tracePairingNative (metriplecticGenerator H S X) Y =
        tracePairingNative (conservativeDriver H X) Y +
          tracePairingNative (dissipativeDriver S X) Y := by
      rw [metriplecticGenerator, tracePairingNative, Matrix.add_mul,
        Matrix.trace_add]
      rfl
    _ = - tracePairingNative X (conservativeDriver H Y) +
          tracePairingNative X (dissipativeDriver S Y) := by
      rw [conservative_driver_trace_skew, dissipative_driver_trace_symmetric]

theorem conservative_driver_self_tracePairing_zero
    (H X : TraceOperatorSpace n) :
    tracePairingNative (conservativeDriver H X) X = 0 := by
  have h := conservative_driver_trace_skew H X X
  have hcomm := tracePairing_native_comm
    (conservativeDriver H X) X
  linarith

theorem metriplectic_generator_self_tracePairing_eq_dissipative
    (H S X : TraceOperatorSpace n) :
    tracePairingNative (metriplecticGenerator H S X) X =
      tracePairingNative (dissipativeDriver S X) X := by
  calc
    tracePairingNative (metriplecticGenerator H S X) X =
        tracePairingNative (conservativeDriver H X) X +
          tracePairingNative (dissipativeDriver S X) X := by
      rw [metriplecticGenerator, tracePairingNative, Matrix.add_mul,
        Matrix.trace_add]
      rfl
    _ = 0 + tracePairingNative (dissipativeDriver S X) X := by
      rw [conservative_driver_self_tracePairing_zero]
    _ = tracePairingNative (dissipativeDriver S X) X := zero_add _

theorem conservative_energy_conservation (H X : TraceOperatorSpace n) :
    tracePairingNative H (conservativeDriver H X) = 0 := by
  simpa [conservativeDriver] using
    commutatorDriver_energy_orthogonal (n := n) H X

/-! The coupling-weighted total driver is the canonical single operator for
the metriplectic evolution.  The two summands remain noncommutative matrix
actions; `γ` only controls the strength of the Jordan direction. -/
def weightedMetriplecticGenerator (γ : ℝ) (H S X : TraceOperatorSpace n) :
    TraceOperatorSpace n :=
  conservativeDriver H X + γ • dissipativeDriver S X

/- The same total generator, now exposed as the single linear operator acting
   on the state variable.  This is the canonical operator-level packaging of
   the metriplectic evolution. -/
def weightedMetriplecticOperator (γ : ℝ)
    (H S : TraceOperatorSpace n) :
    TraceOperatorSpace n →ₗ[ℝ] TraceOperatorSpace n where
  toFun := weightedMetriplecticGenerator γ H S
  map_add' := by
    intro X Y
    simp [weightedMetriplecticGenerator, conservativeDriver,
      dissipativeDriver, commutatorDriver, commutatorActionNative,
      jordanActionNative, leftActionNative, rightActionNative,
      Matrix.add_mul, Matrix.mul_add, smul_add]
    unfold jordanDriver jordanActionNative leftActionNative rightActionNative
    simp only [Matrix.mul_add, Matrix.add_mul, smul_add]
    abel
  map_smul' := by
    intro a X
    simp [weightedMetriplecticGenerator, conservativeDriver,
      dissipativeDriver, commutatorDriver, commutatorActionNative,
      jordanActionNative, leftActionNative, rightActionNative,
      Matrix.add_mul, Matrix.mul_add, smul_add]
    unfold jordanDriver jordanActionNative leftActionNative rightActionNative
    simp only [smul_add]
    ext i j
    simp [Matrix.mul_apply, Finset.mul_sum]
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
    ring

@[simp] theorem weightedMetriplecticOperator_apply
    (γ : ℝ) (H S X : TraceOperatorSpace n) :
    weightedMetriplecticOperator γ H S X =
      weightedMetriplecticGenerator γ H S X := rfl

@[simp] theorem weightedMetriplecticGenerator_zero (H S X : TraceOperatorSpace n) :
    weightedMetriplecticGenerator 0 H S X = conservativeDriver H X := by
  simp [weightedMetriplecticGenerator]

@[simp] theorem weightedMetriplecticOperator_zero (H S X : TraceOperatorSpace n) :
    weightedMetriplecticOperator 0 H S X = conservativeDriver H X := by
  rw [weightedMetriplecticOperator_apply, weightedMetriplecticGenerator_zero]

theorem weightedMetriplecticGenerator_add
    (γ₁ γ₂ : ℝ) (H S X : TraceOperatorSpace n) :
    weightedMetriplecticGenerator (γ₁ + γ₂) H S X =
      weightedMetriplecticGenerator γ₁ H S X + γ₂ • dissipativeDriver S X := by
  simp only [weightedMetriplecticGenerator, add_smul]
  abel

theorem weighted_metriplectic_generator_decomposition
    (γ : ℝ) (H S X Y : TraceOperatorSpace n) :
    tracePairingNative (weightedMetriplecticGenerator γ H S X) Y =
      - tracePairingNative X (conservativeDriver H Y) +
        γ * tracePairingNative X (dissipativeDriver S Y) := by
  calc
    tracePairingNative (weightedMetriplecticGenerator γ H S X) Y =
        tracePairingNative (conservativeDriver H X) Y +
          γ * tracePairingNative (dissipativeDriver S X) Y := by
      rw [weightedMetriplecticGenerator, tracePairingNative, Matrix.add_mul,
        Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul]
      rfl
    _ = - tracePairingNative X (conservativeDriver H Y) +
          γ * tracePairingNative X (dissipativeDriver S Y) := by
      rw [conservative_driver_trace_skew, dissipative_driver_trace_symmetric]

theorem weightedMetriplecticOperator_tracePairing_decomposition
    (γ : ℝ) (H S X Y : TraceOperatorSpace n) :
    tracePairingNative (weightedMetriplecticOperator γ H S X) Y =
      - tracePairingNative X (conservativeDriver H Y) +
        γ * tracePairingNative X (dissipativeDriver S Y) := by
  rw [weightedMetriplecticOperator_apply]
  exact weighted_metriplectic_generator_decomposition γ H S X Y

theorem weighted_metriplectic_generator_self_tracePairing
    (γ : ℝ) (H S X : TraceOperatorSpace n) :
    tracePairingNative (weightedMetriplecticGenerator γ H S X) X =
      γ * tracePairingNative (dissipativeDriver S X) X := by
  calc
    tracePairingNative (weightedMetriplecticGenerator γ H S X) X =
        - tracePairingNative X (conservativeDriver H X) +
          γ * tracePairingNative X (dissipativeDriver S X) := by
      exact weighted_metriplectic_generator_decomposition γ H S X X
    _ = γ * tracePairingNative (dissipativeDriver S X) X := by
      have hzero : tracePairingNative (conservativeDriver H X) X = 0 :=
        conservative_driver_self_tracePairing_zero H X
      have hcon : tracePairingNative X (conservativeDriver H X) =
          tracePairingNative (conservativeDriver H X) X := by
        exact tracePairing_native_comm _ _
      have hcomm : tracePairingNative X (dissipativeDriver S X) =
          tracePairingNative (dissipativeDriver S X) X := by
        exact tracePairing_native_comm _ _
      simp [hcon, hzero, hcomm]

theorem weighted_metriplectic_generator_self_tracePairing_nonneg
    {γ : ℝ} (H S X : TraceOperatorSpace n) (hγ : 0 ≤ γ)
    (hD : 0 ≤ tracePairingNative (dissipativeDriver S X) X) :
    0 ≤ tracePairingNative
      (weightedMetriplecticGenerator γ H S X) X := by
  rw [weighted_metriplectic_generator_self_tracePairing]
  exact mul_nonneg hγ hD

theorem weightedMetriplecticOperator_self_tracePairing
    (γ : ℝ) (H S X : TraceOperatorSpace n) :
    tracePairingNative (weightedMetriplecticOperator γ H S X) X =
      γ * tracePairingNative (dissipativeDriver S X) X := by
  rw [weightedMetriplecticOperator_apply]
  exact weighted_metriplectic_generator_self_tracePairing γ H S X

theorem weightedMetriplecticOperator_self_tracePairing_nonneg
    {γ : ℝ} (H S X : TraceOperatorSpace n) (hγ : 0 ≤ γ)
    (hD : 0 ≤ tracePairingNative (dissipativeDriver S X) X) :
    0 ≤ tracePairingNative
      (weightedMetriplecticOperator γ H S X) X := by
  rw [weightedMetriplecticOperator_self_tracePairing]
  exact mul_nonneg hγ hD

@[simp] theorem weighted_metriplectic_generator_zero_self_tracePairing
    (H S X : TraceOperatorSpace n) :
    tracePairingNative
      (weightedMetriplecticGenerator 0 H S X) X = 0 := by
  rw [weighted_metriplectic_generator_self_tracePairing]
  simp

end InfoGeometry.Physics
