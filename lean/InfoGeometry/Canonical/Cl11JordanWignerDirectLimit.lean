import InfoGeometry.Canonical.Cl11SequentialColimitSystemBridge
import InfoGeometry.Clifford.JordanWignerCAR
import InfoGeometry.Clifford.CliffordBitWordEquivalence
import InfoGeometry.Clifford.Cl11MarkovJonesEngine
import InfoGeometry.Physics.ChiralSUSYBlockFactorization
import InfoGeometry.Clifford.SupergradedCliffordColimit

set_option autoImplicit false

/-!
# Jordan--Wigner generators in the `Cl(1,1)` algebraic direct limit

For a fixed site `k`, the finite Jordan--Wigner generator is represented at
all later stages by `jw_u k d` (and similarly for annihilation).  This file
proves that these representatives have a stage-independent image in the
existing algebraic direct limit, and transports the genuine finite CAR laws
to that image.  No Hilbert-space or C*-completion is asserted.
-/

namespace InfoGeometry.Canonical.Cl11JordanWignerDirectLimit

noncomputable section

open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.JordanWignerBridge
open InfoGeometry.Clifford.JordanWignerCAR
open InfoGeometry.Algebra
open InfoGeometry.Algebra.PrimonColimitAlgebra
open InfoGeometry.Algebra.CliffordBitWordEquivalence
open InfoGeometry.Physics
open InfoGeometry.Clifford.SupergradedCliffordColimit

abbrev Limit := InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit

def jwUImage (k d : ℕ) : Limit :=
  ofStage (k + 1 + d) (jw_u k d)

def jwVImage (k d : ℕ) : Limit :=
  ofStage (k + 1 + d) (jw_v k d)

theorem jwUImage_succ (k d : ℕ) :
    jwUImage k (d + 1) = jwUImage k d := by
  rw [jwUImage, jwUImage, ← matStageEmbed_jw_u k d]
  exact ofStage_apply_bond (k + 1 + d) (jw_u k d)

theorem jwVImage_succ (k d : ℕ) :
    jwVImage k (d + 1) = jwVImage k d := by
  rw [jwVImage, jwVImage, ← matStageEmbed_jw_v k d]
  exact ofStage_apply_bond (k + 1 + d) (jw_v k d)

theorem jwUImage_eq_base (k d : ℕ) :
    jwUImage k d = jwUImage k 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [jwUImage_succ, ih]

theorem jwVImage_eq_base (k d : ℕ) :
    jwVImage k d = jwVImage k 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [jwVImage_succ, ih]

theorem jwUImage_sq (k d : ℕ) :
    jwUImage k d * jwUImage k d = 0 := by
  rw [jwUImage_eq_base k d]
  simp only [jwUImage, jw_u, embedToStage]
  rw [← ofStage_mul]
  simpa using congrArg (ofStage (k + 1)) (jw_u_new_sq k)

theorem jwVImage_sq (k d : ℕ) :
    jwVImage k d * jwVImage k d = 0 := by
  rw [jwVImage_eq_base k d]
  simp only [jwVImage, jw_v, embedToStage]
  rw [← ofStage_mul]
  simpa using congrArg (ofStage (k + 1)) (jw_v_new_sq k)

theorem jwUVImage_anticomm (k d : ℕ) :
    jwUImage k d * jwVImage k d + jwVImage k d * jwUImage k d = 1 := by
  rw [jwUImage_eq_base k d, jwVImage_eq_base k d]
  simp only [jwUImage, jwVImage, jw_u, jw_v, embedToStage]
  rw [← ofStage_mul, ← ofStage_mul, ← ofStage_add]
  simpa using congrArg (ofStage (k + 1)) (jw_uv_anticomm_new k)

/-! The fixed-site CAR representatives are now read in the BitWord/UHF
coordinate presentation through the existing finite-stage equivalence. -/

@[simp] theorem cliffordBitWordColimitEquiv_jwUImage (k d : ℕ) :
    cliffordBitWordColimitEquiv (jwUImage k d) =
      PrimonColimitAlgebra.toColimit (k + 1 + d)
        (clStageEquiv (k + 1 + d) (jw_u k d)) := by
  exact cliffordBitWordColimitEquiv_ofStage (k + 1 + d) (jw_u k d)

@[simp] theorem cliffordBitWordColimitEquiv_jwVImage (k d : ℕ) :
    cliffordBitWordColimitEquiv (jwVImage k d) =
      PrimonColimitAlgebra.toColimit (k + 1 + d)
        (clStageEquiv (k + 1 + d) (jw_v k d)) := by
  exact cliffordBitWordColimitEquiv_ofStage (k + 1 + d) (jw_v k d)

theorem cliffordBitWordColimitEquiv_jwUImage_sq (k d : ℕ) :
    cliffordBitWordColimitEquiv (jwUImage k d) *
        cliffordBitWordColimitEquiv (jwUImage k d) = 0 := by
  rw [← map_mul]
  rw [jwUImage_sq]
  exact map_zero cliffordBitWordColimitEquiv

theorem cliffordBitWordColimitEquiv_jwVImage_sq (k d : ℕ) :
    cliffordBitWordColimitEquiv (jwVImage k d) *
        cliffordBitWordColimitEquiv (jwVImage k d) = 0 := by
  rw [← map_mul]
  rw [jwVImage_sq]
  exact map_zero cliffordBitWordColimitEquiv

theorem cliffordBitWordColimitEquiv_jwUVImage_anticomm (k d : ℕ) :
    cliffordBitWordColimitEquiv (jwUImage k d) *
          cliffordBitWordColimitEquiv (jwVImage k d) +
        cliffordBitWordColimitEquiv (jwVImage k d) *
          cliffordBitWordColimitEquiv (jwUImage k d) = 1 := by
  rw [← map_mul, ← map_mul, ← map_add, jwUVImage_anticomm]
  exact map_one cliffordBitWordColimitEquiv

private theorem trace_jw_u_new (k : ℕ) :
    Matrix.trace (jw_u_new k) = 0 := by
  unfold jw_u_new
  rw [Matrix.trace_kronecker]
  simp [a_dagger_base, Matrix.trace, Fin.sum_univ_two]

private theorem trace_jw_v_new (k : ℕ) :
    Matrix.trace (jw_v_new k) = 0 := by
  unfold jw_v_new
  rw [Matrix.trace_kronecker]
  simp [a_base, Matrix.trace, Fin.sum_univ_two]

private theorem trace_jw_u (k d : ℕ) :
    Matrix.trace (jw_u k d) = 0 := by
  induction d with
  | zero => simpa [jw_u] using trace_jw_u_new k
  | succ d ih =>
      rw [← matStageEmbed_jw_u k d, matStageEmbed_trace, ih]
      ring

private theorem trace_jw_v (k d : ℕ) :
    Matrix.trace (jw_v k d) = 0 := by
  induction d with
  | zero => simpa [jw_v] using trace_jw_v_new k
  | succ d ih =>
      rw [← matStageEmbed_jw_v k d, matStageEmbed_trace, ih]
      ring

theorem tauInfinity_cliffordBitWordColimitEquiv_jwUImage (k d : ℕ) :
    tauInfinity (cliffordBitWordColimitEquiv (jwUImage k d)) = 0 := by
  rw [cliffordBitWordColimitEquiv_jwUImage]
  rw [PrimonColimitAlgebra.tauInfinity_stage]
  unfold PrimonColimitAlgebra.normalizedTrace
    PrimonColimitAlgebra.rawTrace
  rw [clStageEquiv_trace, trace_jw_u]
  simp

theorem tauInfinity_cliffordBitWordColimitEquiv_jwVImage (k d : ℕ) :
    tauInfinity (cliffordBitWordColimitEquiv (jwVImage k d)) = 0 := by
  rw [cliffordBitWordColimitEquiv_jwVImage]
  rw [PrimonColimitAlgebra.tauInfinity_stage]
  unfold PrimonColimitAlgebra.normalizedTrace
    PrimonColimitAlgebra.rawTrace
  rw [clStageEquiv_trace, trace_jw_v]
  simp

theorem tauInfinity_cliffordBitWordColimitEquiv_stage
    (n : ℕ) (A : ClStage n) :
    tauInfinity
        (cliffordBitWordColimitEquiv
          (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n A)) =
      InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace n A := by
  rw [cliffordBitWordColimitEquiv_ofStage,
    PrimonColimitAlgebra.tauInfinity_stage]
  exact normalizedTrace_clStageEquiv n A

theorem tauInfinity_cliffordBitWordColimitEquiv_markovTrace
    (n : ℕ) (A : ClStage n) :
    tauInfinity
        (cliffordBitWordColimitEquiv
          (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n A)) =
      InfoGeometry.Clifford.Cl11MarkovJonesEngine.cl11MarkovTraceNet.trace n A := by
  rw [tauInfinity_cliffordBitWordColimitEquiv_stage]
  exact (InfoGeometry.Clifford.Cl11MarkovJonesEngine.cl11MarkovTraceNet_apply n A).symm

theorem tauInfinity_cliffordBitWordColimitEquiv_commutator_zero
    (x y : Limit) :
    tauInfinity
        (cliffordBitWordColimitEquiv (x * y - y * x)) = 0 := by
  rw [map_sub, map_mul, map_mul]
  exact PrimonColimitAlgebra.tauInfinity_commutator_zero
    (cliffordBitWordColimitEquiv x) (cliffordBitWordColimitEquiv y)

/-- The odd chiral block has zero carrier trace.  This is the finite
    supertrace readout transported to the unified algebraic colimit. -/
theorem tauInfinity_chiralQPlus_trace_zero (a : Limit) :
    tauInfinity
        (cliffordBitWordColimitEquiv
          (Matrix.trace (chiralQPlus (A := Limit) a))) = 0 := by
  simp [chiralQPlus, Matrix.trace, Fin.sum_univ_two]

/-- The opposite odd chiral block has zero carrier trace as well. -/
theorem tauInfinity_chiralQMinus_trace_zero (a : Limit) :
    tauInfinity
        (cliffordBitWordColimitEquiv
          (Matrix.trace (chiralQMinus (A := Limit) a))) = 0 := by
  simp [chiralQMinus, Matrix.trace, Fin.sum_univ_two]

theorem tauInfinity_chiralSUSYHamiltonian_jw (k d : ℕ) :
    tauInfinity
        (cliffordBitWordColimitEquiv
          (Matrix.trace
            (chiralSUSYHamiltonian (A := Limit)
              (jwUImage k d) (jwVImage k d)))) = 1 := by
  have htrace (a b : Limit) :
      Matrix.trace (chiralSUSYHamiltonian (A := Limit) a b) = a * b + b * a := by
    simp [chiralSUSYHamiltonian, chiralQPlus, chiralQMinus,
      Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  rw [htrace, jwUVImage_anticomm]
  simpa using InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity_one

theorem tauInfinity_chiralDirac_square_jw (k d : ℕ) :
    tauInfinity
        (cliffordBitWordColimitEquiv
          (Matrix.trace
            (chiralDirac (A := Limit) (jwUImage k d) (jwVImage k d) *
              chiralDirac (A := Limit) (jwUImage k d) (jwVImage k d)))) = 1 := by
  rw [chiralDirac_sq_eq_susyHamiltonian]
  exact tauInfinity_chiralSUSYHamiltonian_jw k d

/-- The Jordan--Wigner SUSY Hamiltonian has nonzero ordinary trace readout,
but its parity-inserted chiral supertrace vanishes by tracial cyclicity. -/
theorem tauInfinity_chiralSupertrace_hamiltonian_jw (k d : ℕ) :
    tauInfinity
        (cliffordBitWordColimitEquiv
          (Matrix.trace
            (chiralParity *
              chiralSUSYHamiltonian (A := Limit)
                (jwUImage k d) (jwVImage k d)))) = 0 := by
  rw [chiral_supertrace_hamiltonian_eq_commutator]
  rw [map_sub, map_mul, map_mul]
  exact tauInfinity_commutator_zero _ _

end

end InfoGeometry.Canonical.Cl11JordanWignerDirectLimit
