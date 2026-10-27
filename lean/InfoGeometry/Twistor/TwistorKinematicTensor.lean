import InfoGeometry.Twistor.PerjesConventions
import InfoGeometry.Twistor.InfinityTwistor
import InfoGeometry.Twistor.SpinorOuterProduct

/-!
# The symmetric kinematic twistor

Perjes (6.4): A = Z tensor I#(Zbar) + I#(Zbar) tensor Z.
The contravariant infinity tensor is separately constructed, not an inverse
of the degenerate covariant infinity form. This tensor is not a Pluecker bivector.
-/
noncomputable section
namespace InfoGeometry.Twistor.TwistorKinematicTensor
open PenroseIncidence PerjesConventions
open scoped BigOperators Matrix

def conjugateDual : Twistor4 →ₗ⋆[ℂ] Module.Dual ℂ Twistor4 where
  toFun Z :=
    { toFun := pairing Z
      map_add' := by intros; simp [pairing,mul_add]; ring
      map_smul' := by intros; simp [pairing,smul_eq_mul]; ring }
  map_add' Z W := by
    apply LinearMap.ext
    intro V
    change pairing (Z+W) V=pairing Z V+pairing W V
    simp [pairing,star_add,add_mul]
    ring
  map_smul' c Z := by
    apply LinearMap.ext
    intro V
    change pairing (c • Z) V=star c * pairing Z V
    simp [pairing,smul_eq_mul,star_mul]
    ring

def upperBasis (i : Fin 2) : Twistor4 := (Pi.single i 1,0)

def infinitySharp : Module.Dual ℂ Twistor4 →ₗ[ℂ] Twistor4 where
  toFun φ := (![φ (upperBasis 1),-φ (upperBasis 0)],0)
  map_add' φ ψ := by ext i <;> fin_cases i <;> simp [add_comm]
  map_smul' c φ := by ext i <;> fin_cases i <;> simp

def raised : Twistor4 →ₗ⋆[ℂ] Twistor4 := infinitySharp.comp conjugateDual

@[simp] theorem raised_apply (Z : Twistor4) :
    raised Z=(![star (Z.2 1),-star (Z.2 0)],0) := by
  simp [raised,infinitySharp,conjugateDual,upperBasis,pairing]

@[simp] theorem raised_twice (Z : Twistor4) : raised (raised Z)=0 := by simp

theorem infinitySharp_covariant_zero (Z : Twistor4) :
    infinitySharp (InfinityTwistor.infinityTwistor Z)=0 := by
  ext i <;> fin_cases i <;>
    simp [infinitySharp,upperBasis,InfinityTwistor.infinityTwistor_apply]

theorem covariant_infinitySharp_zero (φ : Module.Dual ℂ Twistor4) :
    InfinityTwistor.infinityTwistor (infinitySharp φ)=0 := by
  apply LinearMap.ext
  intro W
  simp [InfinityTwistor.infinityTwistor_apply,infinitySharp]

def kinematic (Z : Twistor4) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.vecMulVec (coordinateEquiv Z) (coordinateEquiv (raised Z)) +
  Matrix.vecMulVec (coordinateEquiv (raised Z)) (coordinateEquiv Z)

theorem kinematic_symmetric (Z : Twistor4) : (kinematic Z).transpose=kinematic Z := by
  ext i j
  simp [kinematic,Matrix.vecMulVec,Matrix.transpose_apply]
  ring

theorem kinematic_scaling (c : ℂ) (Z : Twistor4) :
    kinematic (c • Z)=(c*star c) • kinematic Z := by
  have hr : raised (c • Z)=star c • raised Z := raised.map_smulₛₗ c Z
  ext i j
  simp only [kinematic,hr,map_smul,Matrix.add_apply,Matrix.vecMulVec,
    Pi.smul_apply,smul_eq_mul]
  ring

theorem kinematic_phase_invariant (c : ℂ) (hc : c*star c=1) (Z : Twistor4) :
    kinematic (c • Z)=kinematic Z := by rw [kinematic_scaling,hc,one_smul]

def momentum (π : Spinor2) : ComplexSpacetime := Matrix.vecMulVec π (star π)

def momentumReadout (A : Matrix (Fin 4) (Fin 4) ℂ) : ComplexSpacetime :=
  !![-A 1 2,A 0 2; -A 1 3,A 0 3]

theorem momentumReadout_kinematic (Z : Twistor4) :
    momentumReadout (kinematic Z)=momentum Z.2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [momentumReadout,kinematic,momentum,coordinateEquiv,Matrix.vecMulVec] <;> ring

def angularSpinor (Z : Twistor4) : ComplexSpacetime :=
  (Complex.I/2) • !![(kinematic Z) 0 0,(kinematic Z) 0 1;
    (kinematic Z) 1 0,(kinematic Z) 1 1]

theorem angular_block (Z : Twistor4) :
    (-2*Complex.I) • angularSpinor Z=
      !![(kinematic Z) 0 0,(kinematic Z) 0 1;
        (kinematic Z) 1 0,(kinematic Z) 1 1] := by
  unfold angularSpinor
  rw [smul_smul]
  have h : (-2*Complex.I)*(Complex.I/2)=(1:ℂ) := by
    calc (-2*Complex.I)*(Complex.I/2) = -(Complex.I^2) := by ring
      _ = 1 := by rw [Complex.I_sq]; norm_num
  rw [h,one_smul]

theorem momentum_hermitian (π : Spinor2) : (momentum π).conjTranspose=momentum π := by
  ext i j
  simp [momentum,Matrix.vecMulVec,Matrix.conjTranspose_apply,star_mul]

theorem momentum_det_zero (π : Spinor2) : (momentum π).det=0 := by
  simp [momentum,Matrix.det_fin_two,Matrix.vecMulVec]
  ring

theorem momentum_trace (π : Spinor2) :
    (Matrix.trace (momentum π)).re=Complex.normSq (π 0)+Complex.normSq (π 1) := by
  simp [momentum,Matrix.trace,Matrix.vecMulVec,Fin.sum_univ_two,
    Complex.mul_re,Complex.normSq_apply]

theorem momentum_trace_nonnegative (π : Spinor2) : 0 ≤ (Matrix.trace (momentum π)).re := by
  rw [momentum_trace]
  exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

theorem momentum_trace_positive (π : Spinor2) (hπ : π ≠ 0) :
    0 < (Matrix.trace (momentum π)).re := by
  rw [momentum_trace]
  have h0 := Complex.normSq_nonneg (π 0)
  have h1 := Complex.normSq_nonneg (π 1)
  by_contra hn
  have hz0 : Complex.normSq (π 0)=0 := by linarith
  have hz1 : Complex.normSq (π 1)=0 := by linarith
  apply hπ
  funext i
  fin_cases i
  · exact Complex.normSq_eq_zero.mp hz0
  · exact Complex.normSq_eq_zero.mp hz1

theorem two_constituent_mass (π ρ : Spinor2) :
    (momentum π+momentum ρ).det=
      (π 0*ρ 1-π 1*ρ 0)*star (π 0*ρ 1-π 1*ρ 0) :=
  SpinorOuterProduct.det_sum_self_outer π ρ

end InfoGeometry.Twistor.TwistorKinematicTensor
