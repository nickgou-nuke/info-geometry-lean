import Mathlib.Analysis.InnerProductSpace.PiL2
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Topology.Algebra.Module.FiniteDimension
import InfoGeometry.Dynamics.EntropicTokenDynamics

/-!
# The canonical Hilbert carrier for token trajectories

`TokenHilbertSpace` is retained as the raw finite-function carrier.  This
module supplies the `PiLp` realization needed by Mathlib's calculus and
inner-product APIs; it does not identify the two carriers by definitional
equality.
-/

namespace InfoGeometry.Dynamics

noncomputable section

variable {V : Type*} [Fintype V]

open Set
open scoped NNReal

/-- The finite `L²` carrier on which Mathlib provides an inner product. -/
abbrev TokenPiLpSpace (V : Type*) [Fintype V] :=
  PiLp 2 (fun _ : V × Fin 2 => ℂ)

/-- The canonical linear lift of a raw token function into the `PiLp` carrier. -/
def tokenToPiLp : TokenHilbertSpace V →ₗ[ℂ] TokenPiLpSpace V :=
  (WithLp.linearEquiv 2 ℂ (V × Fin 2 → ℂ)).symm.toLinearMap

/-- The inverse carrier map, used to transport operators without changing
    the underlying token dynamics. -/
def tokenFromPiLp : TokenPiLpSpace V →ₗ[ℂ] TokenHilbertSpace V :=
  (WithLp.linearEquiv 2 ℂ (V × Fin 2 → ℂ)).toLinearMap

@[simp] theorem tokenToPiLp_fromPiLp (ψ : TokenPiLpSpace V) :
    tokenToPiLp (tokenFromPiLp ψ) = ψ := by
  exact (WithLp.linearEquiv 2 ℂ (V × Fin 2 → ℂ)).symm_apply_apply ψ

@[simp] theorem tokenFromPiLp_toPiLp (ψ : TokenHilbertSpace V) :
    tokenFromPiLp (tokenToPiLp ψ) = ψ := by
  exact (WithLp.linearEquiv 2 ℂ (V × Fin 2 → ℂ)).apply_symm_apply ψ

/-- Conjugate a raw complex-linear generator to the `PiLp` carrier. -/
def transportTokenGenerator (gen : TokenGenerator V) :
    TokenPiLpSpace V →ₗ[ℂ] TokenPiLpSpace V :=
  tokenToPiLp.comp ((totalTokenGenerator gen).comp tokenFromPiLp)

@[simp] theorem transportTokenGenerator_apply (gen : TokenGenerator V)
    (ψ : TokenPiLpSpace V) :
    transportTokenGenerator gen ψ =
      tokenToPiLp (totalTokenGenerator gen (tokenFromPiLp ψ)) := rfl

/-! The complex generator can also be viewed as a real-linear generator on the
    same `PiLp` carrier.  This is scalar restriction, not a new dynamics. -/
def transportTokenGeneratorReal (gen : TokenGenerator V) :
    TokenPiLpSpace V →ₗ[ℝ] TokenPiLpSpace V :=
  (transportTokenGenerator gen).restrictScalars ℝ

@[simp] theorem transportTokenGeneratorReal_apply (gen : TokenGenerator V)
    (ψ : TokenPiLpSpace V) :
    transportTokenGeneratorReal gen ψ = transportTokenGenerator gen ψ := rfl

theorem transportTokenGeneratorReal_round_trip (gen : TokenGenerator V)
    (ψ : TokenHilbertSpace V) :
    tokenFromPiLp (transportTokenGeneratorReal gen (tokenToPiLp ψ)) =
      totalTokenGenerator gen ψ := by
  simp [transportTokenGeneratorReal, transportTokenGenerator]

theorem transportTokenGenerator_round_trip (gen : TokenGenerator V)
    (ψ : TokenHilbertSpace V) :
    tokenFromPiLp (transportTokenGenerator gen (tokenToPiLp ψ)) =
      totalTokenGenerator gen ψ := by
  simp [transportTokenGenerator]

@[simp] theorem tokenToPiLp_apply (ψ : TokenHilbertSpace V) :
    tokenToPiLp ψ = WithLp.toLp 2 ψ := by
  rfl

@[simp] theorem tokenPiLp_inner_apply (ψ φ : TokenPiLpSpace V) :
    inner ℂ ψ φ = ∑ x, inner ℂ (ψ x) (φ x) := by
  rfl

theorem tokenPiLp_norm_sq (ψ : TokenPiLpSpace V) :
    ‖ψ‖ ^ 2 = (inner ℂ ψ ψ).re := by
  simp [pow_two]

/-- A differentiable trajectory contract for a finite `PiLp` generator. -/
structure TokenPiLpTrajectory (G : TokenPiLpSpace V →ₗ[ℝ] TokenPiLpSpace V) where
  state : ℝ → TokenPiLpSpace V
  equation : ∀ t, HasDerivAt state (G (state t)) t

theorem exists_tokenPiLp_trajectory_on_Icc
    (G : TokenPiLpSpace V →ₗ[ℝ] TokenPiLpSpace V)
    {tmin tmax : ℝ} (t₀ : Set.Icc tmin tmax) (ψ₀ : TokenPiLpSpace V)
    {a r L K : ℝ≥0}
    (hG : IsPicardLindelof (fun _ ψ => G ψ) t₀ ψ₀ a r L K)
    (hψ : ψ₀ ∈ Metric.closedBall ψ₀ r) :
    ∃ ψ : ℝ → TokenPiLpSpace V, ψ t₀ = ψ₀ ∧
      ∀ t ∈ Set.Icc tmin tmax,
        HasDerivWithinAt ψ (G (ψ t)) (Set.Icc tmin tmax) t := by
  exact IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt hG hψ

theorem tokenPiLp_trajectory_hasDerivAt_interior
    {G : TokenPiLpSpace V →ₗ[ℝ] TokenPiLpSpace V}
    {ψ : ℝ → TokenPiLpSpace V} {a b t : ℝ}
    (hψ : HasDerivWithinAt ψ (G (ψ t)) (Set.Icc a b) t)
    (hinterior : t ∈ interior (Set.Icc a b)) :
    HasDerivAt ψ (G (ψ t)) t := by
  apply hψ.hasDerivAt
  rw [mem_nhds_iff]
  exact ⟨interior (Set.Icc a b), interior_subset, isOpen_interior, hinterior⟩

theorem tokenPiLp_local_norm_sq_deriv_nonpos
    {G : TokenPiLpSpace V →ₗ[ℝ] TokenPiLpSpace V}
    (hG : ∀ ψ, inner ℝ ψ (G ψ) ≤ 0)
    {ψ : ℝ → TokenPiLpSpace V} {a b t : ℝ}
    (hψ : HasDerivWithinAt ψ (G (ψ t)) (Set.Icc a b) t)
    (hinterior : t ∈ interior (Set.Icc a b)) :
    deriv (fun τ => ‖ψ τ‖ ^ 2) t ≤ 0 := by
  have hat : HasDerivAt ψ (G (ψ t)) t :=
    tokenPiLp_trajectory_hasDerivAt_interior hψ hinterior
  have hnorm := hat.norm_sq.deriv
  rw [hnorm]
  nlinarith [hG (ψ t)]

theorem exists_linearTokenPiLp_trajectory_near_zero
    (G : TokenPiLpSpace V →ₗ[ℝ] TokenPiLpSpace V)
    (ψ₀ : TokenPiLpSpace V) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ ψ : ℝ → TokenPiLpSpace V,
      ψ 0 = ψ₀ ∧
        ∀ t ∈ Set.Icc (-ε) ε,
          HasDerivWithinAt ψ (G (ψ t)) (Set.Icc (-ε) ε) t := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ :=
    IsPicardLindelof.of_contDiffAt_one
      (x₀ := ψ₀) G.toContinuousLinearMap.contDiff.contDiffAt 0
  obtain ⟨ψ, hψ, hderiv⟩ :=
    exists_tokenPiLp_trajectory_on_Icc
      G ⟨0, by simp [le_of_lt hε]⟩ ψ₀ hpl (by simp)
  exact ⟨ε, hε, ψ, hψ, by simpa using hderiv⟩

theorem exists_transportTokenGeneratorReal_trajectory_on_Icc
    (gen : TokenGenerator V)
    {tmin tmax : ℝ} (t₀ : Set.Icc tmin tmax) (ψ₀ : TokenPiLpSpace V)
    {a r L K : ℝ≥0}
    (hG : IsPicardLindelof
      (fun _ ψ => transportTokenGeneratorReal gen ψ) t₀ ψ₀ a r L K)
    (hψ : ψ₀ ∈ Metric.closedBall ψ₀ r) :
    ∃ ψ : ℝ → TokenPiLpSpace V, ψ t₀ = ψ₀ ∧
      ∀ t ∈ Set.Icc tmin tmax,
        HasDerivWithinAt ψ
          (transportTokenGeneratorReal gen (ψ t))
          (Set.Icc tmin tmax) t := by
  exact exists_tokenPiLp_trajectory_on_Icc
    (transportTokenGeneratorReal gen) t₀ ψ₀ hG hψ

/-- The zero state is a global trajectory for every linear generator.  This
    is the theorem-safe equilibrium statement available without invoking an
    ODE existence theorem for arbitrary initial data. -/
def zeroTokenPiLpTrajectory (G : TokenPiLpSpace V →ₗ[ℝ] TokenPiLpSpace V) :
    TokenPiLpTrajectory G where
  state := fun _ => 0
  equation := fun t => by
    simpa using (hasDerivAt_const t (0 : TokenPiLpSpace V))

@[simp] theorem zeroTokenPiLpTrajectory_state
    (G : TokenPiLpSpace V →ₗ[ℝ] TokenPiLpSpace V) (t : ℝ) :
    (zeroTokenPiLpTrajectory G).state t = 0 := rfl

theorem zeroTokenPiLpTrajectory_is_equilibrium
    (G : TokenPiLpSpace V →ₗ[ℝ] TokenPiLpSpace V) :
    G ((zeroTokenPiLpTrajectory G).state 0) = 0 := by
  simp

/-- Any vector in the kernel of a linear generator gives a constant global
    trajectory. -/
def constantTokenPiLpTrajectory
    (G : TokenPiLpSpace V →ₗ[ℝ] TokenPiLpSpace V)
    (ψ₀ : TokenPiLpSpace V) (hG : G ψ₀ = 0) :
    TokenPiLpTrajectory G where
  state := fun _ => ψ₀
  equation := fun t => by
    simpa [hG] using (hasDerivAt_const t ψ₀)

@[simp] theorem constantTokenPiLpTrajectory_state
    (G : TokenPiLpSpace V →ₗ[ℝ] TokenPiLpSpace V)
    (ψ₀ : TokenPiLpSpace V) (hG : G ψ₀ = 0) (t : ℝ) :
    (constantTokenPiLpTrajectory G ψ₀ hG).state t = ψ₀ := rfl

theorem constantTokenPiLpTrajectory_is_equilibrium
    (G : TokenPiLpSpace V →ₗ[ℝ] TokenPiLpSpace V)
    (ψ₀ : TokenPiLpSpace V) (hG : G ψ₀ = 0) :
    G ((constantTokenPiLpTrajectory G ψ₀ hG).state 0) = 0 := by
  simpa using hG

/-- The squared-norm derivative of a trajectory is obtained directly from
    Mathlib's inner-product calculus. -/
theorem tokenPiLpTrajectory_norm_sq_hasDerivAt
    (G : TokenPiLpSpace V →ₗ[ℝ] TokenPiLpSpace V)
    (trajectory : TokenPiLpTrajectory G) (t : ℝ) :
    HasDerivAt (fun τ => ‖trajectory.state τ‖ ^ 2)
      (2 * inner ℝ (trajectory.state t) (G (trajectory.state t))) t := by
  exact (trajectory.equation t).norm_sq

/-- Dissipativity of a `PiLp` generator implies a non-positive squared-norm
    derivative along every trajectory satisfying its equation. -/
theorem tokenPiLpTrajectory_norm_sq_deriv_nonpos
    (G : TokenPiLpSpace V →ₗ[ℝ] TokenPiLpSpace V)
    (hG : ∀ ψ, inner ℝ ψ (G ψ) ≤ 0)
    (trajectory : TokenPiLpTrajectory G) (t : ℝ) :
    deriv (fun τ => ‖trajectory.state τ‖ ^ 2) t ≤ 0 := by
  have hderiv := (tokenPiLpTrajectory_norm_sq_hasDerivAt G trajectory t).deriv
  rw [hderiv]
  nlinarith [hG (trajectory.state t)]

/-! ### A canonical real dissipative generator

The complex expression `-i H - Γ` is represented on the real Hilbert
carrier by a conservative operator `H` (whose real quadratic form vanishes)
and a dissipative operator `Γ`.  This keeps the conservative cancellation
and the positivity assumption explicit, instead of deriving either from a
name such as `selfAdjoint` alone.
-/
structure DissipativePiLpGenerator where
  H : TokenPiLpSpace V →ₗ[ℝ] TokenPiLpSpace V
  Gamma : TokenPiLpSpace V →ₗ[ℝ] TokenPiLpSpace V
  hamiltonian_pairing_zero : ∀ ψ, inner ℝ ψ (H ψ) = 0
  gamma_pairing_nonneg : ∀ ψ, 0 ≤ inner ℝ ψ (Gamma ψ)

/-- The total real representative of the non-unitary generator. -/
def DissipativePiLpGenerator.total
    (gen : DissipativePiLpGenerator (V := V)) :
    TokenPiLpSpace V →ₗ[ℝ] TokenPiLpSpace V :=
  -gen.H - gen.Gamma

@[simp] theorem DissipativePiLpGenerator.total_apply
    (gen : DissipativePiLpGenerator (V := V)) (ψ : TokenPiLpSpace V) :
    gen.total ψ = -gen.H ψ - gen.Gamma ψ := rfl

theorem exists_DissipativePiLpGenerator_trajectory_near_zero
    (gen : DissipativePiLpGenerator (V := V))
    (ψ₀ : TokenPiLpSpace V) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ ψ : ℝ → TokenPiLpSpace V,
      ψ 0 = ψ₀ ∧
        ∀ t ∈ Set.Icc (-ε) ε,
          HasDerivWithinAt ψ (gen.total (ψ t)) (Set.Icc (-ε) ε) t := by
  exact exists_linearTokenPiLp_trajectory_near_zero gen.total ψ₀

theorem DissipativePiLpGenerator.pairing_total
    (gen : DissipativePiLpGenerator (V := V)) (ψ : TokenPiLpSpace V) :
    inner ℝ ψ (gen.total ψ) = -inner ℝ ψ (gen.Gamma ψ) := by
  rw [DissipativePiLpGenerator.total_apply]
  rw [inner_sub_right, inner_neg_right]
  simp only [gen.hamiltonian_pairing_zero]
  ring

theorem DissipativePiLpGenerator.local_norm_sq_deriv_eq
    (gen : DissipativePiLpGenerator (V := V))
    {ψ : ℝ → TokenPiLpSpace V} {a b t : ℝ}
    (hψ : HasDerivWithinAt ψ (gen.total (ψ t)) (Set.Icc a b) t)
    (hinterior : t ∈ interior (Set.Icc a b)) :
    deriv (fun τ => ‖ψ τ‖ ^ 2) t =
      -2 * inner ℝ (ψ t) (gen.Gamma (ψ t)) := by
  have hat : HasDerivAt ψ (gen.total (ψ t)) t :=
    tokenPiLp_trajectory_hasDerivAt_interior hψ hinterior
  have hderiv := hat.norm_sq.deriv
  rw [hderiv, gen.pairing_total]
  ring

theorem DissipativePiLpGenerator.local_norm_sq_deriv_nonpos
    (gen : DissipativePiLpGenerator (V := V))
    {ψ : ℝ → TokenPiLpSpace V} {a b t : ℝ}
    (hψ : HasDerivWithinAt ψ (gen.total (ψ t)) (Set.Icc a b) t)
    (hinterior : t ∈ interior (Set.Icc a b)) :
    deriv (fun τ => ‖ψ τ‖ ^ 2) t ≤ 0 := by
  rw [gen.local_norm_sq_deriv_eq hψ hinterior]
  have hnon : 0 ≤ 2 * inner ℝ (ψ t) (gen.Gamma (ψ t)) :=
    mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
      (gen.gamma_pairing_nonneg (ψ t))
  nlinarith

theorem DissipativePiLpGenerator.local_norm_sq_deriv_eq_zero_of_gamma_pairing_zero
    (gen : DissipativePiLpGenerator (V := V))
    {ψ : ℝ → TokenPiLpSpace V} {a b t : ℝ}
    (hψ : HasDerivWithinAt ψ (gen.total (ψ t)) (Set.Icc a b) t)
    (hinterior : t ∈ interior (Set.Icc a b))
    (hzero : inner ℝ (ψ t) (gen.Gamma (ψ t)) = 0) :
    deriv (fun τ => ‖ψ τ‖ ^ 2) t = 0 := by
  rw [gen.local_norm_sq_deriv_eq hψ hinterior, hzero]
  ring

theorem DissipativePiLpGenerator.pairing_total_nonpos
    (gen : DissipativePiLpGenerator (V := V)) (ψ : TokenPiLpSpace V) :
    inner ℝ ψ (gen.total ψ) ≤ 0 := by
  rw [gen.pairing_total]
  exact neg_nonpos.mpr (gen.gamma_pairing_nonneg ψ)

theorem DissipativePiLpGenerator.norm_sq_deriv_nonpos
    (gen : DissipativePiLpGenerator (V := V))
    (trajectory : TokenPiLpTrajectory gen.total) (t : ℝ) :
    deriv (fun τ => ‖trajectory.state τ‖ ^ 2) t ≤ 0 := by
  exact tokenPiLpTrajectory_norm_sq_deriv_nonpos gen.total
    (fun ψ => gen.pairing_total_nonpos ψ) trajectory t

theorem DissipativePiLpGenerator.norm_sq_deriv_eq
    (gen : DissipativePiLpGenerator (V := V))
    (trajectory : TokenPiLpTrajectory gen.total) (t : ℝ) :
    deriv (fun τ => ‖trajectory.state τ‖ ^ 2) t =
      -2 * inner ℝ (trajectory.state t)
        (gen.Gamma (trajectory.state t)) := by
  have hderiv := (tokenPiLpTrajectory_norm_sq_hasDerivAt
    gen.total trajectory t).deriv
  rw [hderiv, gen.pairing_total]
  ring

theorem DissipativePiLpGenerator.norm_sq_deriv_eq_zero_of_gamma_pairing_zero
    (gen : DissipativePiLpGenerator (V := V))
    (trajectory : TokenPiLpTrajectory gen.total) (t : ℝ)
    (hzero : inner ℝ (trajectory.state t)
      (gen.Gamma (trajectory.state t)) = 0) :
    deriv (fun τ => ‖trajectory.state τ‖ ^ 2) t = 0 := by
  rw [gen.norm_sq_deriv_eq, hzero]
  ring

theorem DissipativePiLpGenerator.norm_sq_deriv_eq_zero_iff_gamma_pairing_zero
    (gen : DissipativePiLpGenerator (V := V))
    (trajectory : TokenPiLpTrajectory gen.total) (t : ℝ) :
    deriv (fun τ => ‖trajectory.state τ‖ ^ 2) t = 0 ↔
      inner ℝ (trajectory.state t)
        (gen.Gamma (trajectory.state t)) = 0 := by
  rw [gen.norm_sq_deriv_eq]
  constructor
  · intro h
    linarith
  · intro h
    rw [h]
    ring

end
end InfoGeometry.Dynamics
