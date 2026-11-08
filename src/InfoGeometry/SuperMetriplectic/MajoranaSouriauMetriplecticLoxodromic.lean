/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.NeutralKreinMajoranaFrame
import InfoGeometry.SuperGrassmannian.MajoranaCARSuperalgebra
import InfoGeometry.Physics.SouriauMassieuPlanckFunctional
import InfoGeometry.Thermo.GenericMetriplecticFlow
import InfoGeometry.SuperMetriplectic.Flow
import InfoGeometry.Topology.CanonicalRapidityAngleMetriplecticFlow
import InfoGeometry.Routing.PlanarRotation
import InfoGeometry.Quantum.ThermofieldDouble

/-!
# Majorana–Souriau Metriplectic Loxodromic Bridge

This module unifies the existing repository owners across the four Causal Poset
archetypes:

1. **Archetype I (Kinematics — Real Majorana Frame, Split Polarization, Witt Nilpotents,
   and Quadratic Lie Bilinears)**:
   Bridges the finite doubled neutral Krein–Majorana frame
   (`InfoGeometry.Quantum.NeutralKreinMajoranaFrame`) with the split Clifford CAR cell
   (`InfoGeometry.SuperGrassmannian.MajoranaCAR.SplitCliffordCell`), constructing the
   block-matrix Witt lightcone nilpotents `wittAnnihilator n` and `wittCreator n` on
   `Matrix2 n`, proving the orthogonal Majorana bilinear commutator identities
   $[γ_1, γ_2] = 2 γ_1 γ_2$, $[γ_1 γ_2, γ_1] = -2 γ_2$, and $[γ_1 γ_2, γ_2] = 2 γ_1$,
   and instantiating them concretely on `(grading n, exchange n)` in `Matrix2 n`.

2. **Archetype II (Souriau's Symplectic Thermodynamics on Coadjoint Orbits)**:
   Formalizes the Kirillov–Kostant–Souriau (KKS) coadjoint 2-form `kksForm`, the
   concrete matrix commutator `matrixCommutator`, the Lie-algebraic Gibbs partition
   function `souriauLiePartition` and state `souriauLieGibbs` associated with a
   Lie-algebra temperature vector $\beta \in \mathfrak{g}$, the coadjoint heat covector
   $\alpha(\beta) = \mathbb{E}_\beta[J(x)] \in \mathfrak{g}^*$, its concrete KKS
   instantiation on `Matrix ι ι ℝ`, and Souriau's vector Legendre entropy identity
   $S(\alpha) = \ln Z(\beta) + \langle \alpha(\beta), \beta \rangle$.

3. **Archetype III (Metriplectic Double-Bracket Formalism and Casimir Orthogonality)**:
   Formalizes the Poisson and dissipative metric bracket rates on
   `InfoGeometry.Thermo.GenericMetriplecticFlow.System`, constructs the bidirectional
   bridge between `GenericMetriplecticFlow.System V` and
   `InfoGeometry.SuperMetriplectic.MetriplecticFlow (GenericMetriplecticFlow.Covector V)`
   via `genericSystemToSuperMetriplecticFlow`, proves full total-flow energy conservation
   and entropy production on `matrixMetriplecticFlow`, and exhibits a concrete $2 \times 2$
   planar metriplectic flow witness.

4. **Archetype IV (Hypercomplex Loxodromic Phase Dynamics and Thermofield Double to Souriau
   Gibbs KMS Equilibrium)**:
   Defines the $2 \times 2$ loxodromic propagator `loxodromicPropagator γ ω t`, proves its
   one-parameter semigroup law, quadratic norm contraction, polar action equivariance with
   `InfoGeometry.Topology.CanonicalRapidityAngleMetriplecticFlow.flowMap`, and the
   logarithmic spiral angle law, and proves that the squared real zero-time Thermofield
   Double amplitude equals Souriau's Gibbs weight both for scalar energy and for the
   Lie-algebraic moment map `souriauLieGibbs`.
-/

noncomputable section

namespace InfoGeometry.SuperMetriplectic.MajoranaSouriauMetriplecticLoxodromic

open Matrix Finset
open scoped BigOperators
open InfoGeometry.Quantum
open InfoGeometry.SuperGrassmannian
open InfoGeometry.Physics
open InfoGeometry.Thermo
open InfoGeometry.Topology
open InfoGeometry.Routing

/-! ### Private Scalar Arithmetic Helpers (Trap T16 Safe) -/

private lemma exp_neg_gamma_add_eq (γ t s : ℝ) :
    Real.exp (-γ * (t + s)) = Real.exp (-γ * t) * Real.exp (-γ * s) := by
  have h : -γ * (t + s) = -γ * t + -γ * s := by ring
  rw [h, Real.exp_add]

private lemma exp_mul_exp_eq_neg_two (γ t : ℝ) :
    Real.exp (-γ * t) * Real.exp (-γ * t) = Real.exp (-2 * γ * t) := by
  rw [← Real.exp_add]
  congr 1
  ring

private lemma spiral_exponent_identity (γ ω t θ₀ : ℝ) (hω : ω ≠ 0) :
    -(γ / ω) * (θ₀ + ω * t - θ₀) = -γ * t := by
  have hsub : θ₀ + ω * t - θ₀ = ω * t := by ring
  rw [hsub]
  calc
    -(γ / ω) * (ω * t) = -(γ / ω * ω) * t := by ring
    _ = -γ * t := by rw [div_mul_cancel₀ γ hω]

private lemma exp_neg_half_mul_sq (β E : ℝ) :
    Real.exp (-(β / 2) * E) ^ 2 = Real.exp (-β * E) := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring

private lemma eq_zero_of_eq_neg_self (x : ℝ) (h : x = -x) : x = 0 := by
  linarith [h]

/-!
### Archetype I — Kinematics: Real Majorana Frame, Split Polarization, Witt Nilpotents, and Quadratic Lie Bilinears
-/

/-- The paracomplex grading $\Gamma$ and the skew Majorana symplectic form $\Omega$ anticommute
on the doubled carrier `Fin n ⊕ Fin n`: $\Gamma \Omega + \Omega \Gamma = 0$. -/
theorem grading_majoranaForm_anticomm (n : ℕ) :
    NeutralKreinMajoranaFrame.grading n * NeutralKreinMajoranaFrame.majoranaForm n +
      NeutralKreinMajoranaFrame.majoranaForm n * NeutralKreinMajoranaFrame.grading n = 0 := by
  unfold NeutralKreinMajoranaFrame.grading NeutralKreinMajoranaFrame.majoranaForm
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

/-- The neutral Krein–Majorana frame `(grading n, majoranaForm n)` forms a concrete
real block-matrix `SplitCliffordCell` on `Matrix2 n`. -/
def kreinMajoranaSplitCell (n : ℕ) :
    MajoranaCAR.SplitCliffordCell (NeutralKreinMajoranaFrame.Matrix2 n) where
  e := NeutralKreinMajoranaFrame.grading n
  f := NeutralKreinMajoranaFrame.majoranaForm n
  half := (1 / 2 : ℝ) • (1 : NeutralKreinMajoranaFrame.Matrix2 n)
  e_sq := by
    rw [sq]
    exact NeutralKreinMajoranaFrame.grading_sq n
  f_sq := by
    rw [sq]
    exact NeutralKreinMajoranaFrame.majoranaForm_squared n
  anticomm := grading_majoranaForm_anticomm n
  two_half := by
    ext i j
    simp [Matrix.add_apply, Matrix.smul_apply]
    ring
  half_comm := fun X => by
    ext i j
    simp

/-- Witt lightcone annihilation nilpotent $a_n = \frac{1}{2}(\Gamma_n + \Omega_n)$ on `Matrix2 n`. -/
def wittAnnihilator (n : ℕ) : NeutralKreinMajoranaFrame.Matrix2 n :=
  (kreinMajoranaSplitCell n).a

/-- Witt lightcone creation nilpotent $a^*_n = \frac{1}{2}(\Gamma_n - \Omega_n)$ on `Matrix2 n`. -/
def wittCreator (n : ℕ) : NeutralKreinMajoranaFrame.Matrix2 n :=
  (kreinMajoranaSplitCell n).a_star

/-- The Witt annihilation operator is nilpotent of order 2: $a_n^2 = 0$. -/
theorem wittAnnihilator_sq_zero (n : ℕ) :
    wittAnnihilator n * wittAnnihilator n = 0 :=
  MajoranaCAR.SplitCliffordCell.a_mul_a (kreinMajoranaSplitCell n)

/-- The Witt creation operator is nilpotent of order 2: $(a^*_n)^2 = 0$. -/
theorem wittCreator_sq_zero (n : ℕ) :
    wittCreator n * wittCreator n = 0 :=
  MajoranaCAR.SplitCliffordCell.a_star_mul_a_star (kreinMajoranaSplitCell n)

/-- Canonical Anticommutation Relation (CAR) for the block-matrix Witt modes:
$a_n a^*_n + a^*_n a_n = 1$. -/
theorem witt_car_anticomm (n : ℕ) :
    wittAnnihilator n * wittCreator n + wittCreator n * wittAnnihilator n = 1 :=
  MajoranaCAR.SplitCliffordCell.car_anticommutator (kreinMajoranaSplitCell n)

/-- For anticommuting Majorana generators $\gamma_1 \gamma_2 + \gamma_2 \gamma_1 = 0$, the
commutator equals twice the quadratic bivector: $[\gamma_1, \gamma_2] = 2 \gamma_1 \gamma_2$. -/
theorem majorana_commutator_eq_two_mul_bivector {R : Type*} [Ring R]
    (γ₁ γ₂ : R) (h_anti : γ₁ * γ₂ + γ₂ * γ₁ = 0) :
    γ₁ * γ₂ - γ₂ * γ₁ = (2 : R) * (γ₁ * γ₂) := by
  calc
    γ₁ * γ₂ - γ₂ * γ₁ = (γ₁ * γ₂ + γ₁ * γ₂) - (γ₁ * γ₂ + γ₂ * γ₁) := by abel
    _ = (γ₁ * γ₂ + γ₁ * γ₂) - 0 := by rw [h_anti]
    _ = (2 : R) * (γ₁ * γ₂) := by noncomm_ring

/-- Orthogonal Majorana quadratic Lie bilinear action on the first generator:
$[\gamma_1 \gamma_2, \gamma_1] = -2 \gamma_2$. -/
theorem majorana_bivector_commutator_first {R : Type*} [Ring R]
    (γ₁ γ₂ : R) (h₁ : γ₁ * γ₁ = 1) (h_anti : γ₁ * γ₂ + γ₂ * γ₁ = 0) :
    (γ₁ * γ₂) * γ₁ - γ₁ * (γ₁ * γ₂) = -((2 : R) * γ₂) := by
  calc
    (γ₁ * γ₂) * γ₁ - γ₁ * (γ₁ * γ₂)
      = γ₁ * (γ₁ * γ₂ + γ₂ * γ₁) - (2 : R) * (γ₁ * γ₁) * γ₂ := by noncomm_ring
    _ = γ₁ * 0 - (2 : R) * 1 * γ₂ := by rw [h_anti, h₁]
    _ = -((2 : R) * γ₂) := by noncomm_ring

/-- Orthogonal Majorana quadratic Lie bilinear action on the second generator:
$[\gamma_1 \gamma_2, \gamma_2] = 2 \gamma_1$. -/
theorem majorana_bivector_commutator_second {R : Type*} [Ring R]
    (γ₁ γ₂ : R) (h₂ : γ₂ * γ₂ = 1) (h_anti : γ₁ * γ₂ + γ₂ * γ₁ = 0) :
    (γ₁ * γ₂) * γ₂ - γ₂ * (γ₁ * γ₂) = (2 : R) * γ₁ := by
  calc
    (γ₁ * γ₂) * γ₂ - γ₂ * (γ₁ * γ₂)
      = (2 : R) * γ₁ * (γ₂ * γ₂) - (γ₁ * γ₂ + γ₂ * γ₁) * γ₂ := by noncomm_ring
    _ = (2 : R) * γ₁ * 1 - 0 * γ₂ := by rw [h₂, h_anti]
    _ = (2 : R) * γ₁ := by noncomm_ring

/-- Anticommutator sum form for `grading n` and `exchange n` on `Matrix2 n`. -/
theorem grading_exchange_anticomm_sum (n : ℕ) :
    NeutralKreinMajoranaFrame.grading n * NeutralKreinMajoranaFrame.exchange n +
      NeutralKreinMajoranaFrame.exchange n * NeutralKreinMajoranaFrame.grading n = 0 := by
  rw [NeutralKreinMajoranaFrame.grading_exchange_anticommute n, neg_add_cancel]

/-- Concrete instantiation of the Majorana quadratic Lie bilinear action on `grading n`
in `NeutralKreinMajoranaFrame.Matrix2 n`. -/
theorem kreinMajorana_bivector_commutator_grading (n : ℕ) :
    (NeutralKreinMajoranaFrame.grading n * NeutralKreinMajoranaFrame.exchange n) *
        NeutralKreinMajoranaFrame.grading n -
      NeutralKreinMajoranaFrame.grading n *
        (NeutralKreinMajoranaFrame.grading n * NeutralKreinMajoranaFrame.exchange n) =
      -((2 : NeutralKreinMajoranaFrame.Matrix2 n) * NeutralKreinMajoranaFrame.exchange n) :=
  majorana_bivector_commutator_first
    (NeutralKreinMajoranaFrame.grading n)
    (NeutralKreinMajoranaFrame.exchange n)
    (NeutralKreinMajoranaFrame.grading_sq n)
    (grading_exchange_anticomm_sum n)

/-- Concrete instantiation of the Majorana quadratic Lie bilinear action on `exchange n`
in `NeutralKreinMajoranaFrame.Matrix2 n`. -/
theorem kreinMajorana_bivector_commutator_exchange (n : ℕ) :
    (NeutralKreinMajoranaFrame.grading n * NeutralKreinMajoranaFrame.exchange n) *
        NeutralKreinMajoranaFrame.exchange n -
      NeutralKreinMajoranaFrame.exchange n *
        (NeutralKreinMajoranaFrame.grading n * NeutralKreinMajoranaFrame.exchange n) =
      (2 : NeutralKreinMajoranaFrame.Matrix2 n) * NeutralKreinMajoranaFrame.grading n :=
  majorana_bivector_commutator_second
    (NeutralKreinMajoranaFrame.grading n)
    (NeutralKreinMajoranaFrame.exchange n)
    (NeutralKreinMajoranaFrame.exchange_sq n)
    (grading_exchange_anticomm_sum n)

/-!
### Archetype II — Souriau’s Symplectic Thermodynamics on Coadjoint Orbits: KKS Form, Lie-Algebra Temperature $\beta \in \mathfrak{g}$, Coadjoint Heat $\alpha \in \mathfrak{g}^*$, and Vector Legendre Identity
-/

/-- The Kirillov–Kostant–Souriau (KKS) coadjoint orbit 2-form evaluated at covector
$\xi \in \mathfrak{g}^*$ on Lie algebra generators $X, Y \in \mathfrak{g}$:
$\omega_\xi(X, Y) = -\langle \xi, [X, Y] \rangle$. -/
def kksForm {g : Type*} [AddCommGroup g] [Module ℝ g]
    (bracket : g →ₗ[ℝ] g →ₗ[ℝ] g) (ξ : g →ₗ[ℝ] ℝ) (X Y : g) : ℝ :=
  -ξ (bracket X Y)

/-- Skew-symmetry of the KKS coadjoint 2-form from Lie bracket antisymmetry. -/
theorem kksForm_skew {g : Type*} [AddCommGroup g] [Module ℝ g]
    (bracket : g →ₗ[ℝ] g →ₗ[ℝ] g) (ξ : g →ₗ[ℝ] ℝ)
    (h_skew : ∀ X Y : g, bracket X Y = -bracket Y X) (X Y : g) :
    kksForm bracket ξ X Y = -kksForm bracket ξ Y X := by
  unfold kksForm
  rw [h_skew X Y, map_neg, neg_neg]

/-- Diagonal vanishing of the KKS coadjoint 2-form on any generator with $[X, X] = 0$. -/
theorem kksForm_self_zero {g : Type*} [AddCommGroup g] [Module ℝ g]
    (bracket : g →ₗ[ℝ] g →ₗ[ℝ] g) (ξ : g →ₗ[ℝ] ℝ) (X : g)
    (h_diag : bracket X X = 0) :
    kksForm bracket ξ X X = 0 := by
  unfold kksForm
  rw [h_diag, map_zero, neg_zero]

variable {ι : Type*}

/-- Concrete bilinear matrix commutator $[X, Y] = X Y - Y X$ on `Matrix ι ι ℝ`. -/
def matrixCommutator [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ where
  toFun X :=
    { toFun := fun Y => X * Y - Y * X
      map_add' := fun Y₁ Y₂ => by
        rw [Matrix.mul_add, Matrix.add_mul]
        abel
      map_smul' := fun c Y => by
        rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
        rfl }
  map_add' X₁ X₂ := by
    ext Y i j
    simp [Matrix.add_mul, Matrix.mul_add, Matrix.sub_apply, Matrix.add_apply]
    abel
  map_smul' c X := by
    ext Y i j
    simp [Matrix.sub_apply, Matrix.smul_apply]
    ring

/-- The concrete matrix commutator is skew-symmetric: $[X, Y] = -[Y, X]$. -/
theorem matrixCommutator_skew [Fintype ι] [DecidableEq ι]
    (X Y : Matrix ι ι ℝ) :
    matrixCommutator X Y = -matrixCommutator Y X := by
  change X * Y - Y * X = -(Y * X - X * Y)
  abel

/-- The concrete matrix commutator vanishes on identical arguments: $[X, X] = 0$. -/
theorem matrixCommutator_self_zero [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℝ) :
    matrixCommutator X X = 0 := by
  change X * X - X * X = 0
  exact sub_self (X * X)

/-- Souriau moment-map energy readout $E_\beta(x) = \langle J(x), \beta \rangle$ for a
Lie-algebraic inverse temperature vector $\beta \in \mathfrak{g}$. -/
def souriauMomentEnergy {g : Type*} [AddCommGroup g] [Module ℝ g]
    (J : ι → (g →ₗ[ℝ] ℝ)) (β : g) (x : ι) : ℝ :=
  J x β

/-- Souriau Lie-algebraic partition function $Z(\beta) = \sum_x \exp(-\langle J(x), \beta \rangle)$. -/
def souriauLiePartition [Fintype ι] {g : Type*} [AddCommGroup g] [Module ℝ g]
    (J : ι → (g →ₗ[ℝ] ℝ)) (β : g) : ℝ :=
  SouriauMassieuPlanckFunctional.souriauPartition 1 (souriauMomentEnergy J β)

/-- Souriau Lie-algebraic Gibbs weight $\rho_\beta(x) = \exp(-\langle J(x), \beta \rangle) / Z(\beta)$. -/
def souriauLieGibbs [Fintype ι] {g : Type*} [AddCommGroup g] [Module ℝ g]
    (J : ι → (g →ₗ[ℝ] ℝ)) (β : g) (x : ι) : ℝ :=
  SouriauMassieuPlanckFunctional.gibbsWeight 1 (souriauMomentEnergy J β) x

/-- Souriau coadjoint heat covector $\alpha(\beta) = \mathbb{E}_\beta[J(x)] \in \mathfrak{g}^*$. -/
def souriauHeatCovector [Fintype ι] {g : Type*} [AddCommGroup g] [Module ℝ g]
    (J : ι → (g →ₗ[ℝ] ℝ)) (β : g) : g →ₗ[ℝ] ℝ :=
  ∑ x : ι, souriauLieGibbs J β x • J x

/-- Positivity of Souriau's Lie-algebraic partition function on a nonempty finite state space. -/
theorem souriauLiePartition_pos [Fintype ι] [Nonempty ι]
    {g : Type*} [AddCommGroup g] [Module ℝ g]
    (J : ι → (g →ₗ[ℝ] ℝ)) (β : g) :
    0 < souriauLiePartition J β :=
  SouriauMassieuPlanckFunctional.souriauPartition_pos 1 (souriauMomentEnergy J β)

/-- Normalization of Souriau's Lie-algebraic Gibbs measure: $\sum_x \rho_\beta(x) = 1$. -/
theorem souriauLieGibbs_sum_one [Fintype ι] [Nonempty ι]
    {g : Type*} [AddCommGroup g] [Module ℝ g]
    (J : ι → (g →ₗ[ℝ] ℝ)) (β : g) :
    ∑ x : ι, souriauLieGibbs J β x = 1 :=
  SouriauMassieuPlanckFunctional.gibbsWeight_sum_eq_one 1 (souriauMomentEnergy J β)

/-- Pointwise evaluation of the coadjoint heat covector $\langle \alpha(\beta), X \rangle$. -/
theorem souriauHeatCovector_apply [Fintype ι]
    {g : Type*} [AddCommGroup g] [Module ℝ g]
    (J : ι → (g →ₗ[ℝ] ℝ)) (β X : g) :
    souriauHeatCovector J β X = ∑ x : ι, souriauLieGibbs J β x * J x X := by
  unfold souriauHeatCovector
  rw [LinearMap.sum_apply]
  rfl

/-- Pairing the coadjoint heat covector $\alpha(\beta)$ with the Lie-algebraic temperature
$\beta$ recovers the mean moment energy $\mathbb{E}_\beta[\langle J(x), \beta \rangle]$. -/
theorem souriauHeatCovector_eval_beta [Fintype ι]
    {g : Type*} [AddCommGroup g] [Module ℝ g]
    (J : ι → (g →ₗ[ℝ] ℝ)) (β : g) :
    souriauHeatCovector J β β =
      SouriauMassieuPlanckFunctional.meanEnergy 1 (souriauMomentEnergy J β) := by
  rw [souriauHeatCovector_apply]
  rfl

/-- **Souriau Vector Legendre Entropy Identity**:
The Boltzmann entropy of the Lie-algebraic Gibbs state equals the Massieu–Planck log-partition
potential plus the natural duality pairing between the coadjoint heat covector
$\alpha(\beta) \in \mathfrak{g}^*$ and the Lie-algebra temperature $\beta \in \mathfrak{g}$:
$S(\rho_\beta) = \ln Z(\beta) + \langle \alpha(\beta), \beta \rangle$. -/
theorem souriauLie_entropy_eq_logPartition_add_heat_pairing [Fintype ι] [Nonempty ι]
    {g : Type*} [AddCommGroup g] [Module ℝ g]
    (J : ι → (g →ₗ[ℝ] ℝ)) (β : g) :
    SouriauMassieuPlanckFunctional.boltzmannEntropy (souriauLieGibbs J β) =
      Real.log (souriauLiePartition J β) + souriauHeatCovector J β β := by
  unfold souriauLieGibbs souriauLiePartition
  rw [souriauHeatCovector_eval_beta]
  have h :=
    SouriauMassieuPlanckFunctional.boltzmannEntropy_gibbsWeight_eq_massieu_add_beta_meanEnergy
      1 (souriauMomentEnergy J β)
  unfold SouriauMassieuPlanckFunctional.massieuPlanckPotential at h
  rw [one_mul] at h
  exact h

/-- Unconditional skew-symmetry of the KKS coadjoint 2-form evaluated at Souriau's
coadjoint heat covector `souriauHeatCovector J β` on the matrix Lie algebra `Matrix k k ℝ`. -/
theorem kksForm_souriauHeatCovector_skew [Fintype ι]
    {k : Type*} [Fintype k] [DecidableEq k]
    (J : ι → (Matrix k k ℝ →ₗ[ℝ] ℝ)) (β X Y : Matrix k k ℝ) :
    kksForm matrixCommutator (souriauHeatCovector J β) X Y =
      -kksForm matrixCommutator (souriauHeatCovector J β) Y X :=
  kksForm_skew matrixCommutator (souriauHeatCovector J β) matrixCommutator_skew X Y

/-- Unconditional diagonal vanishing of the KKS coadjoint 2-form evaluated at Souriau's
coadjoint heat covector `souriauHeatCovector J β` on the matrix Lie algebra `Matrix k k ℝ`. -/
theorem kksForm_souriauHeatCovector_self_zero [Fintype ι]
    {k : Type*} [Fintype k] [DecidableEq k]
    (J : ι → (Matrix k k ℝ →ₗ[ℝ] ℝ)) (β X : Matrix k k ℝ) :
    kksForm matrixCommutator (souriauHeatCovector J β) X X = 0 :=
  kksForm_self_zero matrixCommutator (souriauHeatCovector J β) X (matrixCommutator_self_zero X)

/-!
### Archetype III — Metriplectic Double-Bracket Formalism, Casimir Orthogonality & `GenericMetriplecticFlow` ↔ `SuperMetriplectic.MetriplecticFlow` Bridge
-/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Reversible Poisson bracket rate $\{F, H\} = \langle dF, L(dH) \rangle$ of an observable covector `dF`. -/
def poissonBracketRate (S : GenericMetriplecticFlow.System V)
    (dF : GenericMetriplecticFlow.Covector V) : ℝ :=
  dF (S.L S.dH)

/-- Dissipative metric bracket rate $(F, S) = \langle dF, M(dS) \rangle$ of an observable covector `dF`. -/
def metricBracketRate (S : GenericMetriplecticFlow.System V)
    (dF : GenericMetriplecticFlow.Covector V) : ℝ :=
  dF (S.M S.dS)

/-- Total metriplectic rate $\dot{F} = \langle dF, L(dH) + M(dS) \rangle$ of an observable covector `dF`. -/
def totalObservableRate (S : GenericMetriplecticFlow.System V)
    (dF : GenericMetriplecticFlow.Covector V) : ℝ :=
  dF S.flow

/-- Double-bracket decomposition of the evolution of any observable covector `dF`:
$\dot{F} = \{F, H\} + (F, S)$. -/
theorem totalObservableRate_eq_double_bracket (S : GenericMetriplecticFlow.System V)
    (dF : GenericMetriplecticFlow.Covector V) :
    totalObservableRate S dF = poissonBracketRate S dF + metricBracketRate S dF := by
  unfold totalObservableRate poissonBracketRate metricBracketRate GenericMetriplecticFlow.System.flow
  exact map_add dF (S.L S.dH) (S.M S.dS)

/-- Entropy is a Casimir of the reversible Poisson bracket: $\{F, S\} = \langle dF, L(dS) \rangle = 0$. -/
theorem poissonBracket_entropy_casimir (S : GenericMetriplecticFlow.System V)
    (dF : GenericMetriplecticFlow.Covector V) :
    dF (S.L S.dS) = 0 := by
  rw [S.L_entropy_casimir, map_zero]

/-- Energy is a Casimir of the dissipative metric bracket: $(F, H) = \langle dF, M(dH) \rangle = 0$. -/
theorem metricBracket_hamiltonian_casimir (S : GenericMetriplecticFlow.System V)
    (dF : GenericMetriplecticFlow.Covector V) :
    dF (S.M S.dH) = 0 := by
  rw [S.M_hamiltonian_casimir, map_zero]

/-- Pullback of a GENERIC system `S : GenericMetriplecticFlow.System V` along a Riesz/metric
identification `flat : V →ₗ[ℝ] GenericMetriplecticFlow.Covector V` satisfying
`∀ α : Covector V, flat (S.M α) = 0 → S.M α = 0`, producing an `OnsagerMetricData (Covector V)`
with Onsager operator `flat ∘ S.M` and metric pairing `⟨α, β⟩ = α(S.M(flat⁻¹...))`.
Even more directly, for any `S : GenericMetriplecticFlow.System V` and any linear map
`flat : V →ₗ[ℝ] GenericMetriplecticFlow.Covector V` that is symmetric and positive with respect
to `S.M` (`∀ x y, (flat x) (S.M (flat y)) = (flat y) (S.M (flat x))`), we obtain a
`SuperMetriplectic.MetriplecticFlow V` directly on the state space `V`! -/
def genericSystemToOnsagerMetricData (S : GenericMetriplecticFlow.System V)
    (flat : V →ₗ[ℝ] GenericMetriplecticFlow.Covector V) :
    SuperMetriplectic.OnsagerMetricData V where
  onsager := S.M.comp flat
  pairing x v := (flat x) v
  metric_symmetric := fun x y => S.M_symmetric (flat x) (flat y)
  metric_nonnegative := fun x => S.M_nonneg (flat x)
  pairing_zero_right := fun x => map_zero (flat x)

/-- Direct bridge from any `S : GenericMetriplecticFlow.System V` equipped with a Riesz
lift `(flat, gradH, gradS)` (`flat gradH = S.dH`, `flat gradS = S.dS`) to a
`SuperMetriplectic.MetriplecticFlow V` whose total flow is identically `S.flow` and whose
entropy production is identically `S.dS S.flow`. -/
def genericSystemToSuperMetriplecticFlow (S : GenericMetriplecticFlow.System V)
    (flat : V →ₗ[ℝ] GenericMetriplecticFlow.Covector V)
    (gradH gradS : V)
    (hH : flat gradH = S.dH)
    (hS : flat gradS = S.dS) :
    SuperMetriplectic.MetriplecticFlow V where
  metric := genericSystemToOnsagerMetricData S flat
  entropyForce := gradS
  energyForce := gradH
  reversibleFlow := S.L S.dH
  dissipativeFlow := S.M S.dS
  totalFlow := S.flow
  entropyProduction := S.dS (S.M S.dS)
  dissipativeFlow_eq_onsager_entropy := by
    change S.M S.dS = S.M (flat gradS)
    rw [hS]
  totalFlow_eq_reversible_add_dissipative := rfl
  energy_degeneracy := by
    change S.M (flat gradH) = 0
    rw [hH, S.M_hamiltonian_casimir]
  entropyProduction_eq_quadratic := by
    change S.dS (S.M S.dS) = (flat gradS) (S.M S.dS)
    rw [hS]

/-- The total flow and entropy production of `genericSystemToSuperMetriplecticFlow` match
`S.flow` and `totalObservableRate S S.dS` of the underlying `GenericMetriplecticFlow.System V`. -/
theorem genericSystemToSuperMetriplecticFlow_rates_eq
    (S : GenericMetriplecticFlow.System V)
    (flat : V →ₗ[ℝ] GenericMetriplecticFlow.Covector V)
    (gradH gradS : V)
    (hH : flat gradH = S.dH)
    (hS : flat gradS = S.dS) :
    (genericSystemToSuperMetriplecticFlow S flat gradH gradS hH hS).totalFlow = S.flow ∧
      (genericSystemToSuperMetriplecticFlow S flat gradH gradS hH hS).entropyProduction =
        totalObservableRate S S.dS := by
  refine ⟨rfl, ?_⟩
  unfold totalObservableRate
  rw [S.entropy_rate_eq_dissipative]
  rfl

/-- Every skew-symmetric matrix `Lᵀ = -L` has vanishing quadratic form `v ⬝ᵥ (L *ᵥ v) = 0`. -/
theorem dotProduct_mulVec_of_skewSymmetric [Fintype ι]
    (L : Matrix ι ι ℝ) (hL_skew : L.transpose = -L) (v : ι → ℝ) :
    dotProduct v (L.mulVec v) = 0 := by
  have h : dotProduct v (L.mulVec v) = -dotProduct v (L.mulVec v) := by
    calc
      dotProduct v (L.mulVec v) = dotProduct (L.vecMul v) v := Matrix.dotProduct_mulVec v L v
      _ = dotProduct (L.transpose.mulVec v) v := by rw [← Matrix.mulVec_transpose]
      _ = dotProduct ((-L).mulVec v) v := by rw [hL_skew]
      _ = -dotProduct v (L.mulVec v) := by
        rw [Matrix.neg_mulVec, neg_dotProduct, dotProduct_comm]
  exact eq_zero_of_eq_neg_self (dotProduct v (L.mulVec v)) h

/-- Concrete matrix Onsager metric data on `ι → ℝ` induced by a symmetric positive-semidefinite
friction matrix $M$. -/
def matrixOnsagerMetricData [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ)
    (hM_symm : M.transpose = M)
    (hM_psd : ∀ v : ι → ℝ, 0 ≤ dotProduct v (M.mulVec v)) :
    SuperMetriplectic.OnsagerMetricData (ι → ℝ) where
  onsager := Matrix.mulVecLin M
  pairing := dotProduct
  metric_symmetric := fun x y => by
    change dotProduct x (M.mulVec y) = dotProduct y (M.mulVec x)
    rw [Matrix.dotProduct_mulVec, ← hM_symm, Matrix.vecMul_transpose, dotProduct_comm]
    rw [hM_symm]
  metric_nonnegative := hM_psd
  pairing_zero_right := fun x => dotProduct_zero x

/-- Explicit finite-dimensional bridge producing a `SuperMetriplectic.MetriplecticFlow (ι → ℝ)`
from a Poisson matrix $L$, an Onsager friction matrix $M$, and Casimir-orthogonal forces
$dH, dS : \iota \to \mathbb{R}$. -/
def matrixMetriplecticFlow [Fintype ι] [DecidableEq ι]
    (L M : Matrix ι ι ℝ)
    (hM_symm : M.transpose = M)
    (hM_psd : ∀ v : ι → ℝ, 0 ≤ dotProduct v (M.mulVec v))
    (dH dS : ι → ℝ)
    (h_casH : M.mulVec dH = 0) :
    SuperMetriplectic.MetriplecticFlow (ι → ℝ) where
  metric := matrixOnsagerMetricData M hM_symm hM_psd
  entropyForce := dS
  energyForce := dH
  reversibleFlow := L.mulVec dH
  dissipativeFlow := M.mulVec dS
  totalFlow := L.mulVec dH + M.mulVec dS
  entropyProduction := dotProduct dS (M.mulVec dS)
  dissipativeFlow_eq_onsager_entropy := rfl
  totalFlow_eq_reversible_add_dissipative := rfl
  energy_degeneracy := h_casH
  entropyProduction_eq_quadratic := rfl

/-- Full First Law of Thermodynamics on `matrixMetriplecticFlow`: when $L$ is skew-symmetric
($L^T = -L$) and $M dH = 0$, the total metriplectic flow conserves energy:
$\langle dH, L dH + M dS \rangle = 0$. -/
theorem matrixMetriplecticFlow_total_energy_rate_zero [Fintype ι] [DecidableEq ι]
    (L M : Matrix ι ι ℝ)
    (hL_skew : L.transpose = -L)
    (hM_symm : M.transpose = M)
    (hM_psd : ∀ v : ι → ℝ, 0 ≤ dotProduct v (M.mulVec v))
    (dH dS : ι → ℝ)
    (h_casH : M.mulVec dH = 0) :
    dotProduct dH
      (matrixMetriplecticFlow L M hM_symm hM_psd dH dS h_casH).totalFlow = 0 := by
  let F := matrixMetriplecticFlow L M hM_symm hM_psd dH dS h_casH
  change dotProduct dH (L.mulVec dH + M.mulVec dS) = 0
  have hdiss : dotProduct dH (M.mulVec dS) = 0 := F.dissipative_energy_change_eq_zero
  rw [dotProduct_add, dotProduct_mulVec_of_skewSymmetric L hL_skew dH, hdiss, add_zero]

/-- Full Second Law of Thermodynamics on `matrixMetriplecticFlow`: when $L$ is skew-symmetric
($L^T = -L$) and $dS$ is a Casimir of $L$ ($L dS = 0$), the total entropy rate equals the
nonnegative Onsager entropy production:
$\langle dS, L dH + M dS \rangle = \langle dS, M dS \rangle$. -/
theorem matrixMetriplecticFlow_total_entropy_rate_eq [Fintype ι] [DecidableEq ι]
    (L M : Matrix ι ι ℝ)
    (hL_skew : L.transpose = -L)
    (hM_symm : M.transpose = M)
    (hM_psd : ∀ v : ι → ℝ, 0 ≤ dotProduct v (M.mulVec v))
    (dH dS : ι → ℝ)
    (h_casH : M.mulVec dH = 0)
    (h_casS : L.mulVec dS = 0) :
    dotProduct dS
      (matrixMetriplecticFlow L M hM_symm hM_psd dH dS h_casH).totalFlow =
      (matrixMetriplecticFlow L M hM_symm hM_psd dH dS h_casH).entropyProduction := by
  change dotProduct dS (L.mulVec dH + M.mulVec dS) = dotProduct dS (M.mulVec dS)
  have h_rev : dotProduct dS (L.mulVec dH) = 0 := by
    calc
      dotProduct dS (L.mulVec dH) = dotProduct (L.vecMul dS) dH := Matrix.dotProduct_mulVec dS L dH
      _ = dotProduct (L.transpose.mulVec dS) dH := by rw [← Matrix.mulVec_transpose]
      _ = dotProduct ((-L).mulVec dS) dH := by rw [hL_skew]
      _ = 0 := by rw [Matrix.neg_mulVec, h_casS, neg_zero, zero_dotProduct]
  rw [dotProduct_add, h_rev, zero_add]

/-- Concrete $2 \times 2$ planar Onsager friction matrix projecting onto the first coordinate. -/
def planarOnsagerMatrix : PlanarRotation.Mat2 := !![1, 0; 0, 0]

/-- `planarOnsagerMatrix` is symmetric. -/
theorem planarOnsagerMatrix_transpose :
    planarOnsagerMatrix.transpose = planarOnsagerMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- `planarOnsagerMatrix` is positive semidefinite: $v \cdot (M v) = (v_0)^2 \ge 0$. -/
theorem planarOnsagerMatrix_psd (v : Fin 2 → ℝ) :
    0 ≤ dotProduct v (planarOnsagerMatrix.mulVec v) := by
  have h : dotProduct v (planarOnsagerMatrix.mulVec v) = v 0 * v 0 := by
    simp [planarOnsagerMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  rw [h]
  exact mul_self_nonneg (v 0)

/-- `PlanarRotation.ellipticGenerator` is skew-symmetric. -/
theorem ellipticGenerator_skew :
    PlanarRotation.ellipticGenerator.transpose = -PlanarRotation.ellipticGenerator := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PlanarRotation.ellipticGenerator]

/-- Concrete $2 \times 2$ Hamiltonian force vector $dH = (0, 1)^T$ in the kernel of `planarOnsagerMatrix`. -/
def planarEnergyForce : Fin 2 → ℝ := ![0, 1]

/-- Concrete $2 \times 2$ entropy force vector $dS = (1, 0)^T$ along the dissipative axis. -/
def planarEntropyForce : Fin 2 → ℝ := ![1, 0]

/-- `planarEnergyForce` lies in the kernel of `planarOnsagerMatrix`. -/
theorem planarOnsagerMatrix_energy_casimir :
    planarOnsagerMatrix.mulVec planarEnergyForce = 0 := by
  ext i
  fin_cases i <;>
    simp [planarOnsagerMatrix, planarEnergyForce, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Concrete, unconditional $2 \times 2$ `SuperMetriplectic.MetriplecticFlow (Fin 2 → ℝ)` witness
combining symplectic rotation by `ellipticGenerator` and rank-1 Onsager relaxation. -/
def planarMetriplecticFlowWitness : SuperMetriplectic.MetriplecticFlow (Fin 2 → ℝ) :=
  matrixMetriplecticFlow
    PlanarRotation.ellipticGenerator
    planarOnsagerMatrix
    planarOnsagerMatrix_transpose
    planarOnsagerMatrix_psd
    planarEnergyForce
    planarEntropyForce
    planarOnsagerMatrix_energy_casimir

/-- In the concrete $2 \times 2$ planar metriplectic witness, total energy is strictly conserved
and entropy production equals $1$. -/
theorem planarMetriplecticFlowWitness_energy_and_entropy :
    dotProduct planarEnergyForce planarMetriplecticFlowWitness.totalFlow = 0 ∧
      planarMetriplecticFlowWitness.entropyProduction = 1 := by
  refine ⟨matrixMetriplecticFlow_total_energy_rate_zero
    PlanarRotation.ellipticGenerator planarOnsagerMatrix ellipticGenerator_skew
    planarOnsagerMatrix_transpose planarOnsagerMatrix_psd
    planarEnergyForce planarEntropyForce planarOnsagerMatrix_energy_casimir, ?_⟩
  change dotProduct planarEntropyForce (planarOnsagerMatrix.mulVec planarEntropyForce) = 1
  simp [planarEntropyForce, planarOnsagerMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_two]

/-!
### Archetype IV — Hypercomplex Loxodromic Phase Dynamics & Thermofield Double to Souriau Gibbs KMS Equilibrium
-/

/-- The $2 \times 2$ loxodromic propagator combining dissipative rapidity contraction
$e^{-\gamma t}$ and symplectic phase rotation $R(\omega t)$. -/
def loxodromicPropagator (γ ω t : ℝ) : PlanarRotation.Mat2 :=
  Real.exp (-γ * t) • PlanarRotation.rotation (ω * t)

/-- At $t = 0$, the loxodromic propagator is the $2 \times 2$ identity matrix. -/
theorem loxodromicPropagator_zero (γ ω : ℝ) :
    loxodromicPropagator γ ω 0 = 1 := by
  unfold loxodromicPropagator
  rw [mul_zero, Real.exp_zero, mul_zero, PlanarRotation.rotation_zero, one_smul]

/-- One-parameter semigroup law for the loxodromic propagator:
$P_{\gamma, \omega}(t + s) = P_{\gamma, \omega}(t) P_{\gamma, \omega}(s)$. -/
theorem loxodromicPropagator_add (γ ω t s : ℝ) :
    loxodromicPropagator γ ω (t + s) =
      loxodromicPropagator γ ω t * loxodromicPropagator γ ω s := by
  unfold loxodromicPropagator
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, PlanarRotation.rotation_mul_rotation]
  rw [exp_neg_gamma_add_eq γ t s]
  have h_ang : ω * (t + s) = ω * t + ω * s := mul_add ω t s
  rw [h_ang]

/-- Planar rotation preserves the Euclidean dot product on `Fin 2 → ℝ`. -/
theorem rotation_preserves_dotProduct (φ : ℝ) (u v : Fin 2 → ℝ) :
    dotProduct ((PlanarRotation.rotation φ).mulVec u)
      ((PlanarRotation.rotation φ).mulVec v) = dotProduct u v := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec,
    PlanarRotation.rotation_transpose_mul_self, Matrix.vecMul_one]

/-- Under the loxodromic propagator, the Euclidean inner product contracts exponentially
at rate $e^{-2\gamma t}$ while the rotational phase cancels out:
$\langle P(t) u, P(t) v \rangle = e^{-2\gamma t} \langle u, v \rangle$. -/
theorem loxodromicPropagator_dotProduct_decay (γ ω t : ℝ) (u v : Fin 2 → ℝ) :
    dotProduct ((loxodromicPropagator γ ω t).mulVec u)
      ((loxodromicPropagator γ ω t).mulVec v) =
      Real.exp (-2 * γ * t) * dotProduct u v := by
  unfold loxodromicPropagator
  rw [Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, smul_eq_mul, ← mul_assoc, rotation_preserves_dotProduct]
  rw [exp_mul_exp_eq_neg_two γ t]

/-- **Polar Equivariance of the Loxodromic Propagator with `CanonicalRapidityAngleMetriplecticFlow.flowMap`**:
Acting with `loxodromicPropagator γ ω t` on a polar-parametrized vector $r_0 R(\theta_0) v$
evolves the radial and angular parameters directly by `flowMap γ ω t (r₀, θ₀)`. -/
theorem loxodromicPropagator_polar_eq_flowMap (γ ω t r₀ θ₀ : ℝ) (v : Fin 2 → ℝ) :
    (loxodromicPropagator γ ω t).mulVec (r₀ • (PlanarRotation.rotation θ₀).mulVec v) =
      (CanonicalRapidityAngleMetriplecticFlow.flowMap γ ω t (r₀, θ₀)).1 •
        (PlanarRotation.rotation
          (CanonicalRapidityAngleMetriplecticFlow.flowMap γ ω t (r₀, θ₀)).2).mulVec v := by
  unfold loxodromicPropagator CanonicalRapidityAngleMetriplecticFlow.flowMap
  dsimp only
  rw [Matrix.mulVec_smul, Matrix.smul_mulVec, smul_comm, smul_smul,
    Matrix.mulVec_mulVec, PlanarRotation.rotation_mul_rotation, add_comm (ω * t) θ₀]

/-- **Loxodromic Logarithmic Spiral Equation**:
Along `CanonicalRapidityAngleMetriplecticFlow.flowMap γ ω t (r₀, θ₀)` with $\omega \ne 0$,
the radial rapidity coordinate $r(t)$ is an exponential spiral of the angular increment
$\theta(t) - \theta_0$:
$r(t) = r_0 \exp(-(\gamma / \omega) (\theta(t) - \theta_0))$. -/
theorem loxodromic_spiral_angle_law (γ ω t r₀ θ₀ : ℝ) (hω : ω ≠ 0) :
    (CanonicalRapidityAngleMetriplecticFlow.flowMap γ ω t (r₀, θ₀)).1 =
      r₀ * Real.exp (-(γ / ω) *
        ((CanonicalRapidityAngleMetriplecticFlow.flowMap γ ω t (r₀, θ₀)).2 - θ₀)) := by
  unfold CanonicalRapidityAngleMetriplecticFlow.flowMap
  dsimp only
  rw [spiral_exponent_identity γ ω t θ₀ hω, mul_comm]

/-- Full finite quantum spectrum on a `Fintype` index type `ι`. -/
def fullQuantumSpectrum [Fintype ι] [DecidableEq ι] (energy : ι → ℝ) :
    ThermofieldDouble.FiniteQuantumSpectrum ι where
  levels := Finset.univ
  energy := energy

/-- The partition function of `fullQuantumSpectrum energy` coincides identically with
`SouriauMassieuPlanckFunctional.souriauPartition`. -/
theorem fullQuantumSpectrum_partition_eq_souriauPartition [Fintype ι] [DecidableEq ι]
    (energy : ι → ℝ) (β : ℝ) :
    (fullQuantumSpectrum energy).partition β =
      SouriauMassieuPlanckFunctional.souriauPartition β energy := rfl

/-- Real zero-time Thermofield Double amplitude
$\psi_n(\beta) = e^{-\beta E_n / 2} / \sqrt{Z(\beta)}$. -/
def tfdRealAmplitude [Fintype ι] (energy : ι → ℝ) (β : ℝ) (n : ι) : ℝ :=
  Real.exp (-(β / 2) * energy n) /
    Real.sqrt (SouriauMassieuPlanckFunctional.souriauPartition β energy)

/-- Coercing the real zero-time TFD amplitude to $\mathbb{C}$ recovers the complex TFD
coefficient `tfdCoeff β 0 0 n` of `fullQuantumSpectrum energy`. -/
theorem tfdRealAmplitude_coe_eq_tfdCoeff_zero [Fintype ι] [DecidableEq ι]
    (energy : ι → ℝ) (β : ℝ) (n : ι) :
    ((tfdRealAmplitude energy β n : ℝ) : ℂ) =
      (fullQuantumSpectrum energy).tfdCoeff β 0 0 n := by
  rw [(fullQuantumSpectrum energy).tfdCoeff_zero_time β n,
    fullQuantumSpectrum_partition_eq_souriauPartition]
  dsimp [tfdRealAmplitude, fullQuantumSpectrum]
  push_cast
  rfl

/-- **Thermofield Double to Souriau Gibbs KMS Bridge**:
Squaring the real zero-time Thermofield Double amplitude at state $n$ yields Souriau's
Gibbs weight $\rho_n(\beta) = e^{-\beta E_n} / Z(\beta)$. -/
theorem tfdRealAmplitude_sq_eq_souriau_gibbsWeight [Fintype ι] [Nonempty ι]
    (energy : ι → ℝ) (β : ℝ) (n : ι) :
    (tfdRealAmplitude energy β n) ^ 2 =
      SouriauMassieuPlanckFunctional.gibbsWeight β energy n := by
  unfold tfdRealAmplitude SouriauMassieuPlanckFunctional.gibbsWeight
  rw [div_pow, exp_neg_half_mul_sq β (energy n)]
  have hZ : 0 ≤ SouriauMassieuPlanckFunctional.souriauPartition β energy :=
    le_of_lt (SouriauMassieuPlanckFunctional.souriauPartition_pos β energy)
  rw [Real.sq_sqrt hZ]

/-- **Thermofield Double to Souriau Lie-Algebraic Gibbs KMS Bridge**:
Squaring the real zero-time Thermofield Double amplitude associated with Souriau's moment
energy $E_\beta(x) = \langle J(x), \beta \rangle$ at unit scale recovers the Lie-algebraic
Gibbs weight `souriauLieGibbs J β x`. -/
theorem tfdRealAmplitude_sq_eq_souriauLieGibbs [Fintype ι] [Nonempty ι]
    {g : Type*} [AddCommGroup g] [Module ℝ g]
    (J : ι → (g →ₗ[ℝ] ℝ)) (β : g) (x : ι) :
    (tfdRealAmplitude (souriauMomentEnergy J β) 1 x) ^ 2 = souriauLieGibbs J β x :=
  tfdRealAmplitude_sq_eq_souriau_gibbsWeight (souriauMomentEnergy J β) 1 x

/-- The squared real Thermofield Double amplitudes sum to 1 across the finite state space. -/
theorem tfdRealAmplitude_sum_sq_eq_one [Fintype ι] [Nonempty ι]
    (energy : ι → ℝ) (β : ℝ) :
    ∑ n : ι, (tfdRealAmplitude energy β n) ^ 2 = 1 := by
  simp_rw [tfdRealAmplitude_sq_eq_souriau_gibbsWeight]
  exact SouriauMassieuPlanckFunctional.gibbsWeight_sum_eq_one β energy

end InfoGeometry.SuperMetriplectic.MajoranaSouriauMetriplecticLoxodromic

end
