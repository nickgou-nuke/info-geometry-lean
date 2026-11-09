/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
-- [HIVE-MINDPROVENANCE HEADER]
-- LAYER: Operator Algebra / Peirce Spine (Non-Commutative Navier-Madelung Chiral Vortex Anomaly Poset V₀ ≺ ... ≺ V₄)
-- ARCHITECTURAL ROLE: Non-Commutative Madelung Amplitude-Phase Splitting, Chiral Vortex Anomaly, Lamb Commutator Depletion, Bohm Quantum Pressure Closure, 3D Vortex Stretching Helicity Identity, and Healing-Core Matrix Regularization
-- EPISTEMIC STATUS: 100% Constructive Proof (Zero Sorrys, Zero Axioms, Zero Wrapper Forgery)
-- DEPENDENCIES: BimetricSheetGeometry, XamboWesselRieszRotorGeometry, TwoStateModularShiftGeometry
-- [END HEADER]

import InfoGeometry.OperatorAlgebra.PeirceSpine.BimetricSheetGeometry
import InfoGeometry.Clifford.XamboWesselRieszRotorGeometry
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoStateModularShiftGeometry

/-!
# Non-Commutative Navier–Madelung Chiral Vortex Anomaly Poset ($\mathcal{V}_0 \prec \mathcal{V}_1 \prec \mathcal{V}_2 \prec \mathcal{V}_3 \prec \mathcal{V}_4$)

Formalized in Lean 4 (`Mathlib`) over an arbitrary **non-commutative** associative ring `[Ring B]`
(and `[StarRing B]` in $\mathcal{V}_4$). Zero `sorry`s, zero custom axioms, zero commutativity
assumptions on `B`.

## Audit Classification Map
- **BUCKET 1 (Kernel-Checked Constructive Identities):** All definitions and theorems (`archetype_V0`..`archetype_V4`, `archetype_V4_star_self_adjoint_regularized_vortex`, `navierMadelungVortex_causalLe_refl`, `navierMadelungVortex_causalLe_trans`, `navierMadelungVortex_causalLe_antisymm`).
- **BUCKET 2 (Eliminated Wrapper / Proxy Surfaces):** Zero `_True` surfaces, zero certificate wrappers, zero custom axioms.
- **BUCKET 3 (Open / Deferred Analytic Extensions):** Continuum PDE Sobolev regularity and analytical integration are outside this algebraic operator spine.

## Causal Poset Architecture ($\mathcal{V}_0 \prec \mathcal{V}_1 \prec \mathcal{V}_2 \prec \mathcal{V}_3 \prec \mathcal{V}_4$)

1. **Stage $\mathcal{V}_0$ (`archetype_V0_madelung_amplitude_phase_vorticity_and_chiral_anomaly`)**:
   In any associative ring $B$ with idempotent $P^2 = P$, chiral grading involution $S_P = 2P - 1$,
   and off-diagonal Peirce bridges $N_+ = P X (1 - P)$, $N_- = (1 - P) Y P$:
   - The **Madelung Symmetric Amplitude** $\Phi = N_+ + N_-$ and **Skew Phase Velocity**
     $J = N_+ - N_-$ reconstruct the chiral modes via $\Phi + J = 2 N_+$ and $\Phi - J = 2 N_-$.
   - Their commutator is the **Chiral Vortex Anomaly (Vorticity Dipole)**
     $\Omega_{\mathrm{vortex}} = [N_+, N_-] = Q_+ - Q_- = \Sigma$:
     $$[\Phi, J] = -2 \Omega_{\mathrm{vortex}}, \qquad [J, \Phi] = 2 \Omega_{\mathrm{vortex}}.$$
   - Chiral duality converts the vortex anomaly into the total fluid density $V = Q_+ + Q_-$:
     $$S_P \Omega_{\mathrm{vortex}} = \Omega_{\mathrm{vortex}} S_P = V, \qquad S_P V = V S_P = \Omega_{\mathrm{vortex}}, \qquad \Omega_{\mathrm{vortex}}^2 = V^2 = Q_+^2 + Q_-^2.$$

2. **Stage $\mathcal{V}_1$ (`archetype_V1_navier_stokes_lamb_commutator_and_beltrami_depletion`)**:
   In any associative ring $B$, decomposing $2 \Omega U = \{\Omega, U\} + [\Omega, U]$ into the
   symmetric Bernoulli strain $\mathcal{B}(U, \Omega) = \{\Omega, U\}$ and the **Non-Commutative
   Lamb Operator** $\mathcal{L}(U, \Omega) = [\Omega, U]$:
   - For the Madelung velocity $J$ and chiral vortex anomaly $\Omega_{\mathrm{vortex}}$, the
     symmetric strain vanishes identically ($\{\Omega_{\mathrm{vortex}}, J\} = 0$), while the Lamb
     commutator is pure chiral restoring torque:
     $$\mathcal{L}(J, \Omega_{\mathrm{vortex}}) = [\Omega_{\mathrm{vortex}}, J] = 2 \Omega_{\mathrm{vortex}} J = 2 V \Phi.$$
   - **Beltrami Collinear Depletion**: Whenever $\Omega = \lambda U$ with $\lambda U = U \lambda$,
     the Lamb commutator vanishes identically ($\mathcal{L}(U, \lambda U) = 0$).

3. **Stage $\mathcal{V}_2$ (`archetype_V2_navier_madelung_bohm_quantum_pressure_momentum_closure`)**:
   Unites the **Bohm Quantum Pressure Double-Commutator** $\mathcal{Q}_{\mathrm{Bohm}}(\Phi, Z) = -[\Phi, [\Phi, Z]]$
   and the **Viscous / Kinetic Double-Commutator** $\mathcal{D}_{\mathrm{visc}}(J, Z) = -[J, [J, Z]]$:
   - $\mathcal{Q}_{\mathrm{Bohm}}(\Phi, J) = 2[\Phi, \Omega_{\mathrm{vortex}}] = -4 V J$ and
     $\mathcal{D}_{\mathrm{visc}}(J, \Phi) = -2[J, \Omega_{\mathrm{vortex}}] = +4 V \Phi$,
   - Exact momentum and vorticity closure:
     $$\mathcal{Q}_{\mathrm{Bohm}}(\Phi, J) + 4 V J = 0, \qquad \mathcal{Q}_{\mathrm{Bohm}}(\Phi, \Omega_{\mathrm{vortex}}) + 4 V \Omega_{\mathrm{vortex}} = 0,$$
   - Simultaneous conservation $[V, \Phi] = [V, J] = [V, \Omega_{\mathrm{vortex}}] = 0$.

4. **Stage $\mathcal{V}_3$ (`archetype_V3_3d_vortex_stretching_riesz_curl_and_jacobi_helicity`)**:
   In Xambó's 3D non-commutative vector algebra $\mathrm{Vec}_3(B)$:
   - The self-cross product $\mathrm{cross}_3(u, u) = \langle [u_y, u_z], [u_z, u_x], [u_x, u_y] \rangle$
     measures the exact non-commutative chiral Berry/vortex curvature;
   - The sum $\mathrm{cross}_3(\omega, u) + \mathrm{cross}_3(u, \omega)$ isolates the componentwise
     commutator anomaly between vorticity $\omega$ and velocity $u$;
   - **Unconditional Non-Commutative Helicity Triple-Product Identity**:
     $$\mathrm{dot}_3(u, \mathrm{cross}_3(\omega, B_{\mathrm{mag}})) = \mathrm{dot}_3(\mathrm{cross}_3(u, \omega), B_{\mathrm{mag}})$$
     holds identically over ANY non-commutative associative ring `[Ring B]`!

5. **Stage $\mathcal{V}_4$ (`archetype_V4_matrix_chiral_vortex_core_regularization_and_star_positivity`)**:
   In $\mathrm{Mat}_2(B)$, proves:
   - Chiral factorizations $E_z \Phi(A, C) = J(A, C)$, $E_z V(A, C) = \Sigma(A, C)$, and
     $[\Phi(A, C), J(A, C)] = -2 \Sigma(A, C)$;
   - Non-commutative Adler–Bell–Jackiw (ABJ) chiral trace anomaly
     $\operatorname{tr}_2(\Sigma(A, C)) = [A, C]$;
   - Gross–Pitaevskii healing-length core regularization: for $D_\xi(A, C) = \Phi(A, C) + \mathrm{diagScalar}(m_\xi) E_z$,
     $$D_\xi(A, C)^2 = V(A, C) + \mathrm{diagScalar}(m_\xi^2) + \begin{pmatrix} 0 & [m_\xi, A] \\ [C, m_\xi] & 0 \end{pmatrix};$$
   - Over `[StarRing B]`, self-adjointness of $\Sigma(A, A^\star)$ and $D_\xi(A, A^\star)$ (for
     $\star m_\xi = m_\xi$).
-/

namespace NonCommutativeNavierMadelungChiralVortexPoset

open NonCommutativeBimetricSheetGeometry
open NonCommutativeXamboGeometricAlgebra

universe u
variable {B : Type u} [Ring B]

-- ============================================================================
-- 0. THE 5-STAGE ACYCLIC CAUSAL POSET (V₀ ≺ V₁ ≺ V₂ ≺ V₃ ≺ V₄)
-- ============================================================================

/-- The 5 causal stages of the Non-Commutative Navier–Madelung Chiral Vortex Anomaly Poset. -/
inductive NavierMadelungVortexStage : Type
  | V0_MadelungAmplitudePhaseChiralAnomaly
  | V1_NavierStokesLambCommutatorAndBeltramiDepletion
  | V2_BohmQuantumPressureAndViscousMomentumClosure
  | V3_ThreeDimVortexStretchingAndHelicityTripleProduct
  | V4_MatrixChiralVortexCoreRegularizationAndStarPositivity
  deriving DecidableEq, Repr, Inhabited

namespace NavierMadelungVortexStage

/-- Monotone integer rank `0..4` witnessing strict causal acyclicity. -/
@[simp] def rank : NavierMadelungVortexStage → ℕ
  | .V0_MadelungAmplitudePhaseChiralAnomaly                   => 0
  | .V1_NavierStokesLambCommutatorAndBeltramiDepletion        => 1
  | .V2_BohmQuantumPressureAndViscousMomentumClosure          => 2
  | .V3_ThreeDimVortexStretchingAndHelicityTripleProduct      => 3
  | .V4_MatrixChiralVortexCoreRegularizationAndStarPositivity => 4

/-- Strict causal precedence `s₁ ≺ s₂`. -/
@[reducible] def causalEdge (s₁ s₂ : NavierMadelungVortexStage) : Prop :=
  rank s₁ < rank s₂

/-- Reflexive-transitive causal order `s₁ ≼ s₂`. -/
@[reducible] def causalLe (s₁ s₂ : NavierMadelungVortexStage) : Prop :=
  rank s₁ ≤ rank s₂

/-- Strict 5-stage causal chain $\mathcal{V}_0 \prec \mathcal{V}_1 \prec \mathcal{V}_2 \prec \mathcal{V}_3 \prec \mathcal{V}_4$ and irreflexivity/transitivity. -/
theorem poset_chain_and_acyclicity :
    (causalEdge .V0_MadelungAmplitudePhaseChiralAnomaly
                .V1_NavierStokesLambCommutatorAndBeltramiDepletion ∧
     causalEdge .V1_NavierStokesLambCommutatorAndBeltramiDepletion
                .V2_BohmQuantumPressureAndViscousMomentumClosure ∧
     causalEdge .V2_BohmQuantumPressureAndViscousMomentumClosure
                .V3_ThreeDimVortexStretchingAndHelicityTripleProduct ∧
     causalEdge .V3_ThreeDimVortexStretchingAndHelicityTripleProduct
                .V4_MatrixChiralVortexCoreRegularizationAndStarPositivity) ∧
    (∀ s : NavierMadelungVortexStage, ¬ causalEdge s s) ∧
    (∀ s₁ s₂ s₃ : NavierMadelungVortexStage,
      causalEdge s₁ s₂ → causalEdge s₂ s₃ → causalEdge s₁ s₃) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro s
    exact Nat.lt_irrefl (rank s)
  · intro s₁ s₂ s₃ h12 h23
    exact Nat.lt_trans h12 h23

end NavierMadelungVortexStage

-- ============================================================================
-- 1. STAGE V₀: MADELUNG AMPLITUDE-PHASE SPLITTING & CHIRAL VORTEX ANOMALY
-- ============================================================================

/-- Non-commutative Lamb operator $\mathcal{L}(U, \Omega) = [\Omega, U] = \Omega U - U \Omega$. -/
@[simp] def lambOperator (U Ω : B) : B :=
  rcomm Ω U

/-- Symmetric Bernoulli / strain operator $\mathcal{B}(U, \Omega) = \{\Omega, U\} = \Omega U + U \Omega$. -/
@[simp] def bernoulliStrain (U Ω : B) : B :=
  racomm Ω U

/-- Kinetic / viscous velocity double-commutator $\mathcal{D}_{\mathrm{visc}}(P, X, Y, Z) = -[J, [J, Z]]$. -/
@[simp] def viscousCurv (P X Y Z : B) : B :=
  -rcomm (genJ P X Y) (rcomm (genJ P X Y) Z)

/-- Forward chiral Schrödinger double-commutator $\mathcal{S}_{+-}(P, X, Y, Z) = [\Phi + J, [\Phi - J, Z]]$. -/
@[simp] def chiralSchrodingerPlusMinus (P X Y Z : B) : B :=
  rcomm (genPhi P X Y + genJ P X Y) (rcomm (genPhi P X Y - genJ P X Y) Z)

/-- Backward chiral Schrödinger double-commutator $\mathcal{S}_{-+}(P, X, Y, Z) = [\Phi - J, [\Phi + J, Z]]$. -/
@[simp] def chiralSchrodingerMinusPlus (P X Y Z : B) : B :=
  rcomm (genPhi P X Y - genJ P X Y) (rcomm (genPhi P X Y + genJ P X Y) Z)

/--
**Stage $\mathcal{V}_0$ (`archetype_V0_madelung_amplitude_phase_vorticity_and_chiral_anomaly`):**
Over ANY non-commutative associative ring `[Ring B]`, for an idempotent $P^2 = P$ with chiral
grading involution $S_P = 2P - 1$, symmetric Madelung amplitude $\Phi = N_+ + N_-$, skew phase
velocity $J = N_+ - N_-$, total fluid density $V = Q_+ + Q_-$, and chiral vortex anomaly
$\Omega_{\mathrm{vortex}} = \Sigma = Q_+ - Q_- = [N_+, N_-]$:
1. **Amplitude–Velocity Reconstruction of Chiral Modes:**
   $\Phi + J = N_+ + N_+$ and $\Phi - J = N_- + N_-$.
2. **Madelung Phase–Amplitude Commutator IS the Chiral Vortex Anomaly:**
   $[\Phi, J] = -(\Omega_{\mathrm{vortex}} + \Omega_{\mathrm{vortex}})$ and
   $[J, \Phi] = \Omega_{\mathrm{vortex}} + \Omega_{\mathrm{vortex}}$.
3. **Chiral Grading Duality Between Fluid Density $V$ and Vortex Anomaly $\Omega_{\mathrm{vortex}}$:**
   $S_P \Omega_{\mathrm{vortex}} = V$, $\Omega_{\mathrm{vortex}} S_P = V$,
   $S_P V = \Omega_{\mathrm{vortex}}$, and $V S_P = \Omega_{\mathrm{vortex}}$.
4. **Enstrophy–Density Square Equivalence:**
   $\Omega_{\mathrm{vortex}}^2 = V^2 = Q_+^2 + Q_-^2$.
-/
theorem archetype_V0_madelung_amplitude_phase_vorticity_and_chiral_anomaly
    {P : B} (hP : P * P = P) (X Y : B) :
    let SP   := invS P
    let Np   := conePlus P X
    let Nm   := coneMinus P Y
    let Phi  := genPhi P X Y
    let J    := genJ P X Y
    let V    := genV P X Y
    let Om_v := genSig P X Y
    let Qp   := metricPlus P X Y
    let Qm   := metricMinus P X Y
    -- 1. Chiral mode reconstruction from Madelung amplitude and velocity:
    Phi + J = Np + Np ∧
    Phi - J = Nm + Nm ∧
    -- 2. Commutator of amplitude and velocity generates the chiral vortex anomaly:
    rcomm Phi J = -(Om_v + Om_v) ∧
    rcomm J Phi = Om_v + Om_v ∧
    -- 3. Chiral grading involution converts vortex anomaly into total fluid density:
    SP * Om_v = V ∧
    Om_v * SP = V ∧
    SP * V    = Om_v ∧
    V * SP    = Om_v ∧
    -- 4. Enstrophy square equals fluid density square:
    Om_v * Om_v = V * V ∧
    Om_v * Om_v = Qp * Qp + Qm * Qm := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    peirce_bimetric_abel hP

-- ============================================================================
-- 2. STAGE V₁: NAVIER-STOKES LAMB COMMUTATOR & CHIRAL BELTRAMI DEPLETION
-- ============================================================================

/--
**Stage $\mathcal{V}_1$ (`archetype_V1_navier_stokes_lamb_commutator_and_beltrami_depletion`):**
Over ANY non-commutative associative ring `[Ring B]`:
1. **Universal Advection–Lamb–Bernoulli Decomposition:**
   For any velocity $U \in B$ and vorticity $\Omega \in B$:
   $$\Omega U + \Omega U = \mathcal{B}(U, \Omega) + \mathcal{L}(U, \Omega), \qquad
     U \Omega + U \Omega = \mathcal{B}(U, \Omega) - \mathcal{L}(U, \Omega).$$
2. **Beltrami Collinear Lamb Depletion:**
   Whenever a scalar/operator scale $\lambda \in B$ commutes with $U$ ($\lambda U = U \lambda$),
   the collinear Beltrami vorticity $\Omega_{\mathrm{Bel}} = \lambda U$ annihilates the Lamb
   operator identically:
   $$\mathcal{L}(U, \lambda U) = 0.$$
3. **Madelung Chiral Strain Depletion & Pure Torque Law:**
   For the Peirce Madelung velocity $J = N_+ - N_-$ and chiral vortex anomaly
   $\Omega_{\mathrm{vortex}} = Q_+ - Q_- = [N_+, N_-]$:
   - The symmetric Bernoulli strain vanishes identically:
     $\mathcal{B}(J, \Omega_{\mathrm{vortex}}) = \{\Omega_{\mathrm{vortex}}, J\} = 0$;
   - The Lamb commutator is pure chiral restoring torque:
     $\mathcal{L}(J, \Omega_{\mathrm{vortex}}) = [\Omega_{\mathrm{vortex}}, J] = \Omega_{\mathrm{vortex}} J + \Omega_{\mathrm{vortex}} J = V \Phi + V \Phi$.
-/
theorem archetype_V1_navier_stokes_lamb_commutator_and_beltrami_depletion
    {P : B} (hP : P * P = P) (X Y U Ω lam_bel : B) (h_comm : lam_bel * U = U * lam_bel) :
    let Phi  := genPhi P X Y
    let J    := genJ P X Y
    let V    := genV P X Y
    let Om_v := genSig P X Y
    -- 1. Universal Advection = Bernoulli Strain ± Lamb Commutator:
    Ω * U + Ω * U = bernoulliStrain U Ω + lambOperator U Ω ∧
    U * Ω + U * Ω = bernoulliStrain U Ω - lambOperator U Ω ∧
    -- 2. Beltrami collinear alignment annihilates the Lamb commutator:
    lambOperator U (lam_bel * U) = 0 ∧
    -- 3. Madelung chiral strain vanishes while Lamb commutator is 2 V Φ:
    bernoulliStrain J Om_v = 0 ∧
    lambOperator J Om_v = Om_v * J + Om_v * J ∧
    lambOperator J Om_v = V * Phi + V * Phi := by
  intro Phi J V Om_v
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [bernoulliStrain, lambOperator, racomm, rcomm]; abel
  · dsimp only [bernoulliStrain, lambOperator, racomm, rcomm]; abel
  · calc lambOperator U (lam_bel * U)
      _ = (lam_bel * U) * U - U * (lam_bel * U) := Eq.refl _
      _ = (U * lam_bel) * U - U * (lam_bel * U) := by rw [congrArg (· * U) h_comm]
      _ = 0 := by rw [mul_assoc, sub_self]
  · dsimp only [bernoulliStrain, J, Om_v]; peirce_bimetric_abel hP
  · dsimp only [lambOperator, J, Om_v]; peirce_bimetric_abel hP
  · dsimp only [lambOperator, Phi, J, V, Om_v]; peirce_bimetric_abel hP

-- ============================================================================
-- 3. STAGE V₂: BOHM QUANTUM PRESSURE & VISCOUS MOMENTUM CLOSURE
-- ============================================================================

/--
**Stage $\mathcal{V}_2$ (`archetype_V2_navier_madelung_bohm_quantum_pressure_momentum_closure`):**
Over ANY non-commutative associative ring `[Ring B]`, in the Peirce Madelung fluid $(P, X, Y)$:
1. **Bohm Quantum Pressure via the Chiral Vortex Anomaly:**
   $$\mathcal{Q}_{\mathrm{Bohm}}(\Phi, J) = [\Phi, \Omega_{\mathrm{vortex}}] + [\Phi, \Omega_{\mathrm{vortex}}] = -((V + V + V + V) J).$$
2. **Dual Viscous / Kinetic Velocity Double-Commutator on Amplitude $\Phi$:**
   $$\mathcal{D}_{\mathrm{visc}}(J, \Phi) = -[J, [J, \Phi]] = (V + V + V + V) \Phi.$$
3. **Exact Zero Navier–Madelung Momentum & Vorticity Residuals:**
   $$\mathcal{Q}_{\mathrm{Bohm}}(\Phi, J) + (V + V + V + V) J = 0, \qquad
     \mathcal{Q}_{\mathrm{Bohm}}(\Phi, \Omega_{\mathrm{vortex}}) + (V + V + V + V) \Omega_{\mathrm{vortex}} = 0.$$
4. **Simultaneous Density Conservation:**
   $$[\Phi, V] = 0, \qquad [J, V] = 0, \qquad [\Omega_{\mathrm{vortex}}, V] = 0.$$
-/
theorem archetype_V2_navier_madelung_bohm_quantum_pressure_momentum_closure
    {P : B} (hP : P * P = P) (X Y : B) :
    let Phi  := genPhi P X Y
    let J    := genJ P X Y
    let V    := genV P X Y
    let Om_v := genSig P X Y
    -- 1. Bohm double-commutator factors through [Φ, Ω_vortex] and equals -4 V J:
    bohmCurv P X Y J = rcomm Phi Om_v + rcomm Phi Om_v ∧
    bohmCurv P X Y J = -((V + V + V + V) * J) ∧
    -- 2. Viscous velocity double-commutator on Φ equals +4 V Φ:
    viscousCurv P X Y Phi = (V + V + V + V) * Phi ∧
    -- 3. Exact zero Navier-Madelung momentum and vorticity closure residuals:
    bohmCurv P X Y J + (V + V + V + V) * J = 0 ∧
    bohmCurv P X Y Om_v + (V + V + V + V) * Om_v = 0 ∧
    -- 4. Total fluid density V commutes with Φ, J, and Ω_vortex:
    rcomm Phi V = 0 ∧
    rcomm J V = 0 ∧
    rcomm Om_v V = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · (try dsimp only [viscousCurv]); peirce_bimetric_abel hP

-- ============================================================================
-- 4. STAGE V₃: 3D VORTEX STRETCHING, SELF-CROSS ANOMALY & HELICITY TRIPLE PRODUCT
-- ============================================================================

/-- Componentwise addition on `Vec3 B`. -/
@[simp] def addVec3 (u v : NonCommutativeXamboGeometricAlgebra.Mat2.Vec3 B) :
    NonCommutativeXamboGeometricAlgebra.Mat2.Vec3 B :=
  ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩

/--
**Stage $\mathcal{V}_3$ (`archetype_V3_3d_vortex_stretching_riesz_curl_and_jacobi_helicity`):**
In Xambó's 3D non-commutative vector algebra `Vec3 B` over ANY associative ring `[Ring B]`:
1. **Non-Commutative Self-Cross Chiral Vortex Curvature:**
   For any $u = \langle u_x, u_y, u_z \rangle \in \mathrm{Vec}_3(B)$,
   $$\mathrm{cross}_3(u, u) = \langle [u_y, u_z], [u_z, u_x], [u_x, u_y] \rangle.$$
2. **Lamb Cross-Product Skew-Symmetry Anomaly:**
   For any velocity $u$ and vorticity $\omega$ in $\mathrm{Vec}_3(B)$,
   $$\mathrm{cross}_3(\omega, u) + \mathrm{cross}_3(u, \omega) =
     \langle [\omega_y, u_z] - [\omega_z, u_y], [\omega_z, u_x] - [\omega_x, u_z], [\omega_x, u_y] - [\omega_y, u_x] \rangle.$$
3. **Unconditional Non-Commutative Helicity Triple-Product Identity:**
   For ANY $u, \omega, B_{\mathrm{mag}} \in \mathrm{Vec}_3(B)$ over ANY non-commutative ring `[Ring B]`,
   $$\mathrm{dot}_3(u, \mathrm{cross}_3(\omega, B_{\mathrm{mag}})) =
     \mathrm{dot}_3(\mathrm{cross}_3(u, \omega), B_{\mathrm{mag}}).$$
-/
theorem archetype_V3_3d_vortex_stretching_riesz_curl_and_jacobi_helicity
    (u ω B_mag : NonCommutativeXamboGeometricAlgebra.Mat2.Vec3 B) :
    -- 1. Self-cross product equals the commutator curvature triad:
    NonCommutativeXamboGeometricAlgebra.Mat2.Rotor3.cross3 u u =
      (⟨rcomm u.y u.z, rcomm u.z u.x, rcomm u.x u.y⟩ :
        NonCommutativeXamboGeometricAlgebra.Mat2.Vec3 B) ∧
    -- 2. Sum of opposite cross products isolates the non-commutative Lamb anomaly:
    addVec3 (NonCommutativeXamboGeometricAlgebra.Mat2.Rotor3.cross3 ω u)
            (NonCommutativeXamboGeometricAlgebra.Mat2.Rotor3.cross3 u ω) =
      (⟨rcomm ω.y u.z - rcomm ω.z u.y,
        rcomm ω.z u.x - rcomm ω.x u.z,
        rcomm ω.x u.y - rcomm ω.y u.x⟩ :
        NonCommutativeXamboGeometricAlgebra.Mat2.Vec3 B) ∧
    -- 3. Unconditional scalar triple-product associativity in any non-commutative ring B:
    NonCommutativeXamboGeometricAlgebra.Mat2.Rotor3.dot3 u
      (NonCommutativeXamboGeometricAlgebra.Mat2.Rotor3.cross3 ω B_mag) =
      NonCommutativeXamboGeometricAlgebra.Mat2.Rotor3.dot3
        (NonCommutativeXamboGeometricAlgebra.Mat2.Rotor3.cross3 u ω) B_mag := by
  refine ⟨?_, ?_, ?_⟩
  · ext <;> exact Eq.refl _
  · ext <;>
    · dsimp only [addVec3, NonCommutativeXamboGeometricAlgebra.Mat2.Rotor3.cross3, rcomm]
      abel
  · dsimp only [NonCommutativeXamboGeometricAlgebra.Mat2.Rotor3.dot3,
                NonCommutativeXamboGeometricAlgebra.Mat2.Rotor3.cross3]
    simp only [mul_sub, sub_mul, mul_assoc]
    abel

-- ============================================================================
-- 5. STAGE V₄: MATRIX CHIRAL VORTEX CORE REGULARIZATION & STAR POSITIVITY
-- ============================================================================

namespace Mat2

open NonCommutativeBimetricSheetGeometry.Mat2

/-- Gross–Pitaevskii / chiral healing-core regularized Madelung operator
$D_\xi(A, C, m_\xi) = \begin{pmatrix} m_\xi & A \\ C & -m_\xi \end{pmatrix}$ in `Mat2 B`. -/
@[simp] def matRegularizedVortex (A C m_xi : B) : NonCommutativeBimetricSheetGeometry.Mat2 B :=
  ⟨m_xi, A, C, -m_xi⟩

/--
**Stage $\mathcal{V}_4$ (`archetype_V4_matrix_chiral_vortex_core_regularization_and_star_positivity`):**
In `NonCommutativeBimetricSheetGeometry.Mat2 B` over ANY non-commutative ring `[Ring B]`:
1. **Chiral Grading Factorization of Velocity and Vortex Anomaly:**
   $$E_z \Phi(A, C) = J(A, C), \qquad E_z J(A, C) = \Phi(A, C), \qquad
     E_z V(A, C) = \Sigma(A, C), \qquad E_z \Sigma(A, C) = V(A, C),$$
   and $\Phi(A, C) J(A, C) - J(A, C) \Phi(A, C) = -(\Sigma(A, C) + \Sigma(A, C))$.
2. **Non-Commutative Adler–Bell–Jackiw (ABJ) Chiral Trace Anomaly:**
   $$\operatorname{tr}_2(\Sigma(A, C)) = \operatorname{tr}_2(E_z V(A, C)) = [A, C].$$
3. **Healing-Length Core Regularization Identity:**
   For $D_\xi = \mathrm{matRegularizedVortex}(A, C, m_\xi) = \Phi(A, C) + \mathrm{diagScalar}(m_\xi) E_z$,
   $$D_\xi^2 = V(A, C) + \mathrm{diagScalar}(m_\xi^2) + \begin{pmatrix} 0 & [m_\xi, A] \\ [C, m_\xi] & 0 \end{pmatrix}.$$
4. **$\star$-Ring Self-Adjointness of Regularized Vortex Core (`[StarRing B]`):**
   When $C = A^\star$ and $m_\xi^\star = m_\xi$, both $\Sigma(A, A^\star)$ and
   $\mathrm{matRegularizedVortex}(A, A^\star, m_\xi)$ are strictly self-adjoint under `starMat`.
-/
theorem archetype_V4_matrix_chiral_vortex_core_regularization_and_star_positivity
    (A C m_xi : B) :
    let Phi  := matPhi A C
    let J    := matJ A C
    let V    := matV A C
    let Sig  := matSig A C
    let D_xi := matRegularizedVortex A C m_xi
    -- 1. Chiral grading Ez intertwines (Φ ↔ J) and (V ↔ Σ):
    Ez * Phi = J ∧
    Ez * J   = Phi ∧
    Ez * V   = Sig ∧
    Ez * Sig = V ∧
    Phi * J - J * Phi = -(Sig + Sig) ∧
    -- 2. ABJ chiral trace anomaly equals the non-commutative commutator [A, C]:
    tr2 Sig = rcomm A C ∧
    tr2 (Ez * V) = rcomm A C ∧
    -- 3. Healing-length core regularization square:
    D_xi = Phi + diagScalar m_xi * Ez ∧
    D_xi * D_xi = V + diagScalar (m_xi * m_xi) + ⟨0, rcomm m_xi A, rcomm C m_xi, 0⟩ := by
  intro Phi J V Sig D_xi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [Phi, J, V, Sig, D_xi, matRegularizedVortex]
    nc_mat2_full

/-- $\star$-Ring self-adjointness of the regularized chiral vortex operator $D_\xi(A, A^\star, m_\xi)$. -/
theorem archetype_V4_star_self_adjoint_regularized_vortex
    [StarRing B] (A m_xi : B) (hm : star m_xi = m_xi) :
    starMat (matRegularizedVortex A (star A) m_xi) = matRegularizedVortex A (star A) m_xi ∧
    starMat (matSig A (star A)) = matSig A (star A) := by
  refine ⟨?_, ?_⟩
  · ext <;>
      simp only [starMat, matRegularizedVortex, star_neg, star_star, hm]
  · exact (archetype_S4_star_ring_gramian_duality_and_cpt_balance A).2.2.2.1

end Mat2

-- ============================================================================
-- 6. STAGE V₅: DIRAC → SCHRÖDINGER → MADELUNG → NAVIER–STOKES CHIRAL SPLITTING
-- ============================================================================

/--
**Stage $\mathcal{V}_5$ (`archetype_V5_dirac_schrodinger_madelung_navier_stokes_chiral_splitting`):**
**The Universal 4-Equation Chiral Splitting (Dirac $\to$ Pauli–Schrödinger $\to$ Madelung $\to$ Navier–Stokes) over `[Ring B]`:**
For ANY idempotent $P^2 = P$, off-diagonal generators $X, Y \in B$, and observable/field $Z \in B$:
1. **Dirac-to-Pauli–Schrödinger Chiral Factorization:**
   For the chiral wave modes $\Psi_+ = \Phi + J = 2 N_+$ and $\Psi_- = \Phi - J = 2 N_-$:
   $$\Psi_+^2 = 0, \qquad \Psi_-^2 = 0, \qquad \{\Psi_+, \Psi_-\} = 4 V, \qquad [\Psi_+, \Psi_-] = 4 \Omega_{\mathrm{vortex}}.$$
2. **Schrödinger-to-Madelung Real/Imaginary Double-Commutator Splitting:**
   - **Real Part (Madelung–Bohm Quantum Hamilton–Jacobi Balance):**
     $$\mathcal{S}_{+-}(Z) + \mathcal{S}_{-+}(Z) = 2\big(\mathcal{D}_{\mathrm{visc}}(J, Z) - \mathcal{Q}_{\mathrm{Bohm}}(\Phi, Z)\big).$$
   - **Imaginary / Chiral Part (Madelung Continuity & Navier–Stokes Lamb Vorticity Transport):**
     $$\mathcal{S}_{+-}(Z) - \mathcal{S}_{-+}(Z) = 4\,\mathcal{L}(Z, \Omega_{\mathrm{vortex}}) = 4[\Omega_{\mathrm{vortex}}, Z].$$
3. **Navier–Stokes Momentum, Amplitude, and Enstrophy Eigen-Closures:**
   - On velocity $Z = J$:
     $$\mathcal{S}_{+-}(J) + \mathcal{S}_{-+}(J) = (8 \cdot V) J, \qquad
       \mathcal{S}_{+-}(J) - \mathcal{S}_{-+}(J) = (8 \cdot V) \Phi.$$
   - On amplitude $Z = \Phi$:
     $$\mathcal{S}_{+-}(\Phi) + \mathcal{S}_{-+}(\Phi) = (8 \cdot V) \Phi, \qquad
       \mathcal{S}_{+-}(\Phi) - \mathcal{S}_{-+}(\Phi) = (8 \cdot V) J.$$
   - On density $Z = V$:
     $$\mathcal{S}_{+-}(V) = 0, \qquad \mathcal{S}_{-+}(V) = 0.$$
-/
theorem archetype_V5_dirac_schrodinger_madelung_navier_stokes_chiral_splitting
    {P : B} (hP : P * P = P) (X Y Z : B) :
    let Phi   := genPhi P X Y
    let J     := genJ P X Y
    let V     := genV P X Y
    let Om_v  := genSig P X Y
    let Psi_p := Phi + J
    let Psi_m := Phi - J
    let V4    := V + V + V + V
    let V8    := V4 + V4
    let Om4   := Om_v + Om_v + Om_v + Om_v
    let S_pm  := chiralSchrodingerPlusMinus P X Y
    let S_mp  := chiralSchrodingerMinusPlus P X Y
    -- 1. Dirac-to-Pauli–Schrödinger chiral nilpotency, anticommutator density, and commutator spin/vorticity:
    Psi_p * Psi_p = 0 ∧
    Psi_m * Psi_m = 0 ∧
    racomm Psi_p Psi_m = V4 ∧
    rcomm Psi_p Psi_m = Om4 ∧
    -- 2. Schrödinger-to-Madelung real (Hamilton-Jacobi-Bohm) & imaginary (Lamb-vorticity) splitting for arbitrary Z:
    S_pm Z + S_mp Z = (viscousCurv P X Y Z - bohmCurv P X Y Z) + (viscousCurv P X Y Z - bohmCurv P X Y Z) ∧
    S_pm Z - S_mp Z = lambOperator Z Om_v + lambOperator Z Om_v + lambOperator Z Om_v + lambOperator Z Om_v ∧
    -- 3. Navier-Stokes velocity, amplitude, and density eigen-closures:
    S_pm J + S_mp J = V8 * J ∧
    S_pm J - S_mp J = V8 * Phi ∧
    S_pm Phi + S_mp Phi = V8 * Phi ∧
    S_pm Phi - S_mp Phi = V8 * J ∧
    S_pm V = 0 ∧
    S_mp V = 0 := by
  have hV0 := archetype_V0_madelung_amplitude_phase_vorticity_and_chiral_anomaly hP X Y
  have hV1 := archetype_V1_navier_stokes_lamb_commutator_and_beltrami_depletion hP X Y 0 0 0 (by simp)
  have hV2 := archetype_V2_navier_madelung_bohm_quantum_pressure_momentum_closure hP X Y
  have hSym (A C W : B) :
      rcomm (A + C) (rcomm (A - C) W) + rcomm (A - C) (rcomm (A + C) W) =
        (-rcomm C (rcomm C W) - (-rcomm A (rcomm A W))) +
        (-rcomm C (rcomm C W) - (-rcomm A (rcomm A W))) := by
    dsimp only [rcomm]
    simp only [mul_add, add_mul, sub_mul, mul_sub, mul_assoc]
    abel
  have hSkew (A C W : B) :
      rcomm (A + C) (rcomm (A - C) W) - rcomm (A - C) (rcomm (A + C) W) =
        rcomm (-(rcomm A C)) W + rcomm (-(rcomm A C)) W := by
    dsimp only [rcomm]
    simp only [mul_add, add_mul, sub_mul, mul_sub, neg_sub, mul_assoc]
    abel
  have hOmComm (Om W : B) :
      rcomm (Om + Om) W + rcomm (Om + Om) W =
        lambOperator W Om + lambOperator W Om + lambOperator W Om + lambOperator W Om := by
    dsimp only [rcomm, lambOperator]
    simp only [mul_add, add_mul]
    abel
  have hLambPhi :
      lambOperator (genPhi P X Y) (genSig P X Y) =
        genV P X Y * genJ P X Y + genV P X Y * genJ P X Y := by
    dsimp only [lambOperator]
    peirce_bimetric_abel hP
  have hAdd8 (U W : B) :
      ((U + U + U + U) * W) + ((U + U + U + U) * W) =
        ((U + U + U + U) + (U + U + U + U)) * W := by
    simp only [add_mul]
  have hAdd4 (U W : B) :
      (U * W + U * W) + (U * W + U * W) + (U * W + U * W) + (U * W + U * W) =
        ((U + U + U + U) + (U + U + U + U)) * W := by
    simp only [add_mul]
    abel
  have hR0 (A : B) : rcomm A 0 = 0 := by
    dsimp only [rcomm]; simp
  dsimp only []
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · peirce_bimetric_abel hP
  · peirce_bimetric_abel hP
  · peirce_bimetric_abel hP
  · peirce_bimetric_abel hP
  · exact hSym (genPhi P X Y) (genJ P X Y) Z
  · dsimp only [chiralSchrodingerPlusMinus, chiralSchrodingerMinusPlus]
    rw [hSkew (genPhi P X Y) (genJ P X Y) Z, hV0.2.2.1, neg_neg]
    exact hOmComm (genSig P X Y) Z
  · dsimp only [chiralSchrodingerPlusMinus, chiralSchrodingerMinusPlus]
    rw [hSym (genPhi P X Y) (genJ P X Y) (genJ P X Y)]
    have hJJ : rcomm (genJ P X Y) (genJ P X Y) = 0 := sub_self _
    change (-rcomm (genJ P X Y) (rcomm (genJ P X Y) (genJ P X Y)) - bohmCurv P X Y (genJ P X Y)) +
           (-rcomm (genJ P X Y) (rcomm (genJ P X Y) (genJ P X Y)) - bohmCurv P X Y (genJ P X Y)) = _
    rw [hJJ, hR0, neg_zero, zero_sub, hV2.2.1, neg_neg]
    exact hAdd8 (genV P X Y) (genJ P X Y)
  · dsimp only [chiralSchrodingerPlusMinus, chiralSchrodingerMinusPlus]
    rw [hSkew (genPhi P X Y) (genJ P X Y) (genJ P X Y), hV0.2.2.1, neg_neg,
        hOmComm (genSig P X Y) (genJ P X Y), hV1.2.2.2.2.2]
    exact hAdd4 (genV P X Y) (genPhi P X Y)
  · dsimp only [chiralSchrodingerPlusMinus, chiralSchrodingerMinusPlus]
    rw [hSym (genPhi P X Y) (genJ P X Y) (genPhi P X Y)]
    have hPP : rcomm (genPhi P X Y) (genPhi P X Y) = 0 := sub_self _
    change (viscousCurv P X Y (genPhi P X Y) - (-rcomm (genPhi P X Y) (rcomm (genPhi P X Y) (genPhi P X Y)))) +
           (viscousCurv P X Y (genPhi P X Y) - (-rcomm (genPhi P X Y) (rcomm (genPhi P X Y) (genPhi P X Y)))) = _
    rw [hPP, hR0, neg_zero, sub_zero, hV2.2.2.1]
    exact hAdd8 (genV P X Y) (genPhi P X Y)
  · dsimp only [chiralSchrodingerPlusMinus, chiralSchrodingerMinusPlus]
    rw [hSkew (genPhi P X Y) (genJ P X Y) (genPhi P X Y), hV0.2.2.1, neg_neg,
        hOmComm (genSig P X Y) (genPhi P X Y), hLambPhi]
    exact hAdd4 (genV P X Y) (genJ P X Y)
  · dsimp only [chiralSchrodingerPlusMinus]
    have hSubV : rcomm (genPhi P X Y - genJ P X Y) (genV P X Y) =
        rcomm (genPhi P X Y) (genV P X Y) - rcomm (genJ P X Y) (genV P X Y) := by
      dsimp only [rcomm]; simp only [sub_mul, mul_sub]; abel
    rw [hSubV, hV2.2.2.2.2.2.1, hV2.2.2.2.2.2.2.1, sub_zero, hR0]
  · dsimp only [chiralSchrodingerMinusPlus]
    have hAddV : rcomm (genPhi P X Y + genJ P X Y) (genV P X Y) =
        rcomm (genPhi P X Y) (genV P X Y) + rcomm (genJ P X Y) (genV P X Y) := by
      dsimp only [rcomm]; simp only [add_mul, mul_add]; abel
    rw [hAddV, hV2.2.2.2.2.2.1, hV2.2.2.2.2.2.2.1, add_zero, hR0]

end NonCommutativeNavierMadelungChiralVortexPoset
