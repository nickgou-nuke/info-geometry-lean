import Mathlib.Tactic
import InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit
import InfoGeometry.Canonical.ExteriorAlgebraChiralHodgeDiracBlockBridge
import InfoGeometry.Canonical.ChiralExterior3HodgeDiracBlocks

/-!
# Real Krein Chiral Hodge--Dirac Blocks and Hestenes Commutation

This module formalizes the real doubled Krein space carrier
$$\mathcal{K}_{\mathbb{R}} = V_+ \oplus V_- \simeq \mathbb{R}^{n,n}$$
carrying both:
1. A real grading involution $\Gamma$ ($\Gamma^2 = I$) giving the Witt/chiral decomposition $V_\pm = \operatorname{ker}(\Gamma \mp I)$
   with projectors $P_\pm = \frac{1}{2}(I \pm \Gamma)$.
2. An internal real Hestenes complex structure $K$ ($K^2 = -I$).
3. A real odd Hodge--Dirac operator $D = \begin{pmatrix} 0 & D_- \\ D_+ & 0 \end{pmatrix}$ with
   $\{\Gamma, D\} = 0$ and $[K, D] = 0$.

## Key Physical & Mathematical Theorems:
- **Cross-Sheet Chiral Arrows:** $D_+ : V_+ \to V_-$ and $D_- : V_- \to V_+$ with $D_\pm^2 = 0$.
- **Hodge Laplacian Chiral Blocks:** $\Delta = D^2 = \Delta_+ + \Delta_-$ where $\Delta_+ = D_- D_+$ and $\Delta_- = D_+ D_-$.
- **Hestenes-Dirac Hyperbolic/Elliptic Duality:**
  $$D^2 = +\Delta \qquad \text{and} \qquad (K D)^2 = -\Delta.$$
- **Chiral-Hestenes Commutation:** When $[\Gamma, K] = 0$, the Hestenes phase preserves each chiral sheet $K(V_\pm) \subseteq V_\pm$,
  $K P_\pm = P_\pm K$, and $K D_\pm = D_\pm K$.
- **Second Real Complex Structure $J_\chi = K \Gamma$:**
  $$J_\chi^2 = -I, \qquad \{J_\chi, D\} = 0.$$
- **Hestenes Phase Flow Preservation:**
  For $\Phi_K(t) = \cos t I + \sin t K$, we have $[\Phi_K(t), D] = 0$, $[\Phi_K(t), \Gamma] = 0$,
  $[\Phi_K(t), P_\pm] = 0$, and $[\Phi_K(t), D_\pm] = 0$.
- **Sheet Exchange Involution:** $\kappa_{\rm exch}^2 = I$, $\{\kappa_{\rm exch}, \Gamma\} = 0$, exchanging the chiral projectors
  $\kappa_{\rm exch} P_\pm = P_\mp \kappa_{\rm exch}$.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealKreinChiralHodgeDiracBlocks

open InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit
open InfoGeometry.Canonical.ExteriorAlgebraChiralHodgeDiracBlockBridge
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-! ## 1. Hestenes Complex Structure and Dirac Dynamics -/

theorem hestenes_dirac_sq_neg_laplacian {K D : Module.End ℝ M}
    (hK_sq : K * K = -1) (hKD : K * D = D * K) :
    (K * D) * (K * D) = -(D * D) := by
  calc (K * D) * (K * D)
    _ = K * (D * K) * D := by noncomm_ring
    _ = K * (K * D) * D := by rw [← hKD]
    _ = (K * K) * (D * D) := by noncomm_ring
    _ = (-1) * (D * D) := by rw [hK_sq]
    _ = -(D * D) := by rw [neg_one_mul]

/-! ## 2. Chiral Sheet Hestenes Preservation: [Γ, K] = 0 -/

theorem hestenes_commutes_projectorPlus {Γ K : Module.End ℝ M} (hΓK : Γ * K = K * Γ) :
    K * chiralProjectorPlus Γ = chiralProjectorPlus Γ * K := by
  dsimp [chiralProjectorPlus]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply,
    LinearMap.map_smul, LinearMap.map_add, Module.End.mul_apply]
  have h : Γ (K x) = K (Γ x) := by
    simpa only [Module.End.mul_apply] using
      congrArg (fun T : Module.End ℝ M => T x) hΓK
  rw [h]

theorem hestenes_commutes_projectorMinus {Γ K : Module.End ℝ M} (hΓK : Γ * K = K * Γ) :
    K * chiralProjectorMinus Γ = chiralProjectorMinus Γ * K := by
  dsimp [chiralProjectorMinus]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.map_smul, LinearMap.map_sub, Module.End.mul_apply]
  have h : Γ (K x) = K (Γ x) := by
    simpa only [Module.End.mul_apply] using
      congrArg (fun T : Module.End ℝ M => T x) hΓK
  rw [h]

theorem hestenes_commutes_chiralDiracPlus {Γ D K : Module.End ℝ M}
    (hΓ_sq : Γ * Γ = 1) (hodd : Γ * D = -(D * Γ))
    (hΓK : Γ * K = K * Γ) (hKD : K * D = D * K) :
    K * chiralDiracPlus Γ D = chiralDiracPlus Γ D * K := by
  have h1 : chiralDiracPlus Γ D = D * chiralProjectorPlus Γ :=
    chiralDiracPlus_eq_dirac_projPlus hΓ_sq hodd
  have hP : K * chiralProjectorPlus Γ = chiralProjectorPlus Γ * K :=
    hestenes_commutes_projectorPlus hΓK
  rw [h1]
  calc K * (D * chiralProjectorPlus Γ)
    _ = (K * D) * chiralProjectorPlus Γ := by noncomm_ring
    _ = (D * K) * chiralProjectorPlus Γ := by rw [hKD]
    _ = D * (K * chiralProjectorPlus Γ) := by noncomm_ring
    _ = D * (chiralProjectorPlus Γ * K) := by rw [hP]
    _ = (D * chiralProjectorPlus Γ) * K := by noncomm_ring

theorem hestenes_commutes_chiralDiracMinus {Γ D K : Module.End ℝ M}
    (hΓ_sq : Γ * Γ = 1) (hodd : Γ * D = -(D * Γ))
    (hΓK : Γ * K = K * Γ) (hKD : K * D = D * K) :
    K * chiralDiracMinus Γ D = chiralDiracMinus Γ D * K := by
  have h1 : chiralDiracMinus Γ D = D * chiralProjectorMinus Γ :=
    chiralDiracMinus_eq_dirac_projMinus hΓ_sq hodd
  have hP : K * chiralProjectorMinus Γ = chiralProjectorMinus Γ * K :=
    hestenes_commutes_projectorMinus hΓK
  rw [h1]
  calc K * (D * chiralProjectorMinus Γ)
    _ = (K * D) * chiralProjectorMinus Γ := by noncomm_ring
    _ = (D * K) * chiralProjectorMinus Γ := by rw [hKD]
    _ = D * (K * chiralProjectorMinus Γ) := by noncomm_ring
    _ = D * (chiralProjectorMinus Γ * K) := by rw [hP]
    _ = (D * chiralProjectorMinus Γ) * K := by noncomm_ring

/-! ## 3. Second Real Complex Structure J_χ = K Γ -/

def chiralComplexStructure (K Γ : Module.End ℝ M) : Module.End ℝ M := K * Γ

theorem chiralComplexStructure_sq {K Γ : Module.End ℝ M}
    (hK_sq : K * K = -1) (hΓ_sq : Γ * Γ = 1) (hΓK : Γ * K = K * Γ) :
    chiralComplexStructure K Γ * chiralComplexStructure K Γ = -1 := by
  dsimp [chiralComplexStructure]
  calc (K * Γ) * (K * Γ)
    _ = K * (Γ * K) * Γ := by noncomm_ring
    _ = K * (K * Γ) * Γ := by rw [← hΓK]
    _ = (K * K) * (Γ * Γ) := by noncomm_ring
    _ = (-1) * 1 := by rw [hK_sq, hΓ_sq]
    _ = -1 := by rw [mul_one]

theorem chiralComplexStructure_anticomm_dirac {K Γ D : Module.End ℝ M}
    (hodd : Γ * D = -(D * Γ)) (hKD : K * D = D * K) :
    chiralComplexStructure K Γ * D = -(D * chiralComplexStructure K Γ) := by
  dsimp [chiralComplexStructure]
  calc (K * Γ) * D
    _ = K * (Γ * D) := by noncomm_ring
    _ = K * -(D * Γ) := by rw [hodd]
    _ = -(K * (D * Γ)) := by rw [mul_neg]
    _ = -((K * D) * Γ) := by noncomm_ring
    _ = -((D * K) * Γ) := by rw [hKD]
    _ = -(D * (K * Γ)) := by noncomm_ring

/-! ## 4. Hestenes Phase Flow and Chiral Intertwining -/

def hestenesPhaseFlow (K : Module.End ℝ M) (t : ℝ) : Module.End ℝ M :=
  (Real.cos t) • (1 : Module.End ℝ M) + (Real.sin t) • K

theorem hestenesPhaseFlow_commutes_dirac {K D : Module.End ℝ M}
    (hKD : K * D = D * K) (t : ℝ) :
    hestenesPhaseFlow K t * D = D * hestenesPhaseFlow K t := by
  dsimp [hestenesPhaseFlow]
  calc ((Real.cos t) • (1 : Module.End ℝ M) + (Real.sin t) • K) * D
    _ = (Real.cos t) • D + (Real.sin t) • (K * D) := by
      rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc]
    _ = (Real.cos t) • D + (Real.sin t) • (D * K) := by rw [hKD]
    _ = D * ((Real.cos t) • (1 : Module.End ℝ M) + (Real.sin t) • K) := by
      rw [mul_add, mul_smul_comm, mul_one, mul_smul_comm]

theorem hestenesPhaseFlow_commutes_grading {K Γ : Module.End ℝ M}
    (hΓK : Γ * K = K * Γ) (t : ℝ) :
    hestenesPhaseFlow K t * Γ = Γ * hestenesPhaseFlow K t := by
  dsimp [hestenesPhaseFlow]
  calc ((Real.cos t) • (1 : Module.End ℝ M) + (Real.sin t) • K) * Γ
    _ = (Real.cos t) • Γ + (Real.sin t) • (K * Γ) := by
      rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc]
    _ = (Real.cos t) • Γ + (Real.sin t) • (Γ * K) := by rw [← hΓK]
    _ = Γ * ((Real.cos t) • (1 : Module.End ℝ M) + (Real.sin t) • K) := by
      rw [mul_add, mul_smul_comm, mul_one, mul_smul_comm]

theorem hestenesPhaseFlow_commutes_projectorPlus {K Γ : Module.End ℝ M}
    (hΓK : Γ * K = K * Γ) (t : ℝ) :
    hestenesPhaseFlow K t * chiralProjectorPlus Γ =
      chiralProjectorPlus Γ * hestenesPhaseFlow K t := by
  exact hestenes_commutes_projectorPlus (K := hestenesPhaseFlow K t)
    (Γ := Γ) (by
      exact (hestenesPhaseFlow_commutes_grading hΓK t).symm)

theorem hestenesPhaseFlow_commutes_projectorMinus {K Γ : Module.End ℝ M}
    (hΓK : Γ * K = K * Γ) (t : ℝ) :
    hestenesPhaseFlow K t * chiralProjectorMinus Γ =
      chiralProjectorMinus Γ * hestenesPhaseFlow K t := by
  exact hestenes_commutes_projectorMinus (K := hestenesPhaseFlow K t)
    (Γ := Γ) (by
      exact (hestenesPhaseFlow_commutes_grading hΓK t).symm)

theorem hestenesPhaseFlow_commutes_chiralDiracPlus {K Γ D : Module.End ℝ M}
    (hΓ_sq : Γ * Γ = 1) (hodd : Γ * D = -(D * Γ))
    (hΓK : Γ * K = K * Γ) (hKD : K * D = D * K) (t : ℝ) :
    hestenesPhaseFlow K t * chiralDiracPlus Γ D =
      chiralDiracPlus Γ D * hestenesPhaseFlow K t := by
  exact hestenes_commutes_chiralDiracPlus hΓ_sq hodd
    (by exact (hestenesPhaseFlow_commutes_grading hΓK t).symm)
    (hestenesPhaseFlow_commutes_dirac hKD t)

theorem hestenesPhaseFlow_commutes_chiralDiracMinus {K Γ D : Module.End ℝ M}
    (hΓ_sq : Γ * Γ = 1) (hodd : Γ * D = -(D * Γ))
    (hΓK : Γ * K = K * Γ) (hKD : K * D = D * K) (t : ℝ) :
    hestenesPhaseFlow K t * chiralDiracMinus Γ D =
      chiralDiracMinus Γ D * hestenesPhaseFlow K t := by
  exact hestenes_commutes_chiralDiracMinus hΓ_sq hodd
    (by exact (hestenesPhaseFlow_commutes_grading hΓK t).symm)
    (hestenesPhaseFlow_commutes_dirac hKD t)

/-! ## 5. Sheet Exchange Involution κ_exch -/

/-- Sheet exchange involution exchanging V_+ and V_- -/
structure SheetExchangeDatum (Γ : Module.End ℝ M) where
  κ : Module.End ℝ M
  κ_sq : κ * κ = 1
  anticomm : κ * Γ = -(Γ * κ)

theorem sheetExchange_swaps_projectorPlus {Γ : Module.End ℝ M}
    (datum : SheetExchangeDatum Γ) :
    datum.κ * chiralProjectorPlus Γ = chiralProjectorMinus Γ * datum.κ := by
  dsimp [chiralProjectorPlus, chiralProjectorMinus]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply,
    Module.End.one_apply, LinearMap.map_smul, LinearMap.map_add, Module.End.mul_apply]
  have h : datum.κ (Γ x) = - Γ (datum.κ x) := by
    simpa only [Module.End.mul_apply, LinearMap.neg_apply] using
      congrArg (fun T : Module.End ℝ M => T x) datum.anticomm
  rw [h]
  module

theorem sheetExchange_swaps_projectorMinus {Γ : Module.End ℝ M}
    (datum : SheetExchangeDatum Γ) :
    datum.κ * chiralProjectorMinus Γ = chiralProjectorPlus Γ * datum.κ := by
  dsimp [chiralProjectorPlus, chiralProjectorMinus]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply,
    Module.End.one_apply, LinearMap.map_smul, LinearMap.map_sub, Module.End.mul_apply]
  have h : datum.κ (Γ x) = - Γ (datum.κ x) := by
    simpa only [Module.End.mul_apply, LinearMap.neg_apply] using
      congrArg (fun T : Module.End ℝ M => T x) datum.anticomm
  rw [h]
  module

/-! ## 6. Concrete Real Krein Carrier Verification on DoubledExterior3 -/

theorem concrete_chirality3_commutes_hestenesPhase3 :
    concreteChirality3 * hestenesPhase3 = hestenesPhase3 * concreteChirality3 := by
  apply LinearMap.ext
  rintro ⟨a, b⟩
  simp [concreteChirality3, hestenesPhase3, doubledDiagonal]

theorem concrete_hestenes_dirac_sq_neg_laplacian (v : V3) (φ : Module.Dual ℝ V3) :
    (hestenesPhase3 * concreteDirac3 v φ) * (hestenesPhase3 * concreteDirac3 v φ) =
      -(concreteLaplacian3 v φ) := by
  have hK_sq := hestenesPhase3_sq
  have hKD := concreteDirac3_phase v φ
  have hD_sq := concreteDirac3_sq v φ
  rw [hestenes_dirac_sq_neg_laplacian hK_sq hKD, hD_sq]

theorem concrete_hestenes_commutes_chiralDiracPlus (v : V3) (φ : Module.Dual ℝ V3) :
    hestenesPhase3 * concreteChiralDiracPlus3 v φ =
      concreteChiralDiracPlus3 v φ * hestenesPhase3 :=
  hestenes_commutes_chiralDiracPlus concreteChirality3_sq
    (concreteChirality3_odd v φ) concrete_chirality3_commutes_hestenesPhase3
    (concreteDirac3_phase v φ)

theorem concrete_hestenes_commutes_chiralDiracMinus (v : V3) (φ : Module.Dual ℝ V3) :
    hestenesPhase3 * concreteChiralDiracMinus3 v φ =
      concreteChiralDiracMinus3 v φ * hestenesPhase3 :=
  hestenes_commutes_chiralDiracMinus concreteChirality3_sq
    (concreteChirality3_odd v φ) concrete_chirality3_commutes_hestenesPhase3
    (concreteDirac3_phase v φ)

theorem concrete_chiralComplexStructure_sq :
    chiralComplexStructure hestenesPhase3 concreteChirality3 *
        chiralComplexStructure hestenesPhase3 concreteChirality3 = -1 :=
  chiralComplexStructure_sq hestenesPhase3_sq concreteChirality3_sq
    concrete_chirality3_commutes_hestenesPhase3

theorem concrete_chiralComplexStructure_anticomm_dirac (v : V3) (φ : Module.Dual ℝ V3) :
    chiralComplexStructure hestenesPhase3 concreteChirality3 * concreteDirac3 v φ =
      -(concreteDirac3 v φ * chiralComplexStructure hestenesPhase3 concreteChirality3) :=
  chiralComplexStructure_anticomm_dirac (concreteChirality3_odd v φ)
    (concreteDirac3_phase v φ)

end InfoGeometry.Canonical.RealKreinChiralHodgeDiracBlocks
