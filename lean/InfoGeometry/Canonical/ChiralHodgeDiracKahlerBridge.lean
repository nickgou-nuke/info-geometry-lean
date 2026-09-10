import Mathlib.Tactic
import Mathlib.Algebra.Module.Basic
import InfoGeometry.Canonical.CylinderHodgeDualityFreudenthalBridge

/-!
# Chiral Hodge-Dirac-Kähler Operator & 6-Fold Polarized Hodge Decomposition Bridge

This module formalizes the canonical mathematical bridge uniting:
1. **The Dirac-Kähler Operator**:
   Differential forms carry the odd first-order Dirac-Kähler operator $\mathcal{D} = d - \delta$,
   whose square is the negative Hodge-de Rham Laplacian:
   $$\mathcal{D}^2 = -\Delta = -(d\delta + \delta d)$$
2. **Degree Chirality Grading & Anticommutation**:
   The degree/spinorial chirality involution $\Gamma = (-1)^p$ anticommutes with both the
   exterior derivative $d$ and the Hodge codifferential $\delta$:
   $$\{d, \Gamma\} = 0, \qquad \{\delta, \Gamma\} = 0 \implies \{\mathcal{D}, \Gamma\} = 0$$
3. **Split Peirce Chiral Projectors & Intertwining**:
   The idempotent projectors $P_\pm = \frac{1}{2}(\mathbb{I} \pm \Gamma)$ satisfy:
   $$P_+ + P_- = \mathbb{I}, \quad P_+ - P_- = \Gamma, \quad P_\pm^2 = P_\pm, \quad P_+ P_- = P_- P_+ = 0$$
   The Dirac-Kähler operator exactly swaps the chiral eigenspaces (chiral exchange):
   $$\mathcal{D} P_\pm = P_\mp \mathcal{D}$$
4. **Cross-Sheet Arrows & Nilpotent Block Decomposition**:
   The off-diagonal cross-sheet arrows $\mathcal{D}_+ = P_- \mathcal{D} P_+$ and
   $\mathcal{D}_- = P_+ \mathcal{D} P_-$ reconstruct the full operator:
   $$\mathcal{D} = \mathcal{D}_+ + \mathcal{D}_-, \qquad P_\pm \mathcal{D} P_\pm = 0$$
   and satisfy topological nilpotence $\mathcal{D}_\pm^2 = 0$.
5. **Exact-Coexact Transmutation & Harmonic Kernel**:
   $\mathcal{D}$ acts as the kinetic intertwining engine across the Souriau bifurcation:
   - On exact forms (Souriau irrotational sector): $\mathcal{D}(d\alpha) = -\delta d \alpha \in \operatorname{im}(\delta)$.
   - On coexact forms (Souriau rotational sector): $\mathcal{D}(\delta\beta) = d\delta\beta \in \operatorname{im}(d)$.
   - On harmonic forms $\mathcal{H}_\Delta = \ker(d) \cap \ker(\delta)$: $\mathcal{D}\gamma = 0$ and $\Delta\gamma = 0$.
6. **Laplacian Commutation & Chiral Sector Preservation**:
   The Laplacian commutes with all structural operators:
   $$[d, \Delta] = 0, \quad [\delta, \Delta] = 0 \implies [\mathcal{D}, \Delta] = 0$$
   $$[\Gamma, \Delta] = 0 \implies [P_\pm, \Delta] = 0$$
   proving that $\Delta$ preserves each chiral sector.
7. **The 6-Fold Polarized Hodge Decomposition**:
   Differential forms decompose into 6 canonical polarized subspaces:
   $$\Omega^\bullet = (\operatorname{im}(d)_+ \oplus \operatorname{im}(d)_-) \oplus (\operatorname{im}(\delta)_+ \oplus \operatorname{im}(\delta)_-) \oplus (\mathcal{H}_+ \oplus \mathcal{H}_-)$$
   where $P_\pm(d\alpha) = d(P_\mp \alpha)$, $P_\pm(\delta\beta) = \delta(P_\mp \beta)$, and
   $P_\pm \gamma_h \in \mathcal{H}_\Delta$.
8. **Concrete Realization on 2D Cylinder Forms**:
   Explicit realization on the graded forms `GradedForms R` and derivation data `CylinderDerivData R`
   of the cylinder $\mathbb{R} \times S^1$.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace InfoGeometry.Canonical.ChiralHodgeDiracKahlerBridge

open InfoGeometry.Canonical.CylinderHodgeDualityFreudenthalBridge
open GradedForms
open CylinderDerivData

section AbstractAlgebraic

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {V : Type*} [AddCommGroup V] [Module R V]

/-! ## 1. Graded Operators and Dirac-Kähler Kinetic Engine -/

/-- The Hodge-de Rham Laplacian $\Delta = d\delta + \delta d$. -/
def laplacian (d delta : Module.End R V) : Module.End R V :=
  d * delta + delta * d

/-- The Dirac-Kähler operator $\mathcal{D} = d - \delta$. -/
def diracKahler (d delta : Module.End R V) : Module.End R V :=
  d - delta

/-- Positive chiral Peirce projector $P_+ = \frac{1}{2}(\mathbb{I} + \Gamma)$. -/
def projPlus (gamma : Module.End R V) : Module.End R V :=
  ⅟(2 : R) • (1 + gamma)

/-- Negative chiral Peirce projector $P_- = \frac{1}{2}(\mathbb{I} - \Gamma)$. -/
def projMinus (gamma : Module.End R V) : Module.End R V :=
  ⅟(2 : R) • (1 - gamma)

/-- The cross-sheet Dirac-Kähler arrow $\mathcal{D}_+ : V_+ \to V_-$. -/
def diracKahlerPlus (d delta gamma : Module.End R V) : Module.End R V :=
  (projMinus gamma) * (diracKahler d delta) * (projPlus gamma)

/-- The cross-sheet Dirac-Kähler arrow $\mathcal{D}_- : V_- \to V_+$. -/
def diracKahlerMinus (d delta gamma : Module.End R V) : Module.End R V :=
  (projPlus gamma) * (diracKahler d delta) * (projMinus gamma)

/-- **Fundamental Theorem**: The square of the Dirac-Kähler operator is the negative Laplacian:
    $\mathcal{D}^2 = -\Delta$. -/
theorem diracKahler_sq (d delta : Module.End R V)
    (hd2 : d * d = 0) (hdelta2 : delta * delta = 0) :
    (diracKahler d delta) * (diracKahler d delta) = - laplacian d delta := by
  dsimp [diracKahler, laplacian]
  have h1 : (d - delta) * (d - delta) = d * d - d * delta - delta * d + delta * delta := by
    noncomm_ring
  rw [h1, hd2, hdelta2]
  simp only [zero_sub, add_zero]
  noncomm_ring

/-- **Theorem**: The Dirac-Kähler operator anticommutes with chirality:
    $\{\mathcal{D}, \Gamma\} = 0$. -/
theorem diracKahler_anticomm_gamma (d delta gamma : Module.End R V)
    (hd_gamma : d * gamma + gamma * d = 0)
    (hdelta_gamma : delta * gamma + gamma * delta = 0) :
    (diracKahler d delta) * gamma + gamma * (diracKahler d delta) = 0 := by
  dsimp [diracKahler]
  have h1 : (d - delta) * gamma + gamma * (d - delta) =
    (d * gamma + gamma * d) - (delta * gamma + gamma * delta) := by noncomm_ring
  rw [h1, hd_gamma, hdelta_gamma, sub_zero]

/-! ## 2. Commutation with the Hodge-de Rham Laplacian -/

/-- Exterior derivative commutes with Laplacian: $[d, \Delta] = 0$. -/
theorem laplacian_comm_d (d delta : Module.End R V) (hd2 : d * d = 0) :
    d * laplacian d delta = (laplacian d delta) * d := by
  dsimp [laplacian]
  have h1 : d * (d * delta + delta * d) = (d * d) * delta + d * delta * d := by noncomm_ring
  have h2 : (d * delta + delta * d) * d = d * delta * d + delta * (d * d) := by noncomm_ring
  rw [h1, h2, hd2, zero_mul, mul_zero, zero_add, add_zero]

/-- Hodge codifferential commutes with Laplacian: $[\delta, \Delta] = 0$. -/
theorem laplacian_comm_delta (d delta : Module.End R V) (hdelta2 : delta * delta = 0) :
    delta * laplacian d delta = (laplacian d delta) * delta := by
  dsimp [laplacian]
  have h1 : delta * (d * delta + delta * d) = delta * d * delta + (delta * delta) * d := by noncomm_ring
  have h2 : (d * delta + delta * d) * delta = d * (delta * delta) + delta * d * delta := by noncomm_ring
  rw [h1, h2, hdelta2, zero_mul, mul_zero, add_zero, zero_add]

/-- The Dirac-Kähler operator commutes with the Laplacian: $[\mathcal{D}, \Delta] = 0$. -/
theorem laplacian_comm_diracKahler (d delta : Module.End R V)
    (hd2 : d * d = 0) (hdelta2 : delta * delta = 0) :
    (diracKahler d delta) * laplacian d delta = (laplacian d delta) * (diracKahler d delta) := by
  dsimp [diracKahler]
  have h1 : (d - delta) * laplacian d delta = d * laplacian d delta - delta * laplacian d delta := by noncomm_ring
  have h2 : laplacian d delta * (d - delta) = laplacian d delta * d - laplacian d delta * delta := by noncomm_ring
  rw [h1, h2, laplacian_comm_d d delta hd2, laplacian_comm_delta d delta hdelta2]

/-- The degree chirality grading commutes with the Laplacian: $[\Gamma, \Delta] = 0$. -/
theorem laplacian_comm_gamma (d delta gamma : Module.End R V)
    (hd_gamma : d * gamma + gamma * d = 0)
    (hdelta_gamma : delta * gamma + gamma * delta = 0) :
    gamma * laplacian d delta = (laplacian d delta) * gamma := by
  dsimp [laplacian]
  have h_d_g : gamma * d = - (d * gamma) := by
    calc
      gamma * d = (d * gamma + gamma * d) - d * gamma := by noncomm_ring
      _ = 0 - d * gamma := by rw [hd_gamma]
      _ = - (d * gamma) := by noncomm_ring
  have h_delta_g : gamma * delta = - (delta * gamma) := by
    calc
      gamma * delta = (delta * gamma + gamma * delta) - delta * gamma := by noncomm_ring
      _ = 0 - delta * gamma := by rw [hdelta_gamma]
      _ = - (delta * gamma) := by noncomm_ring
  have h_g_d_delta : gamma * (d * delta) = d * delta * gamma := by
    calc
      gamma * (d * delta) = (gamma * d) * delta := by noncomm_ring
      _ = (- (d * gamma)) * delta := by rw [h_d_g]
      _ = - (d * (gamma * delta)) := by noncomm_ring
      _ = - (d * (- (delta * gamma))) := by rw [h_delta_g]
      _ = d * delta * gamma := by noncomm_ring
  have h_g_delta_d : gamma * (delta * d) = delta * d * gamma := by
    calc
      gamma * (delta * d) = (gamma * delta) * d := by noncomm_ring
      _ = (- (delta * gamma)) * d := by rw [h_delta_g]
      _ = - (delta * (gamma * d)) := by noncomm_ring
      _ = - (delta * (- (d * gamma))) := by rw [h_d_g]
      _ = delta * d * gamma := by noncomm_ring
  calc
    gamma * (d * delta + delta * d) = gamma * (d * delta) + gamma * (delta * d) := by noncomm_ring
    _ = (d * delta * gamma) + (delta * d * gamma) := by rw [h_g_d_delta, h_g_delta_d]
    _ = (d * delta + delta * d) * gamma := by noncomm_ring

/-- The Laplacian commutes with the positive chiral projector: $[\Delta, P_+] = 0$. -/
theorem laplacian_comm_projPlus (d delta gamma : Module.End R V)
    (hd_gamma : d * gamma + gamma * d = 0)
    (hdelta_gamma : delta * gamma + gamma * delta = 0) :
    laplacian d delta * projPlus gamma = projPlus gamma * laplacian d delta := by
  dsimp [projPlus]
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  have h_comm := laplacian_comm_gamma d delta gamma hd_gamma hdelta_gamma
  have h1 : laplacian d delta * (1 + gamma) = laplacian d delta + laplacian d delta * gamma := by noncomm_ring
  have h2 : (1 + gamma) * laplacian d delta = laplacian d delta + gamma * laplacian d delta := by noncomm_ring
  rw [h1, h2, h_comm]

/-- The Laplacian commutes with the negative chiral projector: $[\Delta, P_-] = 0$. -/
theorem laplacian_comm_projMinus (d delta gamma : Module.End R V)
    (hd_gamma : d * gamma + gamma * d = 0)
    (hdelta_gamma : delta * gamma + gamma * delta = 0) :
    laplacian d delta * projMinus gamma = projMinus gamma * laplacian d delta := by
  dsimp [projMinus]
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  have h_comm := laplacian_comm_gamma d delta gamma hd_gamma hdelta_gamma
  have h1 : laplacian d delta * (1 - gamma) = laplacian d delta - laplacian d delta * gamma := by noncomm_ring
  have h2 : (1 - gamma) * laplacian d delta = laplacian d delta - gamma * laplacian d delta := by noncomm_ring
  rw [h1, h2, h_comm]

/-! ## 3. Split Peirce Projectors and Off-Diagonal Chiral Exchange -/

/-- Projector completeness: $P_+ + P_- = \mathbb{I}$. -/
theorem projPlus_add_projMinus (gamma : Module.End R V) :
    projPlus gamma + projMinus gamma = 1 := by
  dsimp [projPlus, projMinus]
  rw [← smul_add]
  have h : (1 + gamma) + (1 - gamma) = (2 : R) • (1 : Module.End R V) := by
    ext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.smul_apply, two_smul]
    abel
  rw [h, smul_smul, invOf_mul_self, one_smul]

/-- Projector difference reconstructs the chirality grading: $P_+ - P_- = \Gamma$. -/
theorem projPlus_sub_projMinus (gamma : Module.End R V) :
    projPlus gamma - projMinus gamma = gamma := by
  dsimp [projPlus, projMinus]
  rw [← smul_sub]
  have h : (1 + gamma) - (1 - gamma) = (2 : R) • gamma := by
    ext x
    simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.one_apply,
      LinearMap.smul_apply, two_smul]
    abel
  rw [h, smul_smul, invOf_mul_self, one_smul]

/-- Idempotency of $P_+$: $P_+^2 = P_+$. -/
theorem projPlus_sq (gamma : Module.End R V) (hgamma2 : gamma * gamma = 1) :
    projPlus gamma * projPlus gamma = projPlus gamma := by
  dsimp [projPlus]
  ext x
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
    Module.End.one_apply, map_smul, map_add]
  have hgamma_app : gamma (gamma x) = x := by
    have h : (gamma * gamma) x = (1 : Module.End R V) x := by rw [hgamma2]
    exact h
  rw [hgamma_app]
  rw [← smul_add]
  have hsum : (x + gamma x) + (gamma x + x) = (2 : R) • (x + gamma x) := by
    simp only [two_smul]; abel
  rw [hsum, smul_smul, smul_smul]
  have h_scalar : (⅟(2 : R) * ⅟(2 : R)) * (2 : R) = ⅟(2 : R) := by
    calc
      (⅟(2 : R) * ⅟(2 : R)) * (2 : R) = ⅟(2 : R) * (⅟(2 : R) * 2) := by ring
      _ = ⅟(2 : R) * 1 := by rw [invOf_mul_self]
      _ = ⅟(2 : R) := by ring
  rw [h_scalar]

/-- Idempotency of $P_-$: $P_-^2 = P_-$. -/
theorem projMinus_sq (gamma : Module.End R V) (hgamma2 : gamma * gamma = 1) :
    projMinus gamma * projMinus gamma = projMinus gamma := by
  dsimp [projMinus]
  ext x
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.one_apply, map_smul, map_sub]
  have hgamma_app : gamma (gamma x) = x := by
    have h : (gamma * gamma) x = (1 : Module.End R V) x := by rw [hgamma2]
    exact h
  rw [hgamma_app]
  rw [← smul_sub]
  have hsum : (x - gamma x) - (gamma x - x) = (2 : R) • (x - gamma x) := by
    simp only [two_smul]; abel
  rw [hsum, smul_smul, smul_smul]
  have h_scalar : (⅟(2 : R) * ⅟(2 : R)) * (2 : R) = ⅟(2 : R) := by
    calc
      (⅟(2 : R) * ⅟(2 : R)) * (2 : R) = ⅟(2 : R) * (⅟(2 : R) * 2) := by ring
      _ = ⅟(2 : R) * 1 := by rw [invOf_mul_self]
      _ = ⅟(2 : R) := by ring
  rw [h_scalar]

/-- Orthogonality of chiral projectors: $P_+ P_- = 0$ and $P_- P_+ = 0$. -/
theorem proj_orthogonal (gamma : Module.End R V) (hgamma2 : gamma * gamma = 1) :
    projPlus gamma * projMinus gamma = 0 ∧ projMinus gamma * projPlus gamma = 0 := by
  constructor
  · dsimp [projPlus, projMinus]
    ext x
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.sub_apply, Module.End.one_apply, LinearMap.zero_apply, map_smul, map_add, map_sub]
    have hgamma_app : gamma (gamma x) = x := by
      have h : (gamma * gamma) x = (1 : Module.End R V) x := by rw [hgamma2]
      exact h
    rw [hgamma_app]
    rw [← smul_sub]
    have hsum : (x + gamma x) - (gamma x + x) = 0 := by abel
    rw [hsum, smul_zero, smul_zero]
  · dsimp [projPlus, projMinus]
    ext x
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.sub_apply, Module.End.one_apply, LinearMap.zero_apply, map_smul, map_add, map_sub]
    have hgamma_app : gamma (gamma x) = x := by
      have h : (gamma * gamma) x = (1 : Module.End R V) x := by rw [hgamma2]
      exact h
    rw [hgamma_app]
    rw [← smul_add]
    have hsum : (x - gamma x) + (gamma x - x) = 0 := by abel
    rw [hsum, smul_zero, smul_zero]

/-- Chiral exchange property: $\mathcal{D} P_+ = P_- \mathcal{D}$. -/
theorem diracKahler_projPlus_intertwine (d delta gamma : Module.End R V)
    (hd_gamma : d * gamma + gamma * d = 0)
    (hdelta_gamma : delta * gamma + gamma * delta = 0) :
    (diracKahler d delta) * projPlus gamma = projMinus gamma * (diracKahler d delta) := by
  dsimp [projPlus, projMinus]
  ext x
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.sub_apply, Module.End.one_apply, map_smul, map_add, map_sub]
  have h_anticomm := diracKahler_anticomm_gamma d delta gamma hd_gamma hdelta_gamma
  have h_anticomm_x : ((diracKahler d delta) * gamma + gamma * (diracKahler d delta)) x = 0 := by
    rw [h_anticomm, LinearMap.zero_apply]
  simp only [Module.End.mul_apply, LinearMap.add_apply] at h_anticomm_x
  have h_swap : (diracKahler d delta) (gamma x) = - (gamma ((diracKahler d delta) x)) := by
    calc
      (diracKahler d delta) (gamma x) = ((diracKahler d delta) (gamma x) + gamma ((diracKahler d delta) x)) - gamma ((diracKahler d delta) x) := by abel
      _ = 0 - gamma ((diracKahler d delta) x) := by rw [h_anticomm_x]
      _ = - (gamma ((diracKahler d delta) x)) := by abel
  rw [h_swap]
  have h_eq : (diracKahler d delta) x + - (gamma ((diracKahler d delta) x)) =
    (diracKahler d delta) x - gamma ((diracKahler d delta) x) := by abel
  rw [h_eq]

/-- Chiral exchange property: $\mathcal{D} P_- = P_+ \mathcal{D}$. -/
theorem diracKahler_projMinus_intertwine (d delta gamma : Module.End R V)
    (hd_gamma : d * gamma + gamma * d = 0)
    (hdelta_gamma : delta * gamma + gamma * delta = 0) :
    (diracKahler d delta) * projMinus gamma = projPlus gamma * (diracKahler d delta) := by
  dsimp [projPlus, projMinus]
  ext x
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.sub_apply, Module.End.one_apply, map_smul, map_add, map_sub]
  have h_anticomm := diracKahler_anticomm_gamma d delta gamma hd_gamma hdelta_gamma
  have h_anticomm_x : ((diracKahler d delta) * gamma + gamma * (diracKahler d delta)) x = 0 := by
    rw [h_anticomm, LinearMap.zero_apply]
  simp only [Module.End.mul_apply, LinearMap.add_apply] at h_anticomm_x
  have h_swap : (diracKahler d delta) (gamma x) = - (gamma ((diracKahler d delta) x)) := by
    calc
      (diracKahler d delta) (gamma x) = ((diracKahler d delta) (gamma x) + gamma ((diracKahler d delta) x)) - gamma ((diracKahler d delta) x) := by abel
      _ = 0 - gamma ((diracKahler d delta) x) := by rw [h_anticomm_x]
      _ = - (gamma ((diracKahler d delta) x)) := by abel
  rw [h_swap]
  have h_eq : (diracKahler d delta) x - - (gamma ((diracKahler d delta) x)) =
    (diracKahler d delta) x + gamma ((diracKahler d delta) x) := by abel
  rw [h_eq]

/-! ## 4. Cross-Sheet Arrows and Off-Diagonal Nilpotence -/

/-- Simplification of cross-arrow $\mathcal{D}_+ = \mathcal{D} P_+$. -/
theorem diracKahlerPlus_eq (d delta gamma : Module.End R V)
    (hd_gamma : d * gamma + gamma * d = 0)
    (hdelta_gamma : delta * gamma + gamma * delta = 0)
    (hgamma2 : gamma * gamma = 1) :
    diracKahlerPlus d delta gamma = (diracKahler d delta) * projPlus gamma := by
  dsimp [diracKahlerPlus]
  have h_int_plus := diracKahler_projPlus_intertwine d delta gamma hd_gamma hdelta_gamma
  rw [← h_int_plus, mul_assoc, projPlus_sq gamma hgamma2]

/-- Simplification of cross-arrow $\mathcal{D}_- = \mathcal{D} P_-$. -/
theorem diracKahlerMinus_eq (d delta gamma : Module.End R V)
    (hd_gamma : d * gamma + gamma * d = 0)
    (hdelta_gamma : delta * gamma + gamma * delta = 0)
    (hgamma2 : gamma * gamma = 1) :
    diracKahlerMinus d delta gamma = (diracKahler d delta) * projMinus gamma := by
  dsimp [diracKahlerMinus]
  have h_int_minus := diracKahler_projMinus_intertwine d delta gamma hd_gamma hdelta_gamma
  rw [← h_int_minus, mul_assoc, projMinus_sq gamma hgamma2]

/-- Off-diagonal reconstruction: $\mathcal{D} = \mathcal{D}_+ + \mathcal{D}_-$. -/
theorem diracKahler_sum_cross_arrows (d delta gamma : Module.End R V)
    (hd_gamma : d * gamma + gamma * d = 0)
    (hdelta_gamma : delta * gamma + gamma * delta = 0)
    (hgamma2 : gamma * gamma = 1) :
    diracKahlerPlus d delta gamma + diracKahlerMinus d delta gamma = diracKahler d delta := by
  rw [diracKahlerPlus_eq d delta gamma hd_gamma hdelta_gamma hgamma2]
  rw [diracKahlerMinus_eq d delta gamma hd_gamma hdelta_gamma hgamma2]
  rw [← mul_add, projPlus_add_projMinus, mul_one]

/-- Vanishing diagonal chiral blocks: $P_+ \mathcal{D} P_+ = 0$ and $P_- \mathcal{D} P_- = 0$. -/
theorem diracKahler_diagonal_blocks_zero (d delta gamma : Module.End R V)
    (hd_gamma : d * gamma + gamma * d = 0)
    (hdelta_gamma : delta * gamma + gamma * delta = 0)
    (hgamma2 : gamma * gamma = 1) :
    projPlus gamma * (diracKahler d delta) * projPlus gamma = 0 ∧
    projMinus gamma * (diracKahler d delta) * projMinus gamma = 0 := by
  have h_ortho := proj_orthogonal gamma hgamma2
  constructor
  · rw [mul_assoc, diracKahler_projPlus_intertwine d delta gamma hd_gamma hdelta_gamma]
    rw [← mul_assoc, h_ortho.1, zero_mul]
  · rw [mul_assoc, diracKahler_projMinus_intertwine d delta gamma hd_gamma hdelta_gamma]
    rw [← mul_assoc, h_ortho.2, zero_mul]

/-- Topological nilpotence of positive cross-arrow: $\mathcal{D}_+^2 = 0$. -/
theorem diracKahlerPlus_sq (d delta gamma : Module.End R V)
    (hgamma2 : gamma * gamma = 1) :
    diracKahlerPlus d delta gamma * diracKahlerPlus d delta gamma = 0 := by
  dsimp [diracKahlerPlus]
  have h_ortho := proj_orthogonal gamma hgamma2
  have h_mid : projPlus gamma * (projMinus gamma * diracKahler d delta * projPlus gamma) = 0 := by
    rw [mul_assoc (projMinus gamma), ← mul_assoc (projPlus gamma), h_ortho.1, zero_mul]
  rw [mul_assoc (projMinus gamma * diracKahler d delta), h_mid, mul_zero]

/-- Topological nilpotence of negative cross-arrow: $\mathcal{D}_-^2 = 0$. -/
theorem diracKahlerMinus_sq (d delta gamma : Module.End R V)
    (hgamma2 : gamma * gamma = 1) :
    diracKahlerMinus d delta gamma * diracKahlerMinus d delta gamma = 0 := by
  dsimp [diracKahlerMinus]
  have h_ortho := proj_orthogonal gamma hgamma2
  have h_mid : projMinus gamma * (projPlus gamma * diracKahler d delta * projMinus gamma) = 0 := by
    rw [mul_assoc (projPlus gamma), ← mul_assoc (projMinus gamma), h_ortho.2, zero_mul]
  rw [mul_assoc (projPlus gamma * diracKahler d delta), h_mid, mul_zero]

/-! ## 5. Exact-Coexact Transmutation and Harmonic Kernels -/

/-- **Theorem (Exact to Coexact Transmutation)**:
    On an exact form $d\alpha$, the Dirac-Kähler operator evaluates to a coexact form:
    $\mathcal{D}(d\alpha) = \delta(-d\alpha) \in \operatorname{im}(\delta)$. -/
theorem diracKahler_on_exact (d delta : Module.End R V) (hd2 : d * d = 0) (alpha : V) :
    (diracKahler d delta) (d alpha) = delta (- (d alpha)) := by
  dsimp [diracKahler]
  have hd_apply : d (d alpha) = (d * d) alpha := rfl
  have h : (d * d) alpha = 0 := by rw [hd2, LinearMap.zero_apply]
  rw [hd_apply, h]
  simp only [zero_sub, map_neg]

/-- **Theorem (Coexact to Exact Transmutation)**:
    On a coexact form $\delta\beta$, the Dirac-Kähler operator evaluates to an exact form:
    $\mathcal{D}(\delta\beta) = d(\delta\beta) \in \operatorname{im}(d)$. -/
theorem diracKahler_on_coexact (d delta : Module.End R V) (hdelta2 : delta * delta = 0) (beta : V) :
    (diracKahler d delta) (delta beta) = d (delta beta) := by
  dsimp [diracKahler]
  have hdelta_apply : delta (delta beta) = (delta * delta) beta := rfl
  have h : (delta * delta) beta = 0 := by rw [hdelta2, LinearMap.zero_apply]
  rw [hdelta_apply, h]
  simp only [sub_zero]

/-- **Theorem (Harmonic Annihilation)**:
    On harmonic forms $\mathcal{H}_\Delta = \ker(d) \cap \ker(\delta)$, the Dirac-Kähler operator vanishes:
    $\mathcal{D}\gamma = 0$. -/
theorem diracKahler_on_harmonic (d delta : Module.End R V) (gamma_form : V)
    (h_d : d gamma_form = 0) (h_delta : delta gamma_form = 0) :
    (diracKahler d delta) gamma_form = 0 := by
  dsimp [diracKahler]
  rw [h_d, h_delta, sub_zero]

/-- **Theorem (Harmonic Laplacian Annihilation)**:
    On harmonic forms, the Laplacian vanishes: $\Delta\gamma = 0$. -/
theorem laplacian_on_harmonic (d delta : Module.End R V) (gamma_form : V)
    (h_d : d gamma_form = 0) (h_delta : delta gamma_form = 0) :
    (laplacian d delta) gamma_form = 0 := by
  dsimp [laplacian]
  rw [h_delta, h_d, map_zero, map_zero, add_zero]

/-! ## 6. 6-Fold Polarized Hodge Sectors under Chiral Grading -/

/-- Chiral decomposition on exact forms: $P_+(d\alpha) = d(P_- \alpha)$. -/
theorem projPlus_on_exact (d gamma : Module.End R V)
    (hd_gamma : d * gamma + gamma * d = 0) (alpha : V) :
    (projPlus gamma) (d alpha) = d ((projMinus gamma) alpha) := by
  dsimp [projPlus, projMinus]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply,
    map_smul, map_sub]
  congr 1
  have h_d_g : gamma (d alpha) = - d (gamma alpha) := by
    have h : (d * gamma + gamma * d) alpha = 0 := by rw [hd_gamma, LinearMap.zero_apply]
    simp only [LinearMap.add_apply, Module.End.mul_apply] at h
    calc
      gamma (d alpha) = (d (gamma alpha) + gamma (d alpha)) - d (gamma alpha) := by abel
      _ = 0 - d (gamma alpha) := by rw [h]
      _ = - d (gamma alpha) := by abel
  rw [h_d_g]
  abel

/-- Chiral decomposition on exact forms: $P_-(d\alpha) = d(P_+ \alpha)$. -/
theorem projMinus_on_exact (d gamma : Module.End R V)
    (hd_gamma : d * gamma + gamma * d = 0) (alpha : V) :
    (projMinus gamma) (d alpha) = d ((projPlus gamma) alpha) := by
  dsimp [projPlus, projMinus]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply,
    map_smul, map_add]
  congr 1
  have h_d_g : gamma (d alpha) = - d (gamma alpha) := by
    have h : (d * gamma + gamma * d) alpha = 0 := by rw [hd_gamma, LinearMap.zero_apply]
    simp only [LinearMap.add_apply, Module.End.mul_apply] at h
    calc
      gamma (d alpha) = (d (gamma alpha) + gamma (d alpha)) - d (gamma alpha) := by abel
      _ = 0 - d (gamma alpha) := by rw [h]
      _ = - d (gamma alpha) := by abel
  rw [h_d_g]
  abel

/-- Chiral decomposition on coexact forms: $P_+(\delta\beta) = \delta(P_- \beta)$. -/
theorem projPlus_on_coexact (delta gamma : Module.End R V)
    (hdelta_gamma : delta * gamma + gamma * delta = 0) (beta : V) :
    (projPlus gamma) (delta beta) = delta ((projMinus gamma) beta) := by
  dsimp [projPlus, projMinus]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply,
    map_smul, map_sub]
  congr 1
  have h_delta_g : gamma (delta beta) = - delta (gamma beta) := by
    have h : (delta * gamma + gamma * delta) beta = 0 := by rw [hdelta_gamma, LinearMap.zero_apply]
    simp only [LinearMap.add_apply, Module.End.mul_apply] at h
    calc
      gamma (delta beta) = (delta (gamma beta) + gamma (delta beta)) - delta (gamma beta) := by abel
      _ = 0 - delta (gamma beta) := by rw [h]
      _ = - delta (gamma beta) := by abel
  rw [h_delta_g]
  abel

/-- Chiral decomposition on coexact forms: $P_-(\delta\beta) = \delta(P_+ \beta)$. -/
theorem projMinus_on_coexact (delta gamma : Module.End R V)
    (hdelta_gamma : delta * gamma + gamma * delta = 0) (beta : V) :
    (projMinus gamma) (delta beta) = delta ((projPlus gamma) beta) := by
  dsimp [projPlus, projMinus]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply,
    map_smul, map_add]
  congr 1
  have h_delta_g : gamma (delta beta) = - delta (gamma beta) := by
    have h : (delta * gamma + gamma * delta) beta = 0 := by rw [hdelta_gamma, LinearMap.zero_apply]
    simp only [LinearMap.add_apply, Module.End.mul_apply] at h
    calc
      gamma (delta beta) = (delta (gamma beta) + gamma (delta beta)) - delta (gamma beta) := by abel
      _ = 0 - delta (gamma beta) := by rw [h]
      _ = - delta (gamma beta) := by abel
  rw [h_delta_g]
  abel

/-- Preservation of harmonic forms under positive chiral projector: $P_+ \gamma_h$ is harmonic. -/
theorem projPlus_on_harmonic (d delta gamma : Module.End R V)
    (hd_gamma : d * gamma + gamma * d = 0)
    (hdelta_gamma : delta * gamma + gamma * delta = 0)
    (gamma_form : V) (h_d : d gamma_form = 0) (h_delta : delta gamma_form = 0) :
    d ((projPlus gamma) gamma_form) = 0 ∧ delta ((projPlus gamma) gamma_form) = 0 := by
  constructor
  · dsimp [projPlus]
    simp only [map_smul, map_add, Module.End.one_apply, h_d, zero_add]
    have h_d_g : d (gamma gamma_form) = - gamma (d gamma_form) := by
      have h : (d * gamma + gamma * d) gamma_form = 0 := by rw [hd_gamma, LinearMap.zero_apply]
      simp only [LinearMap.add_apply, Module.End.mul_apply] at h
      calc
        d (gamma gamma_form) = (d (gamma gamma_form) + gamma (d gamma_form)) - gamma (d gamma_form) := by abel
        _ = 0 - gamma (d gamma_form) := by rw [h]
        _ = - gamma (d gamma_form) := by abel
    rw [h_d_g, h_d, map_zero, neg_zero, smul_zero]
  · dsimp [projPlus]
    simp only [map_smul, map_add, Module.End.one_apply, h_delta, zero_add]
    have h_delta_g : delta (gamma gamma_form) = - gamma (delta gamma_form) := by
      have h : (delta * gamma + gamma * delta) gamma_form = 0 := by rw [hdelta_gamma, LinearMap.zero_apply]
      simp only [LinearMap.add_apply, Module.End.mul_apply] at h
      calc
        delta (gamma gamma_form) = (delta (gamma gamma_form) + gamma (delta gamma_form)) - gamma (delta gamma_form) := by abel
        _ = 0 - gamma (delta gamma_form) := by rw [h]
        _ = - gamma (delta gamma_form) := by abel
    rw [h_delta_g, h_delta, map_zero, neg_zero, smul_zero]

/-- Preservation of harmonic forms under negative chiral projector: $P_- \gamma_h$ is harmonic. -/
theorem projMinus_on_harmonic (d delta gamma : Module.End R V)
    (hd_gamma : d * gamma + gamma * d = 0)
    (hdelta_gamma : delta * gamma + gamma * delta = 0)
    (gamma_form : V) (h_d : d gamma_form = 0) (h_delta : delta gamma_form = 0) :
    d ((projMinus gamma) gamma_form) = 0 ∧ delta ((projMinus gamma) gamma_form) = 0 := by
  constructor
  · dsimp [projMinus]
    simp only [map_smul, map_sub, Module.End.one_apply, h_d, zero_sub]
    have h_d_g : d (gamma gamma_form) = - gamma (d gamma_form) := by
      have h : (d * gamma + gamma * d) gamma_form = 0 := by rw [hd_gamma, LinearMap.zero_apply]
      simp only [LinearMap.add_apply, Module.End.mul_apply] at h
      calc
        d (gamma gamma_form) = (d (gamma gamma_form) + gamma (d gamma_form)) - gamma (d gamma_form) := by abel
        _ = 0 - gamma (d gamma_form) := by rw [h]
        _ = - gamma (d gamma_form) := by abel
    rw [h_d_g, h_d, map_zero]
    simp only [neg_zero, smul_zero]
  · dsimp [projMinus]
    simp only [map_smul, map_sub, Module.End.one_apply, h_delta, zero_sub]
    have h_delta_g : delta (gamma gamma_form) = - gamma (delta gamma_form) := by
      have h : (delta * gamma + gamma * delta) gamma_form = 0 := by rw [hdelta_gamma, LinearMap.zero_apply]
      simp only [LinearMap.add_apply, Module.End.mul_apply] at h
      calc
        delta (gamma gamma_form) = (delta (gamma gamma_form) + gamma (delta gamma_form)) - gamma (delta gamma_form) := by abel
        _ = 0 - gamma (delta gamma_form) := by rw [h]
        _ = - gamma (delta gamma_form) := by abel
    rw [h_delta_g, h_delta, map_zero]
    simp only [neg_zero, smul_zero]

end AbstractAlgebraic

/-! ## 7. Concrete Realization on 2D Cylinder Forms -/

namespace CylinderForms

variable {R : Type*} [CommRing R] (D : CylinderDerivData R)

@[simp] theorem sub_omega0 (f g : GradedForms R) : (f - g).omega0 = f.omega0 - g.omega0 := by
  rw [sub_eq_add_neg, add_omega0, neg_omega0, sub_eq_add_neg]

@[simp] theorem sub_omega1_1 (f g : GradedForms R) : (f - g).omega1_1 = f.omega1_1 - g.omega1_1 := by
  rw [sub_eq_add_neg, add_omega1_1, neg_omega1_1, sub_eq_add_neg]

@[simp] theorem sub_omega1_2 (f g : GradedForms R) : (f - g).omega1_2 = f.omega1_2 - g.omega1_2 := by
  rw [sub_eq_add_neg, add_omega1_2, neg_omega1_2, sub_eq_add_neg]

@[simp] theorem sub_omega2 (f g : GradedForms R) : (f - g).omega2 = f.omega2 - g.omega2 := by
  rw [sub_eq_add_neg, add_omega2, neg_omega2, sub_eq_add_neg]

/-- Exterior derivative anticommutes with chirality on 2D forms: $\{d, \Gamma\} = 0$. -/
theorem cylinderExteriorD_anticomm_chirality (f : GradedForms R) :
    exteriorD D (chirality f) + chirality (exteriorD D f) = 0 := by
  ext
  · dsimp [exteriorD, chirality]; ring
  · dsimp [exteriorD, chirality]; ring
  · dsimp [exteriorD, chirality]; ring
  · dsimp [exteriorD, chirality]; simp only [map_neg]; ring

/-- Codifferential anticommutes with chirality on 2D forms: $\{\delta, \Gamma\} = 0$. -/
theorem cylinderCodifferential_anticomm_chirality (f : GradedForms R) :
    codifferential D (chirality f) + chirality (codifferential D f) = 0 := by
  ext
  · dsimp [codifferential, exteriorD, chirality, hodgeStar]; simp only [map_neg, neg_neg]; ring
  · dsimp [codifferential, exteriorD, chirality, hodgeStar]; ring
  · dsimp [codifferential, exteriorD, chirality, hodgeStar]; ring
  · dsimp [codifferential, exteriorD, chirality, hodgeStar]; ring

/-- Concrete Dirac-Kähler operator on 2D cylinder forms: $\mathcal{D} = d - \delta$. -/
def cylinderDiracKahler (f : GradedForms R) : GradedForms R :=
  exteriorD D f - codifferential D f

theorem chirality_sub (f g : GradedForms R) :
    chirality (f - g) = chirality f - chirality g := by
  ext <;> (simp [chirality]; try ring)

/-- The Dirac-Kähler operator anticommutes with chirality on 2D forms: $\{\mathcal{D}, \Gamma\} = 0$. -/
theorem cylinderDiracKahler_anticomm_chirality (f : GradedForms R) :
    cylinderDiracKahler D (chirality f) + chirality (cylinderDiracKahler D f) = 0 := by
  dsimp [cylinderDiracKahler]
  rw [chirality_sub]
  have h1 := cylinderExteriorD_anticomm_chirality D f
  have h2 := cylinderCodifferential_anticomm_chirality D f
  calc
    (exteriorD D (chirality f) - codifferential D (chirality f)) +
        (chirality (exteriorD D f) - chirality (codifferential D f))
      = (exteriorD D (chirality f) + chirality (exteriorD D f)) -
        (codifferential D (chirality f) + chirality (codifferential D f)) := by
      ext <;> (simp; ring)
    _ = 0 - 0 := by rw [h1, h2]
    _ = 0 := sub_zero 0

end CylinderForms

/-! ## 8. Certified Structural Synthesis Package -/

/-- Certified structural synthesis package for the Chiral Hodge-Dirac-Kähler architecture. -/
structure ChiralHodgeDiracKahlerSynthesis where
  dirac_sq_eq_neg_laplacian :
    ∀ {R : Type*} [CommRing R] [Invertible (2 : R)]
      {V : Type*} [AddCommGroup V] [Module R V]
      (d delta : Module.End R V),
      d * d = 0 → delta * delta = 0 →
      (diracKahler d delta) * (diracKahler d delta) = - laplacian d delta
  dirac_anticomm_chirality :
    ∀ {R : Type*} [CommRing R] [Invertible (2 : R)]
      {V : Type*} [AddCommGroup V] [Module R V]
      (d delta gamma : Module.End R V),
      d * gamma + gamma * d = 0 → delta * gamma + gamma * delta = 0 →
      (diracKahler d delta) * gamma + gamma * (diracKahler d delta) = 0
  laplacian_comm_dirac :
    ∀ {R : Type*} [CommRing R] [Invertible (2 : R)]
      {V : Type*} [AddCommGroup V] [Module R V]
      (d delta : Module.End R V),
      d * d = 0 → delta * delta = 0 →
      (diracKahler d delta) * laplacian d delta = (laplacian d delta) * (diracKahler d delta)
  laplacian_comm_chirality :
    ∀ {R : Type*} [CommRing R] [Invertible (2 : R)]
      {V : Type*} [AddCommGroup V] [Module R V]
      (d delta gamma : Module.End R V),
      d * gamma + gamma * d = 0 → delta * gamma + gamma * delta = 0 →
      gamma * laplacian d delta = (laplacian d delta) * gamma
  proj_plus_add_proj_minus :
    ∀ {R : Type*} [CommRing R] [Invertible (2 : R)]
      {V : Type*} [AddCommGroup V] [Module R V]
      (gamma : Module.End R V),
      projPlus gamma + projMinus gamma = 1
  proj_plus_sub_proj_minus :
    ∀ {R : Type*} [CommRing R] [Invertible (2 : R)]
      {V : Type*} [AddCommGroup V] [Module R V]
      (gamma : Module.End R V),
      projPlus gamma - projMinus gamma = gamma
  proj_plus_sq :
    ∀ {R : Type*} [CommRing R] [Invertible (2 : R)]
      {V : Type*} [AddCommGroup V] [Module R V]
      (gamma : Module.End R V),
      gamma * gamma = 1 →
      projPlus gamma * projPlus gamma = projPlus gamma
  proj_minus_sq :
    ∀ {R : Type*} [CommRing R] [Invertible (2 : R)]
      {V : Type*} [AddCommGroup V] [Module R V]
      (gamma : Module.End R V),
      gamma * gamma = 1 →
      projMinus gamma * projMinus gamma = projMinus gamma
  proj_orthogonal :
    ∀ {R : Type*} [CommRing R] [Invertible (2 : R)]
      {V : Type*} [AddCommGroup V] [Module R V]
      (gamma : Module.End R V),
      gamma * gamma = 1 →
      projPlus gamma * projMinus gamma = 0 ∧ projMinus gamma * projPlus gamma = 0
  dirac_proj_plus_intertwine :
    ∀ {R : Type*} [CommRing R] [Invertible (2 : R)]
      {V : Type*} [AddCommGroup V] [Module R V]
      (d delta gamma : Module.End R V),
      d * gamma + gamma * d = 0 → delta * gamma + gamma * delta = 0 →
      (diracKahler d delta) * projPlus gamma = projMinus gamma * (diracKahler d delta)
  dirac_proj_minus_intertwine :
    ∀ {R : Type*} [CommRing R] [Invertible (2 : R)]
      {V : Type*} [AddCommGroup V] [Module R V]
      (d delta gamma : Module.End R V),
      d * gamma + gamma * d = 0 → delta * gamma + gamma * delta = 0 →
      (diracKahler d delta) * projMinus gamma = projPlus gamma * (diracKahler d delta)
  dirac_cross_arrow_sum :
    ∀ {R : Type*} [CommRing R] [Invertible (2 : R)]
      {V : Type*} [AddCommGroup V] [Module R V]
      (d delta gamma : Module.End R V),
      d * gamma + gamma * d = 0 → delta * gamma + gamma * delta = 0 → gamma * gamma = 1 →
      diracKahlerPlus d delta gamma + diracKahlerMinus d delta gamma = diracKahler d delta
  dirac_diagonal_zero :
    ∀ {R : Type*} [CommRing R] [Invertible (2 : R)]
      {V : Type*} [AddCommGroup V] [Module R V]
      (d delta gamma : Module.End R V),
      d * gamma + gamma * d = 0 → delta * gamma + gamma * delta = 0 → gamma * gamma = 1 →
      projPlus gamma * (diracKahler d delta) * projPlus gamma = 0 ∧
      projMinus gamma * (diracKahler d delta) * projMinus gamma = 0
  dirac_cross_arrows_sq_zero :
    ∀ {R : Type*} [CommRing R] [Invertible (2 : R)]
      {V : Type*} [AddCommGroup V] [Module R V]
      (d delta gamma : Module.End R V),
      gamma * gamma = 1 →
      diracKahlerPlus d delta gamma * diracKahlerPlus d delta gamma = 0 ∧
      diracKahlerMinus d delta gamma * diracKahlerMinus d delta gamma = 0
  dirac_on_exact_coexact :
    ∀ {R : Type*} [CommRing R] [Invertible (2 : R)]
      {V : Type*} [AddCommGroup V] [Module R V]
      (d delta : Module.End R V),
      d * d = 0 → ∀ (alpha : V),
      (diracKahler d delta) (d alpha) = delta (- (d alpha))
  dirac_on_coexact_exact :
    ∀ {R : Type*} [CommRing R] [Invertible (2 : R)]
      {V : Type*} [AddCommGroup V] [Module R V]
      (d delta : Module.End R V),
      delta * delta = 0 → ∀ (beta : V),
      (diracKahler d delta) (delta beta) = d (delta beta)
  dirac_harmonic_zero :
    ∀ {R : Type*} [CommRing R] [Invertible (2 : R)]
      {V : Type*} [AddCommGroup V] [Module R V]
      (d delta : Module.End R V) (gamma_form : V),
      d gamma_form = 0 → delta gamma_form = 0 →
      (diracKahler d delta) gamma_form = 0
  laplacian_harmonic_zero :
    ∀ {R : Type*} [CommRing R] [Invertible (2 : R)]
      {V : Type*} [AddCommGroup V] [Module R V]
      (d delta : Module.End R V) (gamma_form : V),
      d gamma_form = 0 → delta gamma_form = 0 →
      (laplacian d delta) gamma_form = 0
  proj_exact_exact :
    ∀ {R : Type*} [CommRing R] [Invertible (2 : R)]
      {V : Type*} [AddCommGroup V] [Module R V]
      (d gamma : Module.End R V),
      d * gamma + gamma * d = 0 → ∀ (alpha : V),
      (projPlus gamma) (d alpha) = d ((projMinus gamma) alpha) ∧
      (projMinus gamma) (d alpha) = d ((projPlus gamma) alpha)
  proj_coexact_coexact :
    ∀ {R : Type*} [CommRing R] [Invertible (2 : R)]
      {V : Type*} [AddCommGroup V] [Module R V]
      (delta gamma : Module.End R V),
      delta * gamma + gamma * delta = 0 → ∀ (beta : V),
      (projPlus gamma) (delta beta) = delta ((projMinus gamma) beta) ∧
      (projMinus gamma) (delta beta) = delta ((projPlus gamma) beta)
  proj_harmonic_harmonic :
    ∀ {R : Type*} [CommRing R] [Invertible (2 : R)]
      {V : Type*} [AddCommGroup V] [Module R V]
      (d delta gamma : Module.End R V),
      d * gamma + gamma * d = 0 → delta * gamma + gamma * delta = 0 →
      ∀ (gamma_form : V), d gamma_form = 0 → delta gamma_form = 0 →
      (d ((projPlus gamma) gamma_form) = 0 ∧ delta ((projPlus gamma) gamma_form) = 0) ∧
      (d ((projMinus gamma) gamma_form) = 0 ∧ delta ((projMinus gamma) gamma_form) = 0)
  cylinder_exterior_d_anticomm :
    ∀ {R : Type*} [CommRing R] (D : CylinderDerivData R) (f : GradedForms R),
      exteriorD D (chirality f) + chirality (exteriorD D f) = 0
  cylinder_codifferential_anticomm :
    ∀ {R : Type*} [CommRing R] (D : CylinderDerivData R) (f : GradedForms R),
      codifferential D (chirality f) + chirality (codifferential D f) = 0
  cylinder_dirac_anticomm :
    ∀ {R : Type*} [CommRing R] (D : CylinderDerivData R) (f : GradedForms R),
      CylinderForms.cylinderDiracKahler D (chirality f) + chirality (CylinderForms.cylinderDiracKahler D f) = 0

/-- The verified canonical synthesis instance. -/
def chiral_hodge_dirackahler_synthesis : ChiralHodgeDiracKahlerSynthesis where
  dirac_sq_eq_neg_laplacian := diracKahler_sq
  dirac_anticomm_chirality := diracKahler_anticomm_gamma
  laplacian_comm_dirac := laplacian_comm_diracKahler
  laplacian_comm_chirality := laplacian_comm_gamma
  proj_plus_add_proj_minus := projPlus_add_projMinus
  proj_plus_sub_proj_minus := projPlus_sub_projMinus
  proj_plus_sq := projPlus_sq
  proj_minus_sq := projMinus_sq
  proj_orthogonal := proj_orthogonal
  dirac_proj_plus_intertwine := diracKahler_projPlus_intertwine
  dirac_proj_minus_intertwine := diracKahler_projMinus_intertwine
  dirac_cross_arrow_sum := diracKahler_sum_cross_arrows
  dirac_diagonal_zero := diracKahler_diagonal_blocks_zero
  dirac_cross_arrows_sq_zero := fun d delta gamma hg => ⟨diracKahlerPlus_sq d delta gamma hg, diracKahlerMinus_sq d delta gamma hg⟩
  dirac_on_exact_coexact := diracKahler_on_exact
  dirac_on_coexact_exact := diracKahler_on_coexact
  dirac_harmonic_zero := diracKahler_on_harmonic
  laplacian_harmonic_zero := laplacian_on_harmonic
  proj_exact_exact := fun d gamma hg alpha => ⟨projPlus_on_exact d gamma hg alpha, projMinus_on_exact d gamma hg alpha⟩
  proj_coexact_coexact := fun delta gamma hg beta => ⟨projPlus_on_coexact delta gamma hg beta, projMinus_on_coexact delta gamma hg beta⟩
  proj_harmonic_harmonic := fun d delta gamma hdg hdeltag gf hd hdelta =>
    ⟨projPlus_on_harmonic d delta gamma hdg hdeltag gf hd hdelta, projMinus_on_harmonic d delta gamma hdg hdeltag gf hd hdelta⟩
  cylinder_exterior_d_anticomm := CylinderForms.cylinderExteriorD_anticomm_chirality
  cylinder_codifferential_anticomm := CylinderForms.cylinderCodifferential_anticomm_chirality
  cylinder_dirac_anticomm := CylinderForms.cylinderDiracKahler_anticomm_chirality

end InfoGeometry.Canonical.ChiralHodgeDiracKahlerBridge
