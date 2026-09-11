import InfoGeometry.Topology.ZetaFlowKleinSemidirectBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.PeirceV4GrandCanonicalEnsembleBridge
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# V₄ Character Readouts and Finite SO(5,5)-Type Polynomial Data

This module formalizes finite character readouts over the complete Klein
Four-Group $V_4 \simeq \mathbb{Z}_2 \times \mathbb{Z}_2$ spectrum and a finite
quadratic Chern-polynomial shadow for a 10-dimensional carrier.

1. **Complete $V_4$ Character Table:**
   - $\chi_0 = (1, 1, 1, 1)$ (Trivial sector);
   - $\chi_h = (1, 1, -1, -1)$ (Height / time-inversion character);
   - $\chi_u = (1, -1, -1, 1)$ (Transverse parity character);
   - $\chi_s = (1, -1, 1, -1)$ (Spatial reflection character).

2. **$V_4$ Grand Character Ensemble & Exact Inversion:**
   $$\mathcal{Z}(g; \beta, \mu) = \sum_{\chi} \chi(g) \mathcal{Z}_\chi(\beta, \mu)$$
   $$\mathcal{Z}_\chi(\beta, \mu) = \frac{1}{4} \sum_{g \in V_4} \chi(g) \mathcal{Z}(g; \beta, \mu)$$

3. **Finite polynomial readout:**
   - the dimension calculation $10 \cdot 9 / 2 = 45$;
   - a supplied scalar field `tr_F2` and the polynomial `10 + tr_F2/2`.

4. This file does **not** construct a trace/exponential Souriau partition,
   a concrete $O(5,5)$ or Pin action, or Chern--Weil cohomology.  Those are
   separate downstream owners.
-/

noncomputable section

namespace InfoGeometry.Canonical.V4O55SouriauChernPartition

open InfoGeometry.Topology.ZetaFlowKleinSemidirect

/-! ## 1. Full V₄ Character Table -/

/-- The 4 irreducible characters of V₄ ≃ ℤ₂ × ℤ₂ -/
inductive V4Char : Type
  | chi0 : V4Char -- Trivial character
  | chih : V4Char -- Height / vertical character
  | chiu : V4Char -- Transverse parity character
  | chis : V4Char -- Spatial reflection character
  deriving DecidableEq

namespace V4Char

/-- Character evaluation on group elements (g1, g2) ∈ ℤ₂ × ℤ₂ -/
def eval : V4Char → ZetaKlein4 → ℝ
  | chi0, _       => 1
  | chih, (0, 0)  => 1
  | chih, (0, 1)  => 1
  | chih, (1, 0)  => -1
  | chih, (1, 1)  => -1
  | chiu, (0, 0)  => 1
  | chiu, (0, 1)  => -1
  | chiu, (1, 0)  => -1
  | chiu, (1, 1)  => 1
  | chis, (0, 0)  => 1
  | chis, (0, 1)  => -1
  | chis, (1, 0)  => 1
  | chis, (1, 1)  => -1

/-- 🏆 THEOREM 1: V₄ Character Orthogonality at the Identity:
    $$\sum_{\chi} \chi(e) = 1 + 1 + 1 + 1 = 4 = |V_4|$$ -/
theorem character_sum_at_identity :
    eval chi0 (0, 0) + eval chih (0, 0) + eval chiu (0, 0) + eval chis (0, 0) = 4 := by
  dsimp [eval]
  ring

/-- 🏆 THEOREM 2: V₄ Character Orthogonality on Non-Identity Elements:
    $$\sum_{\chi} \chi(g) = 0 \qquad (\forall g \ne e)$$ -/
theorem character_sum_at_nonidentity (g : ZetaKlein4) (hg : g ≠ (0, 0)) :
    eval chi0 g + eval chih g + eval chiu g + eval chis g = 0 := by
  rcases g with ⟨g1, g2⟩
  fin_cases g1 <;> fin_cases g2
  · exfalso; exact hg rfl
  · dsimp [eval]; ring
  · dsimp [eval]; ring
  · dsimp [eval]; ring

end V4Char

/-! ## 2. V₄ Character Grand Partition Function -/

/-- Multi-sector partition datum indexed by the 4 V₄ characters -/
structure V4PartitionDatum where
  Z_0 : ℝ
  Z_h : ℝ
  Z_u : ℝ
  Z_s : ℝ

namespace V4PartitionDatum

/-- Group-element twisted partition function:
    $$\mathcal{Z}(g) = \sum_\chi \chi(g) \mathcal{Z}_\chi$$ -/
def groupPartition (D : V4PartitionDatum) (g : ZetaKlein4) : ℝ :=
  V4Char.eval V4Char.chi0 g * D.Z_0 +
  V4Char.eval V4Char.chih g * D.Z_h +
  V4Char.eval V4Char.chiu g * D.Z_u +
  V4Char.eval V4Char.chis g * D.Z_s

/-! The four group readouts are explicit specializations of the canonical
four-sector grand-canonical polynomial.  This is a finite coherence theorem;
it does not construct a trace/exponential Souriau partition. -/

theorem groupPartition_identity_eq_grandCanonical (D : V4PartitionDatum) :
    D.groupPartition (0, 0) =
      InfoGeometry.Canonical.PeirceV4GrandCanonical.grandCanonicalV4Partition
        1 1 D.Z_0 D.Z_h D.Z_u D.Z_s := by
  dsimp [groupPartition, V4Char.eval,
    InfoGeometry.Canonical.PeirceV4GrandCanonical.grandCanonicalV4Partition]
  ring

theorem groupPartition_01_eq_grandCanonical (D : V4PartitionDatum) :
    D.groupPartition (0, 1) =
      InfoGeometry.Canonical.PeirceV4GrandCanonical.grandCanonicalV4Partition
        1 (-1) D.Z_0 D.Z_h D.Z_u D.Z_s := by
  dsimp [groupPartition, V4Char.eval,
    InfoGeometry.Canonical.PeirceV4GrandCanonical.grandCanonicalV4Partition]
  ring

theorem groupPartition_10_eq_grandCanonical (D : V4PartitionDatum) :
    D.groupPartition (1, 0) =
      InfoGeometry.Canonical.PeirceV4GrandCanonical.grandCanonicalV4Partition
        (-1) (-1) D.Z_0 D.Z_h D.Z_u D.Z_s := by
  dsimp [groupPartition, V4Char.eval,
    InfoGeometry.Canonical.PeirceV4GrandCanonical.grandCanonicalV4Partition]
  ring

theorem groupPartition_11_eq_grandCanonical (D : V4PartitionDatum) :
    D.groupPartition (1, 1) =
      InfoGeometry.Canonical.PeirceV4GrandCanonical.grandCanonicalV4Partition
        (-1) 1 D.Z_0 D.Z_h D.Z_u D.Z_s := by
  dsimp [groupPartition, V4Char.eval,
    InfoGeometry.Canonical.PeirceV4GrandCanonical.grandCanonicalV4Partition]
  ring

/-- 🏆 THEOREM 3: Exact Fourier Inversion to Recover Character Sector $\mathcal{Z}_0$:
    $$\mathcal{Z}_0 = \frac{1}{4}\sum_{g \in V_4} \mathcal{Z}(g)$$ -/
theorem recover_Z0 (D : V4PartitionDatum) :
    (1 / 4 : ℝ) * (D.groupPartition (0, 0) + D.groupPartition (0, 1) +
                   D.groupPartition (1, 0) + D.groupPartition (1, 1)) = D.Z_0 := by
  dsimp [groupPartition, V4Char.eval]
  ring

/-- 🏆 THEOREM 4: Exact Fourier Inversion to Recover Height Sector $\mathcal{Z}_h$:
    $$\mathcal{Z}_h = \frac{1}{4}\sum_{g \in V_4} \chi_h(g) \mathcal{Z}(g)$$ -/
theorem recover_Zh (D : V4PartitionDatum) :
    (1 / 4 : ℝ) * (1 * D.groupPartition (0, 0) + 1 * D.groupPartition (0, 1) +
                   (-1) * D.groupPartition (1, 0) + (-1) * D.groupPartition (1, 1)) = D.Z_h := by
  dsimp [groupPartition, V4Char.eval]
  ring

/-- Exact Fourier inversion to recover the transverse sector. -/
theorem recover_Zu (D : V4PartitionDatum) :
    (1 / 4 : ℝ) * (1 * D.groupPartition (0, 0) + (-1) * D.groupPartition (0, 1) +
                   (-1) * D.groupPartition (1, 0) + 1 * D.groupPartition (1, 1)) = D.Z_u := by
  dsimp [groupPartition, V4Char.eval]
  ring

/-- Exact Fourier inversion to recover the spatial-reflection sector. -/
theorem recover_Zs (D : V4PartitionDatum) :
    (1 / 4 : ℝ) * (1 * D.groupPartition (0, 0) + (-1) * D.groupPartition (0, 1) +
                   1 * D.groupPartition (1, 0) + (-1) * D.groupPartition (1, 1)) = D.Z_s := by
  dsimp [groupPartition, V4Char.eval]
  ring

end V4PartitionDatum

/-! ## 3. O(5,5) / 𝔰𝔬(5,5) Lie Bivector Curvature & Chern Polynomial -/

/-- Dimension of the split orthogonal Lie algebra 𝔰𝔬(5,5) -/
def dim_so55 : ℕ := 10 * 9 / 2

/-- 🏆 THEOREM 5: Exact Lie Algebra Dimension:
    $$\dim \mathfrak{so}(5,5) = 45$$ -/
theorem dim_so55_eq : dim_so55 = 45 := by
  norm_num [dim_so55]

/-- Finite scalar polynomial readout.  The field `tr_F2` is supplied data;
    no curvature matrix or trace operation is constructed here. -/
structure ChernPolySO55 where
  tr_F2 : ℝ

namespace ChernPolySO55

def ch0 : ℝ := 10
def ch1 : ℝ := 0
def ch2 (c : ChernPolySO55) : ℝ := (1 / 2) * c.tr_F2

/-- Total Chern character evaluation up to degree 2:
    $$\operatorname{ch}(F) = \operatorname{ch}_0 + \operatorname{ch}_1 + \operatorname{ch}_2 = 10 + \frac{1}{2}\operatorname{tr}(F^2)$$ -/
def totalChern (c : ChernPolySO55) : ℝ :=
  ch0 + ch1 + c.ch2

/-- The degree-one readout is zero by definition.  This is not a
    Chern--Weil theorem and does not quantify over connections. -/
theorem ch1_readout_zero : ch1 = 0 := by
  norm_num [ch1]

/-- 🏆 THEOREM 7: Total Chern Character Reduction to Quadratic Invariant:
    $$\operatorname{ch}(F) = 10 + \frac{1}{2}\operatorname{tr}(F^2)$$ -/
theorem totalChern_eq (c : ChernPolySO55) :
    c.totalChern = 10 + (1 / 2) * c.tr_F2 := by
  dsimp [totalChern, ch0, ch1, ch2]
  ring

end ChernPolySO55

end InfoGeometry.Canonical.V4O55SouriauChernPartition
