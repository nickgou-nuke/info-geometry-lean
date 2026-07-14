import Mathlib.Data.Complex.Basic
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Canonical.PrimeGasPartitions
import InfoGeometry.Canonical.PrimeGasMaxEnt

/-!
# InfoGeometry.Canonical.PrimeHurwitzLimit

Conditional Hurwitz/Lee--Yang bridge to RH.

This file does not prove RH.

It formalizes the final theorem-safe reduction:

1. finite prime-gas approximants have Lee--Yang zeros on the unit circle;
2. a nonvanishing renormalization preserves those zero sets;
3. the renormalized approximants converge locally uniformly to the Cayley
   pullback of the completed `xi` function;
4. Hurwitz transfers zero-freeness from the finite approximants to the limit
   on the two connected components of the complement of the circle;
5. the Cayley map sends the Lee--Yang unit circle to the Riemann critical line.

The hard analytic work is isolated in `HurwitzZeroTransferWitness`.
-/

noncomputable section

namespace PrimeHurwitzLimit

/-- Cayley map sending the Riemann critical line to the Lee--Yang circle. -/
@[rep_depth operator]
def cayley
    (s : ℂ) : ℂ :=
  s / (1 - s)

/-- Inverse Cayley map. -/
@[rep_depth operator]
def cayleyInv
    (z : ℂ) : ℂ :=
  z / (1 + z)

/-- The inverse Cayley map undoes the Cayley map off the pole at `1`. -/
@[rep_depth operator]
theorem cayleyInv_cayley
    (s : ℂ) (hs : s ≠ 1) :
    cayleyInv (cayley s) = s := by
  have h1 : (1 - s) ≠ 0 := by
    intro h
    apply hs
    exact (sub_eq_zero.mp h).symm
  unfold cayleyInv cayley
  field_simp [h1]
  ring_nf

/-- The Lee--Yang unit circle. -/
@[rep_depth operator]
def OnUnitCircle
    (z : ℂ) : Prop :=
  Complex.normSq z = 1

/-- The open disk inside the Lee--Yang unit circle. -/
@[rep_depth operator]
def InUnitDisk
    (z : ℂ) : Prop :=
  Complex.normSq z < 1

/-- The exterior of the Lee--Yang unit circle. -/
@[rep_depth operator]
def OutsideUnitDisk
    (z : ℂ) : Prop :=
  1 < Complex.normSq z

/-- The Riemann critical line. -/
@[rep_depth operator]
def OnCriticalLine
    (s : ℂ) : Prop :=
  s.re = (1 / 2 : ℝ)

/--
Abstract completed-`xi` zero predicate.

This avoids hard-coding analytic number theory into this bridge file.  The
intended model is `XiZero s := ξ(s) = 0`, where `ξ` is the completed Riemann xi
function.
-/
@[rep_depth operator]
structure CompletedXiZeroPredicate where
  XiZero : ℂ → Prop
  zero_ne_one :
    ∀ s : ℂ, XiZero s → s ≠ 1

/-- RH stated relative to a completed-`xi` zero predicate. -/
@[rep_depth operator]
def RiemannHypothesis
    (Ξ : CompletedXiZeroPredicate) : Prop :=
  ∀ s : ℂ, Ξ.XiZero s → OnCriticalLine s

/--
Cayley geometry witness.

The facts are elementary complex algebra, but are stored as a witness so this
file remains focused on the Hurwitz/Lee--Yang proof interface.
-/
@[rep_depth operator]
structure CayleyCriticalWitness where
  cayleyInv_cayley :
    ∀ s : ℂ, s ≠ 1 → cayleyInv (cayley s) = s

  unit_of_critical :
    ∀ s : ℂ, s ≠ 1 → OnCriticalLine s → OnUnitCircle (cayley s)

  critical_of_unit :
    ∀ s : ℂ, s ≠ 1 → OnUnitCircle (cayley s) → OnCriticalLine s

  reflection_to_inversion :
    ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      cayley (1 - s) = (cayley s)⁻¹

namespace CayleyCriticalWitness

/-- The inverse Cayley map undoes the Cayley map off the pole at `1`. -/
@[rep_depth operator]
theorem cayleyInv_cayley_eq
    (s : ℂ) (hs : s ≠ 1) :
    cayleyInv (cayley s) = s := by
  have h1 : (1 - s) ≠ 0 := by
    intro h
    apply hs
    exact (sub_eq_zero.mp h).symm
  unfold cayleyInv cayley
  field_simp [h1]
  ring_nf

/-- The Cayley image of a critical-line point lies on the Lee--Yang unit circle. -/
@[rep_depth operator]
theorem cayley_unit_of_critical
    (s : ℂ) (hs : s ≠ 1) (hcrit : OnCriticalLine s) :
    OnUnitCircle (cayley s) := by
  have h1 : (1 - s) ≠ 0 := by
    intro h
    apply hs
    exact (sub_eq_zero.mp h).symm
  have hnorm : Complex.normSq s = Complex.normSq (1 - s) := by
    rw [Complex.normSq_apply, Complex.normSq_apply]
    rcases s with ⟨x, y⟩
    have hx : x = (1 / 2 : ℝ) := by simpa [OnCriticalLine] using hcrit
    rw [hx]
    norm_num
  have hden : Complex.normSq (1 - s) ≠ 0 := by
    exact ne_of_gt (Complex.normSq_pos.2 h1)
  calc
    Complex.normSq (cayley s)
        = Complex.normSq s / Complex.normSq (1 - s) := by
            rw [cayley, Complex.normSq_div]
    _ = 1 := by
          rw [hnorm]
          exact div_self hden

/-- A Lee--Yang unit-circle point has critical-line preimage under Cayley. -/
@[rep_depth operator]
theorem cayley_critical_of_unit
    (s : ℂ) (hs : s ≠ 1) (hunit : OnUnitCircle (cayley s)) :
    OnCriticalLine s := by
  rcases s with ⟨x, y⟩
  have h1 : (1 - ({ re := x, im := y } : ℂ)) ≠ 0 := by
    intro h
    apply hs
    exact (sub_eq_zero.mp h).symm
  have hdiv : Complex.normSq ({ re := x, im := y } : ℂ) /
      Complex.normSq (1 - ({ re := x, im := y } : ℂ)) = 1 := by
    simpa [OnUnitCircle, cayley, Complex.normSq_div] using hunit
  have hnorm : Complex.normSq ({ re := x, im := y } : ℂ) =
      Complex.normSq (1 - ({ re := x, im := y } : ℂ)) := by
    have hmul := congrArg (fun t : ℝ => t * Complex.normSq (1 - ({ re := x, im := y } : ℂ))) hdiv
    simpa [h1] using hmul
  have hx : x = (1 / 2 : ℝ) := by
    have hcoord : x * x + y * y = (1 - x) * (1 - x) + y * y := by
      simpa [Complex.normSq_apply] using hnorm
    nlinarith
  simpa [OnCriticalLine] using hx

/-- Reflection across the critical line corresponds to inversion on the circle. -/
@[rep_depth operator]
theorem cayley_reflection_to_inversion
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    cayley (1 - s) = (cayley s)⁻¹ := by
  unfold cayley
  field_simp [hs0, hs1]
  ring

/-- Native proof-carrying Cayley geometry witness. -/
@[rep_depth operator]
def canonicalCayleyCriticalWitness : CayleyCriticalWitness :=
  { cayleyInv_cayley := cayleyInv_cayley_eq
    unit_of_critical := cayley_unit_of_critical
    critical_of_unit := cayley_critical_of_unit
    reflection_to_inversion := cayley_reflection_to_inversion }

end CayleyCriticalWitness

/--
Finite Lee--Yang approximant family.

`Z N` is the finite-volume prime-chain partition readout, and `R N` is a
nonvanishing renormalization.  The limit object is usually the renormalized
product `R N z * Z N z`, not raw `Z N`.
-/
@[rep_depth operator]
structure LeeYangApproximants where
  Z : ℕ → ℂ → ℂ
  R : ℕ → ℂ → ℂ

  /-- Lee--Yang finite-volume circle property. -/
  lee_yang :
    ∀ N : ℕ, ∀ z : ℂ, Z N z = 0 → OnUnitCircle z

  /-- Renormalization has no zeros, so it introduces no spurious finite zeros. -/
  renorm_nonzero :
    ∀ N : ℕ, ∀ z : ℂ, R N z ≠ 0

/-- Renormalized finite approximant. -/
@[rep_depth operator]
def LeeYangApproximants.renormZ
    (A : LeeYangApproximants)
    (N : ℕ)
    (z : ℂ) : ℂ :=
  A.R N z * A.Z N z

/--
Locally uniform convergence of a renormalized approximant family.

This uses Mathlib's compact-open/local-uniform convergence predicate directly.
The concrete analytic file should prove this for `A.renormZ` and the Cayley
pullback of completed `xi`.
-/
@[rep_depth operator]
def LocallyUniformLimit
    (A_renorm : ℕ → ℂ → ℂ)
    (limitF : ℂ → ℂ) : Prop :=
  TendstoLocallyUniformly A_renorm limitF Filter.atTop

namespace LeeYangApproximants

/-- The renormalized approximant also has Lee--Yang zeros only on the circle. -/
@[rep_depth operator]
theorem renormZ_lee_yang
    (A : LeeYangApproximants) :
    ∀ N : ℕ, ∀ z : ℂ, A.renormZ N z = 0 → OnUnitCircle z := by
  intro N z hz
  unfold renormZ at hz
  have hprod : A.R N z = 0 ∨ A.Z N z = 0 :=
    mul_eq_zero.mp hz
  have hzZ : A.Z N z = 0 :=
    hprod.resolve_left (A.renorm_nonzero N z)
  exact A.lee_yang N z hzZ

end LeeYangApproximants

/--
Zero-free complement transfer for the limiting Cayley readout.

This is the precise shape of the Hurwitz consequence after applying the
theorem separately on the two domains:

* `|z| < 1`;
* `|z| > 1`.
-/
@[rep_depth operator]
structure ZeroFreeDomainTransfer where
  limitF : ℂ → ℂ
  inner_zero_free :
    ∀ z : ℂ, InUnitDisk z → limitF z ≠ 0
  outer_zero_free :
    ∀ z : ℂ, OutsideUnitDisk z → limitF z ≠ 0

namespace ZeroFreeDomainTransfer

/-- If a transferred limit has a zero, it must lie on the unit circle. -/
@[rep_depth operator]
theorem zero_on_unit_of_inner_outer_zero_free
    (T : ZeroFreeDomainTransfer)
    {z : ℂ}
    (hz : T.limitF z = 0) :
    OnUnitCircle z := by
  unfold OnUnitCircle
  by_cases hlt : Complex.normSq z < 1
  · exact False.elim (T.inner_zero_free z hlt hz)
  · by_cases hgt : 1 < Complex.normSq z
    · exact False.elim (T.outer_zero_free z hgt hz)
    · linarith

end ZeroFreeDomainTransfer

/--
Hurwitz zero-transfer witness.

This is the hard analytic part.  Mathematically it should be proved from
locally uniform convergence of the renormalized approximants and Hurwitz's
theorem on the zero-free components of the complement of the Lee--Yang circle.
Until that analytic theorem is formalized, we store the transfer as data.
-/
@[rep_depth operator]
structure HurwitzZeroTransferWitness
    (Ξ : CompletedXiZeroPredicate)
    (A : LeeYangApproximants) where
  /--
  Intended locally-uniform convergence statement for `A.renormZ`.

  This is deliberately a `Prop` witness rather than a fake theorem.  A later
  analytic file should replace it by a precise compact-open convergence
  statement on the Cayley chart.
  -/
  locallyUniformRenormalizedLimit : Prop

  /-- The limit is not identically zero on the zero-free components. -/
  nontrivialLimitOnComplement : Prop

  /-- No spurious zeros are produced by renormalization or limiting. -/
  noSpuriousZeros : Prop

  /-- Zero-free transfer on the two complement components. -/
  zeroFreeTransfer : ZeroFreeDomainTransfer

  /--
  Link from the abstract completed-`xi` zero predicate to the limiting Cayley
  readout.
  -/
  xiZero_to_limitZero :
    ∀ s : ℂ, Ξ.XiZero s → zeroFreeTransfer.limitF (cayley s) = 0

/-- Hurwitz conclusion: every completed-`xi` zero maps to the Lee--Yang circle. -/
@[bridge_target_tag, rep_depth operator]
theorem hurwitz_xiZeros_map_to_unit_circle
    {Ξ : CompletedXiZeroPredicate}
    {A : LeeYangApproximants}
    (H : HurwitzZeroTransferWitness Ξ A)
    (s : ℂ)
    (hs : Ξ.XiZero s) :
    OnUnitCircle (cayley s) :=
  ZeroFreeDomainTransfer.zero_on_unit_of_inner_outer_zero_free
    (HurwitzZeroTransferWitness.zeroFreeTransfer H)
    (HurwitzZeroTransferWitness.xiZero_to_limitZero H s hs)

/-- Conditional RH theorem from the Lee--Yang/Hurwitz package. -/
@[bridge_target_tag, rep_depth operator]
theorem RH_of_Hurwitz_LeeYang_limit
    (Ξ : CompletedXiZeroPredicate)
    (C : CayleyCriticalWitness)
    (A : LeeYangApproximants)
    (H : HurwitzZeroTransferWitness Ξ A) :
    RiemannHypothesis Ξ := by
  intro s hs
  have hs_ne_one : s ≠ 1 :=
    Ξ.zero_ne_one s hs
  have hcircle : OnUnitCircle (cayley s) :=
    hurwitz_xiZeros_map_to_unit_circle H s hs
  exact C.critical_of_unit s hs_ne_one hcircle

/-! ## Stronger split-domain witness -/

/--
Corrected Hurwitz witness with the analytic and zero-free pieces split.

This is the stronger future-facing form: locally uniform convergence is a
first-class field, and the zero-free complement transfer is explicitly carried
by `ZeroFreeDomainTransfer`.
-/
@[rep_depth operator]
structure CorrectHurwitzZeroTransferWitness
    (Ξ : CompletedXiZeroPredicate)
    (A : LeeYangApproximants) where
  limitF : ℂ → ℂ
  locallyUniformRenormalizedLimit :
    LocallyUniformLimit A.renormZ limitF
  nontrivial_in :
    ∃ z : ℂ, InUnitDisk z ∧ limitF z ≠ 0
  nontrivial_out :
    ∃ z : ℂ, OutsideUnitDisk z ∧ limitF z ≠ 0
  noSpuriousZeros : Prop
  transfer :
    ZeroFreeDomainTransfer
  transfer_limitF :
    transfer.limitF = limitF
  /--
  Link between the abstract completed-`xi` zeros and zeros of the Cayley
  limiting readout.
  -/
  xi_zero_iff_limit_zero :
    ∀ s : ℂ, s ≠ 1 → (Ξ.XiZero s ↔ limitF (cayley s) = 0)

/-- Zero-location transfer for the corrected split-domain Hurwitz witness. -/
@[bridge_target_tag, rep_depth operator]
theorem corrected_hurwitz_xiZeros_map_to_unit_circle
    {Ξ : CompletedXiZeroPredicate}
    {A : LeeYangApproximants}
    (H : CorrectHurwitzZeroTransferWitness Ξ A)
    (s : ℂ)
    (hs_ne_one : s ≠ 1)
    (hs : Ξ.XiZero s) :
    OnUnitCircle (cayley s) := by
  have hlimit : H.limitF (cayley s) = 0 :=
    (H.xi_zero_iff_limit_zero s hs_ne_one).mp hs
  have htransferZero : H.transfer.limitF (cayley s) = 0 := by
    rw [H.transfer_limitF]
    exact hlimit
  exact ZeroFreeDomainTransfer.zero_on_unit_of_inner_outer_zero_free
    H.transfer htransferZero

/--
Final conditional RH theorem from the corrected split-domain
Hurwitz/Lee--Yang package.
-/
@[bridge_target_tag, rep_depth operator]
theorem RH_from_Correct_Hurwitz_LeeYang
    (Ξ : CompletedXiZeroPredicate)
    (C : CayleyCriticalWitness)
    (A : LeeYangApproximants)
    (H : CorrectHurwitzZeroTransferWitness Ξ A) :
    RiemannHypothesis Ξ := by
  intro s hs
  have hs_ne_one : s ≠ 1 :=
    Ξ.zero_ne_one s hs
  have hcircle : OnUnitCircle (cayley s) :=
    corrected_hurwitz_xiZeros_map_to_unit_circle H s hs_ne_one hs
  exact C.critical_of_unit s hs_ne_one hcircle

end PrimeHurwitzLimit
