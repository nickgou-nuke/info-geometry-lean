import Mathlib

noncomputable section

namespace InfoGeometry.Quantum.KleinParafermionCohomology

/--
Minimal algebraic model of a cross-cap holonomy.

`W` is the observed holonomy, `mirrorW` is its chiral/cross-cap transform.
The two conservative assumptions encode:
* V₄ invariance: `W = mirrorW`;
* cross-cap reversal: `mirrorW = W⁻¹`.
-/
structure CrossCapHolonomy where
  W : ℂ
  mirrorW : ℂ
  nonzero : W ≠ 0
  v4_invariant : W = mirrorW
  crosscap_reversal : mirrorW = W⁻¹

/-- The cross-cap invariant is 2-torsion: `W² = 1`. -/
theorem crosscap_holonomy_sq_one (H : CrossCapHolonomy) :
    H.W ^ 2 = 1 := by
  have h_inv : H.W = H.W⁻¹ := by
    exact H.v4_invariant.trans H.crosscap_reversal
  calc
    H.W ^ 2 = H.W * H.W := by ring
    _ = H.W * H.W⁻¹ := by nth_rw 2 [h_inv]
    _ = 1 := mul_inv_cancel₀ H.nonzero

/-- Over complex phases, a 2-torsion cross-cap holonomy is globally bosonic or fermionic. -/
theorem crosscap_holonomy_is_boson_or_fermion (H : CrossCapHolonomy) :
    H.W = 1 ∨ H.W = -1 := by
  exact sq_eq_one_iff.mp (crosscap_holonomy_sq_one H)

/-- A local parafermion phase of finite order. -/
structure ParafermionPhase (N : ℕ) where
  q : ℂ
  nonzero : q ≠ 0
  finite_order : q ^ N = 1

/--
If a local parafermion phase survives as a global cross-cap holonomy, then the
Klein cross-cap projection forces the global phase into the ordinary `±1`
torsion sectors.
-/
theorem parafermion_crosscap_projection {N : ℕ} (P : ParafermionPhase N)
    (hcross : P.q = P.q⁻¹) :
    P.q = 1 ∨ P.q = -1 := by
  have hsquare : P.q ^ 2 = 1 := by
    calc
      P.q ^ 2 = P.q * P.q := by ring
      _ = P.q * P.q⁻¹ := by nth_rw 2 [hcross]
      _ = 1 := mul_inv_cancel₀ P.nonzero
  exact sq_eq_one_iff.mp hsquare

/-- A fifth-root phase surviving the Klein cross-cap projection is trivial. -/
theorem fifth_root_crosscap_trivial {q : ℂ}
    (hq5 : q ^ 5 = 1) (hq0 : q ≠ 0) (hcross : q = q⁻¹) :
    q = 1 := by
  have hsquare : q ^ 2 = 1 := by
    calc
      q ^ 2 = q * q := by ring
      _ = q * q⁻¹ := by nth_rw 2 [hcross]
      _ = 1 := mul_inv_cancel₀ hq0
  have h4 : q ^ 4 = 1 := by
    calc
      q ^ 4 = (q ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hsquare]; ring
  calc
    q = q ^ 4 * q := by rw [h4]; ring
    _ = q ^ 5 := by ring
    _ = 1 := hq5

/-- A third-root phase surviving the Klein cross-cap projection is trivial. -/
theorem third_root_crosscap_trivial {q : ℂ}
    (hq3 : q ^ 3 = 1) (hq0 : q ≠ 0) (hcross : q = q⁻¹) :
    q = 1 := by
  have hsquare : q ^ 2 = 1 := by
    calc
      q ^ 2 = q * q := by ring
      _ = q * q⁻¹ := by nth_rw 2 [hcross]
      _ = 1 := mul_inv_cancel₀ hq0
  calc
    q = q ^ 2 * q := by rw [hsquare]; ring
    _ = q ^ 3 := by ring
    _ = 1 := hq3

/-- The two global torsion sectors selected by the cross-cap projection. -/
inductive GlobalTorsionSector
  | boson
  | fermion
  deriving DecidableEq, Repr

/-- Classify a cross-cap holonomy after the `±1` projection. -/
def sectorOfHolonomy (H : CrossCapHolonomy) : GlobalTorsionSector :=
  if H.W = 1 then GlobalTorsionSector.boson else GlobalTorsionSector.fermion

theorem sectorOfHolonomy_boson (H : CrossCapHolonomy) (h : H.W = 1) :
    sectorOfHolonomy H = GlobalTorsionSector.boson := by
  simp [sectorOfHolonomy, h]

theorem sectorOfHolonomy_fermion (H : CrossCapHolonomy) (h : H.W = -1) :
    sectorOfHolonomy H = GlobalTorsionSector.fermion := by
  have hne : H.W ≠ 1 := by
    intro h1
    have : (-1 : ℂ) = 1 := by simpa [h] using h1
    norm_num at this
  simp [sectorOfHolonomy, hne]

/--
Bundled conservative invariant:
any nonzero V₄-invariant holonomy that is inverted by the cross-cap is a
2-torsion phase and therefore lands in one of the two global sectors.
-/
theorem klein_parafermion_cohomology_invariant (H : CrossCapHolonomy) :
    H.W ^ 2 = 1 ∧ (H.W = 1 ∨ H.W = -1) := by
  exact ⟨crosscap_holonomy_sq_one H, crosscap_holonomy_is_boson_or_fermion H⟩

/--
Odd parafermion phases of order 3 or 5 do not survive as nontrivial global
Klein cross-cap holonomies; the global projected class is forced to `1`.
-/
theorem odd_parafermion_crosscap_collapse :
    (∀ q : ℂ, q ^ 5 = 1 → q ≠ 0 → q = q⁻¹ → q = 1) ∧
      (∀ q : ℂ, q ^ 3 = 1 → q ≠ 0 → q = q⁻¹ → q = 1) := by
  exact ⟨fun q h5 h0 hcross => fifth_root_crosscap_trivial h5 h0 hcross,
    fun q h3 h0 hcross => third_root_crosscap_trivial h3 h0 hcross⟩

end InfoGeometry.Quantum.KleinParafermionCohomology
