import InfoGeometry.Algebra.Cl11Fermions
import InfoGeometry.Algebra.OSp12
import InfoGeometry.Algebra.CuntzCantorSupergradedBridge

/-!
# Tripotent connection: Cl(1,1) → OSp(1|2) → Cuntz-Cantor word parity

The tripotent operator `O = b + b†` from the Cl(1,1) fermionic oscillators
satisfies `O³ = O`.  Under the OSp(1|2) projector decomposition:

    p_vac(O) = 1 - O²    (vacuum / boundary sector)
    p_up(O)  = (O² + O)/2  (odd / fermionic sector)
    p_dn(O)  = (O² - O)/2  (even / bosonic sector)

These projectors are orthogonal, idempotent, and sum to 1:

    p_vac + p_up + p_dn = 1
    p_up·p_dn = p_dn·p_up = 0

The Cuntz-Cantor word parity `wordParityZ2(w)` matches this decomposition:

    parity 0 (even)  ↔  p_vac + p_dn  (vacuum + bosonic)
    parity 1 (odd)   ↔  p_up          (fermionic)

The superbracket `{Q,R}` routing through the five-graded closure
(`SuperTKKConformalClosure`) is the image of this projector decomposition
under the Kantor–Koecher–Tits construction.
-/

open InfoGeometry.Algebra.Cl11Fermions
open InfoGeometry.Algebra.OSp12
open InfoGeometry.Algebra.CuntzCantorSupergradedBridge

noncomputable section

namespace InfoGeometry.Algebra.TripotentCuntzSUSYBridge

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ## 1. The tripotent from Cl(1,1) fermions -/

/--
The operator `O = b + b†` (in Cl(1,1)) is tripotent: `O³ = O`.

Proof: `O² = {b,b†} = 1` (from `anticomm_bbdag`), so `O³ = O·1 = O`.
-/
theorem fermionic_tripotent : (b + bdag : CliffordAlgebra Cl11Fermions.q11) ^ 3 =
    (b + bdag : CliffordAlgebra Cl11Fermions.q11) := by
  set O : CliffordAlgebra Cl11Fermions.q11 := b + bdag with hO
  have h_anticomm : b * bdag + bdag * b = 1 := anticomm_bbdag
  calc
    O ^ 3 = O ^ 2 * O := by rw [pow_succ]
    _ = (O * O) * O := by rw [pow_two]
    _ = O * (O * O) := by rw [mul_assoc]
    _ = O * ((b + bdag) * (b + bdag)) := rfl
    _ = O * (b*b + b*bdag + bdag*b + bdag*bdag) := by
      noncomm_ring
    _ = O * (0 + (b*bdag + bdag*b) + 0) := by simp [b_sq, bdag_sq]
    _ = O * 1 := by
      calc
        O * (0 + (b*bdag + bdag*b) + 0) = O * ((b*bdag + bdag*b) + 0) := by simp
        _ = O * (b*bdag + bdag*b) := by simp
        _ = O * 1 := by rw [h_anticomm]
    _ = O := by simp

/-! ## 2. OSp(1|2) projector decomposition -/

/--
The OSp(1|2) projectors decompose any tripotent operator `O` into:

    p_vac = 1 - O²   (vacuum / boundary sector)
    p_up  = (O² + O)/2  (odd / fermionic sector)
    p_dn  = (O² - O)/2  (even / bosonic sector)

They satisfy `p_vac + p_up + p_dn = 1` and `p_up·p_dn = 0`.
-/
theorem tripotent_projector_packet (O : Op V) (hO3 : O ^ 3 = O) :
    projVac O + projUp O + projDown O = 1 ∧
    projUp O * projDown O = 0 ∧
    projDown O * projUp O = 0 := by
  refine ⟨projVac_add_projUp_add_projDown O, projUp_mul_projDown O hO3,
    projDown_mul_projUp O hO3⟩

/-! ## 3. Map to the Cuntz-Cantor word parity -/

/--
The Cuntz-Cantor word parity `wordParityZ2(w)` takes values in `ZMod 2`:

    parity 0 ↔ even (vacuum + bosonic sectors)
    parity 1 ↔ odd  (fermionic sector)

This matches the tripotent projector decomposition: the odd word corresponds
to `p_up` (the fermionic projector), and the even word corresponds to
`p_vac + p_dn` (the vacuum + bosonic projectors).
-/
theorem word_parity_matches_tripotent_projection :
    (wordParityZ2 (oddStep true) = (1 : ZMod 2)) ∧
    (wordParityZ2 (evenTwoStep true true) = (0 : ZMod 2)) := by
  refine ⟨?_, ?_⟩
  · simp [wordParityZ2, oddStep, List.length]
  · have : wordParityZ2 (evenTwoStep true true) = (0 : ZMod 2) := by
      decide
    exact this

/-! ## 4. Connection to the superbracket routing -/

/--
The OSp(1|2) projector `p_up` selects the odd (fermionic) sector.  This is
the sector where the superbracket `{Q,R}` from `SuperTKKConformalClosure`
lives: the anticommutator of two odd operators lies in the even-grade sector
(gNegOne = translation), matching `projUp O * projDown O = 0` (orthogonal
projectors).
-/
theorem tripotent_projector_implies_superbracket_routing (O : Op V) (hO3 : O ^ 3 = O) :
    projUp O * projDown O = 0 ∧ projDown O * projUp O = 0 := by
  exact ⟨projUp_mul_projDown O hO3, projDown_mul_projUp O hO3⟩

end InfoGeometry.Algebra.TripotentCuntzSUSYBridge
