import Mathlib.Tactic

/-!
# InfoGeometry.Analysis.AsanoRuelleBasicBranches

Concrete algebraic branches of the Asano--Ruelle contraction lemma.

This file proves real source lemmas:

* zero-freeness off `K₁ × K₂` and `0 ∉ K₁, 0 ∉ K₂` imply `A ≠ 0`;
* the `D = 0` branch of the contraction theorem;
* the degenerate branch `A * D - B * C = 0` forces the endpoint memberships
  `-(C / D) ∈ K₁` and `-(B / D) ∈ K₂`.

No wrappers.
No `sorry`.
-/

namespace InfoGeometry.Analysis.AsanoRuelleBasicBranches

/-- Two-variable separately affine Asano block. -/
def Phi (A B C D z₁ z₂ : ℂ) : ℂ :=
  A + B * z₁ + C * z₂ + D * z₁ * z₂

/-- Contracted one-variable polynomial. -/
def contractedQ (A D z : ℂ) : ℂ :=
  A + D * z

/--
The constant term is nonzero.

If `0 ∉ K₁`, `0 ∉ K₂`, and `Φ` has no zero off `K₁ × K₂`, then
`A = Φ(0,0)` is nonzero.
-/
theorem asano_A_ne_zero_of_zero_free
    (A B C D : ℂ)
    (K₁ K₂ : Set ℂ)
    (h0K₁ : (0 : ℂ) ∉ K₁)
    (h0K₂ : (0 : ℂ) ∉ K₂)
    (hZeroFree :
      ∀ z₁ z₂ : ℂ,
        z₁ ∉ K₁ →
        z₂ ∉ K₂ →
        Phi A B C D z₁ z₂ ≠ 0) :
    A ≠ 0 := by
  have h := hZeroFree 0 0 h0K₁ h0K₂
  simpa [Phi] using h

/--
The `D = 0` branch of Asano contraction.

If `D = 0`, then the contracted polynomial is the nonzero constant `A`.
-/
theorem asano_D_zero_branch
    (A B C D : ℂ)
    (K₁ K₂ : Set ℂ)
    (h0K₁ : (0 : ℂ) ∉ K₁)
    (h0K₂ : (0 : ℂ) ∉ K₂)
    (hZeroFree :
      ∀ z₁ z₂ : ℂ,
        z₁ ∉ K₁ →
        z₂ ∉ K₂ →
        Phi A B C D z₁ z₂ ≠ 0)
    (hD : D = 0)
    (z : ℂ) :
    contractedQ A D z ≠ 0 := by
  have hA :
      A ≠ 0 :=
    asano_A_ne_zero_of_zero_free
      A B C D K₁ K₂ h0K₁ h0K₂ hZeroFree
  simpa [contractedQ, hD] using hA

/--
Degenerate endpoint calculation, left variable.

If `D ≠ 0` and `A * D - B * C = 0`, then

`Φ(-(C/D), z₂) = 0`

for every `z₂`.
-/
theorem phi_left_endpoint_zero_of_degenerate
    (A B C D z₂ : ℂ)
    (hD : D ≠ 0)
    (hdeg : A * D - B * C = 0) :
    Phi A B C D (-(C / D)) z₂ = 0 := by
  have hAD : A * D = B * C := by
    exact sub_eq_zero.mp hdeg
  have hA : A = (B * C) / D := by
    calc
      A = (A * D) / D := by
        field_simp [hD]
      _ = (B * C) / D := by
        rw [hAD]
  unfold Phi
  rw [hA]
  field_simp [hD]
  ring

/--
Degenerate endpoint calculation, right variable.

If `D ≠ 0` and `A * D - B * C = 0`, then

`Φ(z₁, -(B/D)) = 0`

for every `z₁`.
-/
theorem phi_right_endpoint_zero_of_degenerate
    (A B C D z₁ : ℂ)
    (hD : D ≠ 0)
    (hdeg : A * D - B * C = 0) :
    Phi A B C D z₁ (-(B / D)) = 0 := by
  have hAD : A * D = B * C := by
    exact sub_eq_zero.mp hdeg
  have hA : A = (B * C) / D := by
    calc
      A = (A * D) / D := by
        field_simp [hD]
      _ = (B * C) / D := by
        rw [hAD]
  unfold Phi
  rw [hA]
  field_simp [hD]
  ring

/--
Degenerate branch: the left endpoint must lie in `K₁`.

If `-(C/D) ∉ K₁`, then choosing `z₂ = 0 ∉ K₂` gives a zero of `Φ`
outside the forbidden domain, contradicting zero-freeness.
-/
theorem asano_degenerate_left_endpoint_mem
    (A B C D : ℂ)
    (K₁ K₂ : Set ℂ)
    (h0K₂ : (0 : ℂ) ∉ K₂)
    (hD : D ≠ 0)
    (hdeg : A * D - B * C = 0)
    (hZeroFree :
      ∀ z₁ z₂ : ℂ,
        z₁ ∉ K₁ →
        z₂ ∉ K₂ →
        Phi A B C D z₁ z₂ ≠ 0) :
    -(C / D) ∈ K₁ := by
  by_contra hnot
  have hzero :
      Phi A B C D (-(C / D)) 0 = 0 :=
    phi_left_endpoint_zero_of_degenerate A B C D 0 hD hdeg
  exact (hZeroFree (-(C / D)) 0 hnot h0K₂) hzero

/--
Degenerate branch: the right endpoint must lie in `K₂`.

If `-(B/D) ∉ K₂`, then choosing `z₁ = 0 ∉ K₁` gives a zero of `Φ`
outside the forbidden domain, contradicting zero-freeness.
-/
theorem asano_degenerate_right_endpoint_mem
    (A B C D : ℂ)
    (K₁ K₂ : Set ℂ)
    (h0K₁ : (0 : ℂ) ∉ K₁)
    (hD : D ≠ 0)
    (hdeg : A * D - B * C = 0)
    (hZeroFree :
      ∀ z₁ z₂ : ℂ,
        z₁ ∉ K₁ →
        z₂ ∉ K₂ →
        Phi A B C D z₁ z₂ ≠ 0) :
    -(B / D) ∈ K₂ := by
  by_contra hnot
  have hzero :
      Phi A B C D 0 (-(B / D)) = 0 :=
    phi_right_endpoint_zero_of_degenerate A B C D 0 hD hdeg
  exact (hZeroFree 0 (-(B / D)) h0K₁ hnot) hzero

end InfoGeometry.Analysis.AsanoRuelleBasicBranches

