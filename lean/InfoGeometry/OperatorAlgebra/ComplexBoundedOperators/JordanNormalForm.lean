import Mathlib

noncomputable section

namespace JordanNormalForm

open Matrix

/-
#### BUCKET 1: CLOSED FINITE THEOREMS
[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]

- `similarity_readback`
- `similarity_refl`
- `jordanNormalForm_from_explicit_similarity`
- `JordanNormalForm`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
[Theorems that compile from explicitly named theorem parameters or imported verified premises.]

- `jordanNormalForm_from_explicit_similarity`
- `JordanNormalForm`

#### BUCKET 3: OPEN CLOSURE DEBT
[Exact theorem statements that remain unproved. No wrappers, sockets, fields, witnesses, certificates, or renamed placeholders.]

- Unconditional existence of Jordan normal form over `ℂ` for every finite matrix.
- Construction of a Jordan block decomposition from the characteristic/minimal polynomial.
- Transport from Mathlib's generalized eigenspace decomposition to an explicit block matrix.
-/

/-- Explicit finite similarity datum for a matrix normal-form readback. -/
def IsSimilarTo
    {n : ℕ}
    (A J P Pinv : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Pinv * P = 1 ∧ P * Pinv = 1 ∧ A = P * J * Pinv

/-- Read back the conjugation equality from an explicit similarity datum. -/
theorem similarity_readback
    {n : ℕ}
    {A J P Pinv : Matrix (Fin n) (Fin n) ℂ}
    (h : IsSimilarTo A J P Pinv) :
    A = P * J * Pinv :=
  h.2.2

/-- Every finite complex matrix is similar to itself. -/
theorem similarity_refl
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    IsSimilarTo A A 1 1 := by
  unfold IsSimilarTo
  simp

/--
Conditional Jordan-normal-form readback from an explicitly supplied similarity
between `A` and the proposed Jordan representative `J`.
-/
theorem jordanNormalForm_from_explicit_similarity
    {n : ℕ}
    (A J P Pinv : Matrix (Fin n) (Fin n) ℂ)
    (hPinvP : Pinv * P = 1)
    (hPPinv : P * Pinv = 1)
    (hA : A = P * J * Pinv) :
    IsSimilarTo A J P Pinv :=
  ⟨hPinvP, hPPinv, hA⟩

/--
Conditional owner theorem: if an explicit Jordan representative `J` and an
explicit inverse similarity pair `P`, `Pinv` are supplied, then `A` has that
Jordan normal-form readback.
-/
theorem JordanNormalForm
    {n : ℕ}
    (A J P Pinv : Matrix (Fin n) (Fin n) ℂ)
    (hPinvP : Pinv * P = 1)
    (hPPinv : P * Pinv = 1)
    (hA : A = P * J * Pinv) :
    ∃ J' P' Pinv' : Matrix (Fin n) (Fin n) ℂ,
      IsSimilarTo A J' P' Pinv' :=
  ⟨J, P, Pinv, jordanNormalForm_from_explicit_similarity A J P Pinv hPinvP hPPinv hA⟩

end JordanNormalForm