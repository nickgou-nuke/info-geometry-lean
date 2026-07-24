import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# S3 Bruhat Lengths

Finite inversion-length computation for the six elements of the Weyl group
`W(SL_3,T)`, identified with `S3`.

#### BUCKET 1: CLOSED FINITE THEOREMS
[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]
- `len_s_e`
- `len_s_12`
- `len_s_23`
- `len_s_123`
- `len_s_132`
- `len_s_13`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- None.

#### BUCKET 3: OPEN CLOSURE DEBT
- None.
-/

set_option autoImplicit false

namespace InfoGeometry.Canonical.S3BruhatLengths

/-- The inversion set of a map `f : Fin n -> Fin n`. -/
def inversions (n : Nat) (f : Fin n -> Fin n) : Finset (Fin n × Fin n) :=
  Finset.filter (fun p => p.1 < p.2 ∧ f p.2 < f p.1) Finset.univ

/-- The inversion number of a map `f : Fin n -> Fin n`. -/
def inv_length (n : Nat) (f : Fin n -> Fin n) : Nat :=
  (inversions n f).card

/-- The identity permutation. -/
def s_e (x : Fin 3) : Fin 3 :=
  if x.val = 0 then 0
  else if x.val = 1 then 1
  else 2

/-- The adjacent transposition swapping `0` and `1`. -/
def s_12 (x : Fin 3) : Fin 3 :=
  if x.val = 0 then 1
  else if x.val = 1 then 0
  else 2

/-- The adjacent transposition swapping `1` and `2`. -/
def s_23 (x : Fin 3) : Fin 3 :=
  if x.val = 0 then 0
  else if x.val = 1 then 2
  else 1

/-- The cycle `0 -> 1 -> 2 -> 0`. -/
def s_123 (x : Fin 3) : Fin 3 :=
  if x.val = 0 then 1
  else if x.val = 1 then 2
  else 0

/-- The cycle `0 -> 2 -> 1 -> 0`. -/
def s_132 (x : Fin 3) : Fin 3 :=
  if x.val = 0 then 2
  else if x.val = 1 then 0
  else 1

/-- The transposition swapping `0` and `2`. -/
def s_13 (x : Fin 3) : Fin 3 :=
  if x.val = 0 then 2
  else if x.val = 1 then 1
  else 0

/-- The identity has Bruhat length `0`. -/
lemma len_s_e : inv_length 3 s_e = 0 := by
  decide

/-- The adjacent transposition `(0 1)` has Bruhat length `1`. -/
lemma len_s_12 : inv_length 3 s_12 = 1 := by
  decide

/-- The adjacent transposition `(1 2)` has Bruhat length `1`. -/
lemma len_s_23 : inv_length 3 s_23 = 1 := by
  decide

/-- The cycle `(0 1 2)` has Bruhat length `2`. -/
lemma len_s_123 : inv_length 3 s_123 = 2 := by
  decide

/-- The cycle `(0 2 1)` has Bruhat length `2`. -/
lemma len_s_132 : inv_length 3 s_132 = 2 := by
  decide

/-- The transposition `(0 2)` has Bruhat length `3`. -/
lemma len_s_13 : inv_length 3 s_13 = 3 := by
  decide

end InfoGeometry.Canonical.S3BruhatLengths
