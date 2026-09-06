import InfoGeometry.Canonical.QutritWeylOperatorBasis

/-!
# The four commuting Weyl lines of the qutrit Pauli plane

The four directions are represented by the generators `X`, `Z`, `XZ`, and
`XZ²`.  This owner proves the commuting-line statement only.  It does not
promote these lines to mutually unbiased bases; that requires a separate
normalized eigenvector and overlap theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.QutritWeylCommutingLines

open InfoGeometry.Canonical.QutritWeylOperatorBasis

abbrev QutritMatrix := Matrix (Fin 3) (Fin 3) ℂ

def commutingWeylGenerator : Fin 4 → QutritMatrix := ![
  weylWord 1 0,
  weylWord 0 1,
  weylWord 1 1,
  weylWord 1 2
]

def commutingWeylLineWord (g : Fin 4) (t : Fin 3) : QutritMatrix :=
  (commutingWeylGenerator g) ^ (t : ℕ)

theorem commutingWeylLine_commute (g : Fin 4) (r s : Fin 3) :
    Commute (commutingWeylLineWord g r) (commutingWeylLineWord g s) := by
  dsimp [commutingWeylLineWord]
  change commutingWeylGenerator g ^ (r : ℕ) *
      commutingWeylGenerator g ^ (s : ℕ) =
    commutingWeylGenerator g ^ (s : ℕ) *
      commutingWeylGenerator g ^ (r : ℕ)
  rw [← pow_add, add_comm, pow_add]

theorem commutingWeylLine_zero (g : Fin 4) :
    commutingWeylLineWord g 0 = (1 : QutritMatrix) := by
  simp [commutingWeylLineWord]

theorem commutingWeylLine_card : Fintype.card (Fin 4) = 4 := by
  decide

end InfoGeometry.Canonical.QutritWeylCommutingLines
end noncomputable section
