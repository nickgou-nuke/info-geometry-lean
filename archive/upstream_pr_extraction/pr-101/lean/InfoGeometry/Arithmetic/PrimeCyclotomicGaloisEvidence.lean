import Mathlib

/-!
# Explicit CAS evidence rows for the prime cyclotomic tower

This file is the trust-boundary representation of data emitted by the companion
Sage/GAP scripts.  It contains values only, not imported proofs.  All arithmetic
and structural claims are reproved in `PrimeCyclotomicGaloisDirectedClosure`.
-/

namespace InfoGeometry.Arithmetic.PrimeCyclotomicGaloisEvidence

structure CASPrimeRow where
  prime : ℕ
  conductor : ℕ
  degree : ℕ
  deriving DecidableEq, Repr

/-- Rows generated externally for the cumulative prime sequence
`2,3,5,7,11,13`, with conductor the running product and degree Euler phi. -/
def casRow : Fin 6 → CASPrimeRow
  | 0 => ⟨2, 2, 1⟩
  | 1 => ⟨3, 6, 2⟩
  | 2 => ⟨5, 30, 8⟩
  | 3 => ⟨7, 210, 48⟩
  | 4 => ⟨11, 2310, 480⟩
  | 5 => ⟨13, 30030, 5760⟩

@[simp] theorem casRow_0 : casRow 0 = ⟨2, 2, 1⟩ := rfl
@[simp] theorem casRow_1 : casRow 1 = ⟨3, 6, 2⟩ := rfl
@[simp] theorem casRow_2 : casRow 2 = ⟨5, 30, 8⟩ := rfl
@[simp] theorem casRow_3 : casRow 3 = ⟨7, 210, 48⟩ := rfl
@[simp] theorem casRow_4 : casRow 4 = ⟨11, 2310, 480⟩ := rfl
@[simp] theorem casRow_5 : casRow 5 = ⟨13, 30030, 5760⟩ := rfl

end InfoGeometry.Arithmetic.PrimeCyclotomicGaloisEvidence
