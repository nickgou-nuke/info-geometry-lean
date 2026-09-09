import InfoGeometry.Quantum.KitaevPauliBraiding

namespace InfoGeometry.Quantum.KitaevChain

open Matrix

/-!
# Convention-fixed pairing of two Majorana modes

The displayed Kramers-pair formula is convention-sensitive.  This owner fixes
the convention by using the already verified four explicit Pauli Majoranas and
defines the two Dirac modes from them.  The resulting pairing identity is then
an ordinary matrix theorem; no Tomita, commutant, or BdG interpretation is
implicitly added.
-/

noncomputable section

def kramersDirac : Pauli4 :=
  (1 / 2 : ℂ) • (pauliMajorana 0 + Complex.I • pauliMajorana 1)

def kramersPartner : Pauli4 :=
  (1 / 2 : ℂ) • (pauliMajorana 2 + Complex.I • pauliMajorana 3)

def pairingOperator (Δ : ℝ) : Pauli4 :=
  (Δ : ℂ) •
    (kramersDirac.conjTranspose * kramersPartner.conjTranspose +
      kramersPartner * kramersDirac)

theorem kramers_pairing_expansion (Δ : ℝ) :
    pairingOperator Δ =
      (-Complex.I * (Δ : ℂ) / 2) •
        (pauliMajorana 0 * pauliMajorana 3 +
          pauliMajorana 1 * pauliMajorana 2) := by
  have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat (starRingEnd ℂ) 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairingOperator, kramersDirac, kramersPartner,
      pauliMajorana, pauliMajorana0, pauliMajorana1,
      pauliMajorana2, pauliMajorana3, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.conjTranspose_apply,
      Complex.I_mul_I, htwo]
  <;> norm_num
  <;> ring_nf
  <;> rw [Complex.I_sq]
  <;> ring_nf

theorem kramers_pairing_expansion_at_one :
    pairingOperator 1 =
      (-Complex.I / 2 : ℂ) •
        (pauliMajorana 0 * pauliMajorana 3 +
          pauliMajorana 1 * pauliMajorana 2) := by
  simpa using kramers_pairing_expansion 1

theorem pairingOperator_selfAdjoint (Δ : ℝ) :
    (pairingOperator Δ).conjTranspose = pairingOperator Δ := by
  simp [pairingOperator, kramersDirac, kramersPartner,
    Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_smul, pauliMajorana_selfAdjoint]
  <;> abel

end

end InfoGeometry.Quantum.KitaevChain
