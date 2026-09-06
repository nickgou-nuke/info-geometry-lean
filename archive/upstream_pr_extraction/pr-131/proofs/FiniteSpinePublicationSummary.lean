import proofs.ThermodynamicNetworkSpine
import proofs.ColorParafermionCuntzBusSpine

/-!
# Finite spine publication summary

Small standalone facts selected from the thermodynamic, BKB, color, and Cuntz
modules.
-/

noncomputable section

namespace FiniteSpinePublicationSummary

/-- The finite TKK grading has zero formal chiral parity index. -/
lemma tkk_chiral_parity_index_zero :
    ThermodynamicTKKBridge.formalChiralParityIndex = 0 := by
  unfold ThermodynamicTKKBridge.formalChiralParityIndex
  decide

/-- Applying the BKB fold twice returns the original momentum point. -/
lemma bkb_fold_twice
    (k : NonAbelianBrillouinKleinBottle.MomentumPoint) :
    NonAbelianBrillouinKleinBottle.bkbFold
      (NonAbelianBrillouinKleinBottle.bkbFold k) = k := by
  cases k
  simp [NonAbelianBrillouinKleinBottle.bkbFold]

/-- Applying the BKB lane transition twice returns the original lane. -/
lemma bkb_lane_transition_twice
    (ψ : TopologicalAndreevPump.ParafermionLane) :
    NonAbelianBrillouinKleinBottle.bkbLaneTransition
      (NonAbelianBrillouinKleinBottle.bkbLaneTransition ψ) = ψ := by
  rw [NonAbelianBrillouinKleinBottle.bkbLaneTransition]
  simp only [TopologicalAndreevPump.modularJLane_involutive]

/-- In every Bogoliubov frame the affine even-even bracket recovers `[lambda1,lambda2]`. -/
lemma affine_gl1_gl2_commutator
    (F : BogoliubovWeylChemicalPotential.BogoliubovInertialFrame) :
    SupergradedCuntzBdG.affineSuperBracket
      (BogoliubovWeylChemicalPotential.frameWeylQ F)
      SupergradedCuntzBdG.Z2Parity.even SupergradedCuntzBdG.Z2Parity.even
      GellMannSU3.gl1 GellMannSU3.gl2 =
        (2 * Complex.I) • GellMannSU3.gl3 := by
  rw [BogoliubovSU3ParafermionWeld.frame_affine_even_even_lie]
  simpa [SupergradedCuntzBdG.lieBracket] using GellMannSU3.gl1_comm_gl2

/-- The zeroth Cuntz quotient generator is a left inverse of its partner. -/
lemma cuntz_left_inverse_zero :
    AlgebraicCuntzQuotient.T (R := ℂ) (0 : Fin 4) *
        AlgebraicCuntzQuotient.S (R := ℂ) (0 : Fin 4) = 1 := by
  calc
    AlgebraicCuntzQuotient.T (R := ℂ) (0 : Fin 4) *
        AlgebraicCuntzQuotient.S (R := ℂ) (0 : Fin 4) =
        if (0 : Fin 4) = (0 : Fin 4) then 1 else 0 := by
      rw [AlgebraicCuntzQuotient.T_mul_S]
    _ = 1 := by
      simp only [↓reduceIte]

/-- The four-generator algebraic Cuntz quotient has the defining partition relation. -/
lemma cuntz_partition_four :
    (∑ i : Fin 4,
        AlgebraicCuntzQuotient.S (R := ℂ) i *
          AlgebraicCuntzQuotient.T (R := ℂ) i) = 1 := by
  simpa using AlgebraicCuntzQuotient.partition_one (R := ℂ) (ι := Fin 4)

end FiniteSpinePublicationSummary

end noncomputable section
