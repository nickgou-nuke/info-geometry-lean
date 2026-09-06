import InfoGeometry.Exceptional.FreudenthalSymplecticTKKJacobiObstruction

/-!
# The symplectic rank-two operator is not the Freudenthal mixed triple

The existing `mixedSymplecticBracket` is the universal symplectic rank-two
operator.  This owner records a concrete obstruction to promoting it to the
mixed triple symmetry required by the TKK socket.  The witness uses only the
two scalar coordinates of a Freudenthal charge, so it is independent of any
Jordan multiplication or cubic-norm hypotheses.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

def alphaCharge : FreudenthalCharge J :=
  { alpha := 1, beta := 0, x := 0, y := 0 }

def betaCharge : FreudenthalCharge J :=
  { alpha := 0, beta := 1, x := 0, y := 0 }

theorem symplecticRankTwo_mixedTriple_counterexample :
    (mixedSymplecticBracket D (betaCharge (J := J)) (alphaCharge (J := J)) :
        Module.End ℝ (FreudenthalCharge J)) (alphaCharge (J := J)) ≠
      (mixedSymplecticBracket D (alphaCharge (J := J)) (alphaCharge (J := J)) :
        Module.End ℝ (FreudenthalCharge J)) (betaCharge (J := J)) := by
  intro h
  have hα := congrArg (fun Q : FreudenthalCharge J => Q.alpha) h
  simp [mixedSymplecticBracket_val, symplecticRankTwo_apply,
    alphaCharge, betaCharge, FreudenthalCharge.symplecticForm] at hα
  have hneg (Q : FreudenthalCharge J) : (-Q).alpha = -Q.alpha := by
    have hz := congrArg (fun R : FreudenthalCharge J => R.alpha) (add_neg_cancel Q)
    simpa [alpha_add] using (eq_neg_of_add_eq_zero_right hz)
  rw [hneg] at hα
  norm_num at hα

theorem tkk_mixed_jacobi_is_not_available_from_symplecticRankTwo :
    ¬ (∀ x z y : FreudenthalCharge J,
      (mixedSymplecticBracket D z y : Module.End ℝ (FreudenthalCharge J)) x =
        (mixedSymplecticBracket D x y : Module.End ℝ (FreudenthalCharge J)) z) := by
  intro h
  exact symplecticRankTwo_mixedTriple_counterexample D
    |>.elim (h (alphaCharge (J := J)) (betaCharge (J := J))
      (alphaCharge (J := J)))

end InfoGeometry.Exceptional.Freudenthal
