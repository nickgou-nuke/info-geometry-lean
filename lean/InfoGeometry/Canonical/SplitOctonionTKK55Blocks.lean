import InfoGeometry.Canonical.SplitOctonionTKK55

/-!
# Exhaustive hyperbolic block decomposition

This owner records the matrix form of the `(4,4)` pairing and the complete
three-block decomposition of its hyperbolic orthogonal endomorphisms.  The
source carrier is the independently defined `hyperbolicSkewSubmodule` from
`SplitOctonionTKK55`; no abstract quotient or property is used here.
-/

namespace InfoGeometry.Canonical.SplitOctonionTKK55Blocks

open SplitOctonionJordanForm
open SplitOctonionSkew28
open SplitOctonionTKK55

abbrev Middle := MiddleCarrier
abbrev Carrier := SplitOctonionTKK55.Carrier

def eta44Matrix : Matrix (Fin 8) (Fin 8) ℝ := eta44

def beta44Matrix (x y : Middle) : ℝ :=
  (eta44Matrix.mulVec x) ⬝ᵥ y

theorem beta44Matrix_eq (x y : Middle) :
    beta44Matrix x y = beta44 x y := by
  have h : beta44 x y =
      eta44Matrix.mulVec x ⬝ᵥ y := by
    simp [beta44, eta44Matrix, eta44, Matrix.mulVec, Matrix.mul_apply,
      Matrix.diagonal_apply, Finset.sum_ite_eq', dotProduct,
      Fin.sum_univ_succ]
  exact h.symm

theorem eta44Matrix_transpose : Matrix.transpose eta44Matrix = eta44Matrix := by
  exact SplitOctonionSkew28.eta44_transpose

theorem eta44Matrix_sq : eta44Matrix * eta44Matrix = 1 := by
  exact SplitOctonionSkew28.eta44_mul_self

theorem hyperbolic_P_form_skew (x : Middle) (u v : Carrier) :
    hyperbolicBeta (P x u) v + hyperbolicBeta u (P x v) = 0 := by
  exact P_hyperbolic_skew x u v

theorem hyperbolic_N_form_skew (y : Middle) (u v : Carrier) :
    hyperbolicBeta (N y u) v + hyperbolicBeta u (N y v) = 0 := by
  exact N_hyperbolic_skew y u v

def D (a : ℝ) (K : OrthogonalMiddle) (z : Carrier) : Carrier :=
  (a * z.1, (K.1.mulVec z.2.1, -a * z.2.2))

theorem hyperbolic_D_form_skew (a : ℝ) (K : OrthogonalMiddle)
    (u v : Carrier) :
    hyperbolicBeta (D a K u) v + hyperbolicBeta u (D a K v) = 0 := by
  rcases u with ⟨s, x, t⟩
  rcases v with ⟨r, y, q⟩
  change a * s * q + beta44 (K.1.mulVec x) y + (-a * t) * r +
      (s * (-a * q) + beta44 x (K.1.mulVec y) + t * (a * r)) = 0
  have hK := SplitOctonionSkew28.orthogonal44_beta_skew K x y
  linear_combination hK

theorem blockOperator_eq_P_add_D_add_N (d : BlockData) (z : Carrier) :
    blockOperator d z =
      P d.2.2.1 z + D d.1 d.2.1 z + N d.2.2.2 z := by
  rcases z with ⟨s, u, t⟩
  apply Prod.ext
  · simp [blockOperator, P, D, N]
    ring
  · apply Prod.ext
    · simp [blockOperator, P, D, N]
    · simp [blockOperator, P, D, N]
      ring

theorem P_bracket_P_apply (x y : Middle) (z : Carrier) :
    P x (P y z) - P y (P x z) = 0 := by
  exact P_commutator_zero x y z

theorem N_bracket_N_apply (x y : Middle) (z : Carrier) :
    N x (N y z) - N y (N x z) = 0 := by
  exact N_commutator_zero x y z

theorem P_bracket_N_apply (x y : Middle) (z : Carrier) :
    P x (N y z) - N y (P x z) =
      (beta44 y (z.1 • x),
        ((-beta44 y z.2.1) • x - (-beta44 x z.2.1) • y,
          -beta44 x (z.2.2 • y))) := by
  exact P_N_commutator_apply x y z

theorem D_bracket_P_apply_verified (a : ℝ) (K : OrthogonalMiddle)
    (x : Middle) (z : Carrier) :
    D a K (P x z) - P x (D a K z) =
      P (K.1.mulVec x - a • x) z := by
  rcases z with ⟨s, u, t⟩
  have hK := SplitOctonionSkew28.orthogonal44_beta_skew K x u
  dsimp [D, P]
  apply Prod.ext
  · simp [D, P]
  · apply Prod.ext
    · simp only [Prod.fst, Prod.snd]
      simp only [Matrix.mulVec_smul]
      module
    · simp only [Prod.fst, Prod.snd]
      simp only [sub_eq_add_neg, beta44_add_left]
      have hneg : beta44 (-(a • x)) u = -a * beta44 x u := by
        rw [← neg_smul, beta44_smul_left]
      rw [hneg]
      linear_combination hK

theorem D_bracket_N_apply (a : ℝ) (K : OrthogonalMiddle)
    (y : Middle) (z : Carrier) :
    D a K (N y z) - N y (D a K z) =
      N (K.1.mulVec y + a • y) z := by
  rcases z with ⟨s, u, t⟩
  have hK := SplitOctonionSkew28.orthogonal44_beta_skew K y u
  dsimp [D, N]
  apply Prod.ext
  · simp only [Prod.fst, Prod.snd]
    simp only [beta44_add_left, beta44_smul_left, smul_eq_mul]
    linear_combination hK
  · apply Prod.ext
    · simp only [Prod.fst, Prod.snd]
      simp only [Matrix.mulVec_smul]
      module
    · simp [D, N]

theorem D_bracket_D_apply (a b : ℝ) (K L : OrthogonalMiddle)
    (z : Carrier) :
    D a K (D b L z) - D b L (D a K z) =
      D 0 (SplitOctonionSkew28.orthogonal44Bracket K L) z := by
  rcases z with ⟨s, u, t⟩
  change
    (a * (b * s) - b * (a * s),
      ((K.1.mulVec (L.1.mulVec u) - L.1.mulVec (K.1.mulVec u)),
        (-a * (-b * t) - (-b * (-a * t))))) =
      (0 * s,
        ((K.1 * L.1 - L.1 * K.1).mulVec u, -0 * t))
  apply Prod.ext
  · ring
  · apply Prod.ext
    · simp only [Prod.fst, Prod.snd]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.sub_mulVec]
    · ring

def rankTwoMatrix (x y : Middle) : Matrix (Fin 8) (Fin 8) ℝ :=
  fun i j =>
    y i * (eta44Matrix.mulVec x) j -
      x i * (eta44Matrix.mulVec y) j

set_option maxHeartbeats 1000000 in
def rankTwoOrthogonal (x y : Middle) : OrthogonalMiddle :=
  ⟨rankTwoMatrix x y, by
    rw [mem_skewAdjointMatricesSubmodule]
    simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rankTwoMatrix, eta44Matrix, eta44, Matrix.mul_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
        Matrix.transpose_apply]
      <;> ring⟩

theorem rankTwoOrthogonal_apply (x y z : Middle) :
    (rankTwoOrthogonal x y).1.mulVec z =
      beta44 x z • y - beta44 y z • x := by
  ext i
  simp [rankTwoOrthogonal, rankTwoMatrix, beta44, eta44Matrix,
    eta44, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]
  ring

theorem hyperbolic_block_exists (T : hyperbolicSkewSubmodule) :
    ∃ d : BlockData, blockOperator d = T.1 := by
  obtain ⟨d, hd⟩ := blockOperatorLinearSubmodule_surjective T
  exact ⟨d, congrArg Subtype.val hd⟩

theorem hyperbolic_block_unique (d e : BlockData)
    (h : blockOperator d = blockOperator e) : d = e := by
  exact blockOperatorLinear_injective h

theorem hyperbolic_block_decomposition (T : hyperbolicSkewSubmodule) :
    ∃! d : BlockData, blockOperator d = T.1 := by
  obtain ⟨d, hd⟩ := hyperbolic_block_exists T
  refine ⟨d, hd, ?_⟩
  intro e he
  exact (hyperbolic_block_unique d e (hd.trans he.symm)).symm

theorem hyperbolic_block_finrank :
    Module.finrank ℝ hyperbolicSkewSubmodule = 45 := by
  exact hyperbolicSkewSubmodule_finrank

end InfoGeometry.Canonical.SplitOctonionTKK55Blocks
