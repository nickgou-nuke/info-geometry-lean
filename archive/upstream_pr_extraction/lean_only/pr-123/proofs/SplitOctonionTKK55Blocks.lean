import proofs.SplitOctonionTKK55
import proofs.SplitOctonionJordanForm

/-!
# Hyperbolic block model for the split TKK carrier

The middle space is `R^8` with diagonal `(4,4)` form.  The two endpoint
lines are paired hyperbolically, giving the `(5,5)` form on
`R ⊕ R^8 ⊕ R`.
-/

noncomputable section
namespace SplitOctonionTKK55Blocks

inductive HIndex where
  | minus
  | middle (i : Fin 8)
  | plus
  deriving DecidableEq, Fintype

abbrev HMatrix := Matrix HIndex HIndex ℝ
abbrev HVector := Fin 8 → ℝ

/-- Matrix of the normalized middle `(4,4)` form. -/
def eta44 : Matrix (Fin 8) (Fin 8) ℝ :=
  Matrix.diagonal (fun i => if i.val < 4 then 1 else -1)

def beta44Matrix (x y : HVector) : ℝ :=
  dotProduct x (eta44.mulVec y)

/-- The `(4,4)` diagonal bilinear form on the middle carrier. -/
def beta44 (x y : HVector) : ℝ :=
  ∑ i : Fin 8, (if i.val < 4 then 1 else -1) * x i * y i

/-- The covector associated to a middle vector. -/
def flat (x : HVector) : Fin 8 → ℝ :=
  fun i => (if i.val < 4 then 1 else -1) * x i

theorem eta44_transpose : eta44.transpose = eta44 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [eta44]
  · simp [eta44, h, Ne.symm h]

theorem eta44_mul_self : eta44 * eta44 = (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eta44, Matrix.mul_apply, Fin.sum_univ_succ]

theorem beta44_eq_matrix (x y : HVector) :
    beta44 x y = beta44Matrix x y := by
  simp [beta44, beta44Matrix, eta44, dotProduct, Matrix.mulVec,
    Fin.sum_univ_succ]

theorem beta44_symmetric (x y : HVector) : beta44 x y = beta44 y x := by
  simp [beta44, mul_comm, mul_left_comm]

/-- Hyperbolic extension of the middle metric. -/
def metric55 : HMatrix
  | .minus, .plus => 1
  | .plus, .minus => 1
  | .middle i, .middle j => if i = j then if i.val < 4 then 1 else -1 else 0
  | _, _ => 0

/-- The actual orthogonality equation for the hyperbolic block model. -/
def hyperbolicOrthogonal (A : HMatrix) : Prop :=
  A.transpose * metric55 + metric55 * A = 0

/-- Positive grade-one translation block. -/
def P (x : HVector) : HMatrix
  | .middle i, .minus => x i
  | .plus, .middle i => -(flat x i)
  | _, _ => 0

/-- Negative grade-one special-conformal block. -/
def N (y : HVector) : HMatrix
  | .minus, .middle i => -(flat y i)
  | .middle i, .plus => y i
  | _, _ => 0

/-- Degree-zero orthogonal block with scalar dilation. -/
def D (a : ℝ) (K : Matrix (Fin 8) (Fin 8) ℝ) : HMatrix
  | .minus, .minus => a
  | .middle i, .middle j => K i j
  | .plus, .plus => -a
  | _, _ => 0

/-- Eliminate a finite sum over the hyperbolic endpoint/middle carrier. -/
theorem sum_HIndex {R : Type*} [AddCommMonoid R] (f : HIndex → R) :
    (∑ k : HIndex, f k) =
      f .minus + f .plus + ∑ i : Fin 8, f (.middle i) := by
  have huniv : (Finset.univ : Finset HIndex) =
      {.minus, .plus} ∪ Finset.univ.image HIndex.middle := by
    ext k
    cases k <;> simp
  change Finset.sum (Finset.univ : Finset HIndex) f = _
  rw [huniv]
  simp
  rw [Finset.sum_image]
  · simp [add_assoc]
  · intro i _ j _ hij
    exact HIndex.middle.inj hij

theorem beta44_flat (x y : HVector) :
    ∑ i : Fin 8, flat x i * y i = beta44 x y := by
  simp [flat, beta44, mul_assoc, mul_left_comm, mul_comm]

theorem P_hyperbolicOrthogonal (x : HVector) :
    hyperbolicOrthogonal (P x) := by
  unfold hyperbolicOrthogonal
  ext r c
  cases r <;> cases c <;>
    simp [P, metric55, flat, Matrix.mul_apply, sum_HIndex]

theorem N_hyperbolicOrthogonal (y : HVector) :
    hyperbolicOrthogonal (N y) := by
  unfold hyperbolicOrthogonal
  ext r c
  cases r <;> cases c <;>
    simp [N, metric55, flat, Matrix.mul_apply, sum_HIndex]

/-- The middle block is orthogonal when it is skew for `beta44`. -/
def betaSkew (K : Matrix (Fin 8) (Fin 8) ℝ) : Prop :=
  ∀ i j, (if i.val < 4 then 1 else -1) * K i j =
    -((if j.val < 4 then 1 else -1) * K j i)

theorem D_hyperbolicOrthogonal {a : ℝ} {K : Matrix (Fin 8) (Fin 8) ℝ}
    (hK : betaSkew K) :
    hyperbolicOrthogonal (D a K) := by
  unfold hyperbolicOrthogonal
  ext r c
  cases r <;> cases c <;>
    simp [D, metric55, Matrix.mul_apply, sum_HIndex]
  all_goals
    rename_i i j
    have hk := hK i j
    split_ifs at hk ⊢ <;> linarith

/-- The endpoint/middle matrices have the expected TKK grades. -/
def gradeOf : HIndex → ℤ
  | .minus => (-1 : ℤ)
  | .middle _ => 0
  | .plus => 1

def gradeSupport (g : ℤ) (A : HMatrix) : Prop :=
  ∀ r c, gradeOf r - gradeOf c ≠ g → A r c = 0

theorem P_grade_one (x : HVector) : gradeSupport 1 (P x) := by
  intro r c h
  cases r <;> cases c <;> simp [P, gradeOf] at h ⊢

theorem N_grade_minus_one (y : HVector) : gradeSupport (-1) (N y) := by
  intro r c h
  cases r <;> cases c <;> simp [N, gradeOf] at h ⊢

theorem D_grade_zero (a : ℝ) (K : Matrix (Fin 8) (Fin 8) ℝ) :
    gradeSupport 0 (D a K) := by
  intro r c h
  cases r <;> cases c <;> simp [D, gradeOf] at h ⊢

/-- Coordinates for the three block grades of the hyperbolic carrier. -/
structure BlockData where
  x : HVector
  a : ℝ
  K : Matrix (Fin 8) (Fin 8) ℝ
  y : HVector

/-- Assemble the three supported block grades. -/
def assemble (b : BlockData) : HMatrix :=
  P b.x + D b.a b.K + N b.y

theorem assemble_injective : Function.Injective assemble := by
  intro b c h
  have hx : b.x = c.x := by
    funext i
    have hi := congrArg (fun A : HMatrix => A (.middle i) .minus) h
    simpa [assemble, P, D, N] using hi
  have ha : b.a = c.a := by
    have hi := congrArg (fun A : HMatrix => A .minus .minus) h
    simpa [assemble, P, D, N] using hi
  have hK : b.K = c.K := by
    funext i j
    have hij := congrArg (fun A : HMatrix => A (.middle i) (.middle j)) h
    simpa [assemble, P, D, N] using hij
  have hy : b.y = c.y := by
    funext i
    have hi := congrArg (fun A : HMatrix => A (.middle i) .plus) h
    simpa [assemble, P, D, N] using hi
  cases b
  cases c
  simp_all

/-- Extract the four visible blocks from a hyperbolic matrix. -/
def disassemble (A : HMatrix) : BlockData where
  x i := A (.middle i) .minus
  a := A .minus .minus
  K i j := A (.middle i) (.middle j)
  y i := A (.middle i) .plus

theorem disassemble_assemble (b : BlockData) : disassemble (assemble b) = b := by
  cases b
  simp [disassemble, assemble, P, D, N]

/-- The orthogonality equation determines every endpoint and middle block. -/
theorem hyperbolicOrthogonal_entry_constraints {A : HMatrix}
    (hA : hyperbolicOrthogonal A) :
    (A .minus .plus = 0) ∧
    (A .plus .minus = 0) ∧
    (A .plus .plus = -A .minus .minus) ∧
    (∀ i, A .minus (.middle i) = -(flat (disassemble A).y i)) ∧
    (∀ i, A .plus (.middle i) = -(flat (disassemble A).x i)) ∧
    betaSkew (disassemble A).K := by
  unfold hyperbolicOrthogonal at hA
  have entry (r c : HIndex) := congrArg (fun M : HMatrix => M r c) hA
  constructor
  · simpa [metric55, Matrix.mul_apply, sum_HIndex] using entry .plus .plus
  constructor
  · simpa [metric55, Matrix.mul_apply, sum_HIndex] using entry .minus .minus
  constructor
  · have h := entry .minus .plus
    simp [metric55, Matrix.mul_apply, sum_HIndex] at h
    linarith
  constructor
  · intro i
    have h := entry (.middle i) .plus
    simp [flat, disassemble, metric55, Matrix.mul_apply, sum_HIndex] at h ⊢
    split_ifs at h ⊢ <;> linarith
  constructor
  · intro i
    have h := entry (.middle i) .minus
    simp [flat, disassemble, metric55, Matrix.mul_apply, sum_HIndex] at h ⊢
    split_ifs at h ⊢ <;> linarith
  · intro i j
    have hij := entry (.middle i) (.middle j)
    simp [disassemble, metric55, Matrix.mul_apply, sum_HIndex] at hij
    unfold disassemble
    split_ifs at hij ⊢ <;> linarith

/-- Exhaustiveness of the `P + D + N` block form. -/
theorem assemble_disassemble_of_hyperbolicOrthogonal {A : HMatrix}
    (hA : hyperbolicOrthogonal A) : assemble (disassemble A) = A := by
  rcases hyperbolicOrthogonal_entry_constraints hA with
    ⟨hmp, hpm, hpp, hmy, hpx, hK⟩
  ext r c
  cases r <;> cases c <;>
    simp [assemble, disassemble, P, D, N, hmp, hpm, hpp, hmy, hpx]

/-- The extracted middle block is genuinely `(4,4)`-skew. -/
theorem disassemble_betaSkew {A : HMatrix} (hA : hyperbolicOrthogonal A) :
    betaSkew (disassemble A).K :=
  (hyperbolicOrthogonal_entry_constraints hA).2.2.2.2.2

/-- Matrix commutator on the hyperbolic carrier. -/
def hBracket (A B : HMatrix) : HMatrix := A * B - B * A

/-- The rank-two `(4,4)`-skew operator occurring in `[P(x),N(y)]`. -/
def rankTwo (x y : HVector) : Matrix (Fin 8) (Fin 8) ℝ :=
  fun i j => y i * flat x j - x i * flat y j

theorem rankTwo_betaSkew (x y : HVector) : betaSkew (rankTwo x y) := by
  intro i j
  simp [rankTwo, flat]
  split_ifs <;> ring

theorem P_P_bracket (x z : HVector) : hBracket (P x) (P z) = 0 := by
  ext r c
  cases r <;> cases c <;>
    simp [hBracket, P, Matrix.mul_apply, sum_HIndex]
  all_goals
    have hs : (∑ i : Fin 8, flat x i * z i) =
        ∑ i : Fin 8, flat z i * x i := by
      rw [beta44_flat, beta44_flat, beta44_symmetric]
    rw [hs]
    ring

theorem N_N_bracket (y w : HVector) : hBracket (N y) (N w) = 0 := by
  ext r c
  cases r <;> cases c <;>
    simp [hBracket, N, Matrix.mul_apply, sum_HIndex]
  all_goals
    have hs : (∑ i : Fin 8, flat y i * w i) =
        ∑ i : Fin 8, flat w i * y i := by
      rw [beta44_flat, beta44_flat, beta44_symmetric]
    rw [hs]
    ring

theorem P_N_bracket (x y : HVector) :
    hBracket (P x) (N y) = D (beta44 x y) (rankTwo x y) := by
  ext r c
  cases r <;> cases c <;>
    simp [hBracket, P, N, D, rankTwo, Matrix.mul_apply, sum_HIndex,
      beta44_flat, beta44_symmetric]
  all_goals ring

def matVec (K : Matrix (Fin 8) (Fin 8) ℝ) (x : HVector) : HVector :=
  K.mulVec x

private theorem hBracket_orthogonal {A B : HMatrix}
    (hA : hyperbolicOrthogonal A) (hB : hyperbolicOrthogonal B) :
    hyperbolicOrthogonal (hBracket A B) := by
  unfold hyperbolicOrthogonal hBracket at *
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul]
  have hA' : A.transpose * metric55 = -(metric55 * A) := by
    apply eq_neg_of_add_eq_zero_left
    exact hA
  have hB' : B.transpose * metric55 = -(metric55 * B) := by
    apply eq_neg_of_add_eq_zero_left
    exact hB
  rw [sub_mul, mul_sub]
  rw [Matrix.mul_assoc B.transpose A.transpose metric55,
    Matrix.mul_assoc A.transpose B.transpose metric55, hA', hB']
  rw [mul_neg, mul_neg]
  rw [← Matrix.mul_assoc B.transpose metric55 A, hB',
    ← Matrix.mul_assoc A.transpose metric55 B, hA']
  noncomm_ring

theorem hyperbolicOrthogonal_ext {A B : HMatrix}
    (hA : hyperbolicOrthogonal A) (hB : hyperbolicOrthogonal B)
    (h : disassemble A = disassemble B) : A = B := by
  rw [← assemble_disassemble_of_hyperbolicOrthogonal hA,
    ← assemble_disassemble_of_hyperbolicOrthogonal hB, h]

theorem D_P_bracket {a : ℝ} {K : Matrix (Fin 8) (Fin 8) ℝ}
    (hK : betaSkew K) (x : HVector) :
    hBracket (D a K) (P x) = P (matVec K x - a • x) := by
  apply hyperbolicOrthogonal_ext
  · exact hBracket_orthogonal (D_hyperbolicOrthogonal hK)
      (P_hyperbolicOrthogonal x)
  · exact P_hyperbolicOrthogonal _
  · simp [disassemble, hBracket, D, P, matVec, Matrix.mul_apply,
      Matrix.mulVec, sum_HIndex]
    funext i
    simp [dotProduct]
    ring

theorem D_N_bracket {a : ℝ} {K : Matrix (Fin 8) (Fin 8) ℝ}
    (hK : betaSkew K) (y : HVector) :
    hBracket (D a K) (N y) = N (matVec K y + a • y) := by
  apply hyperbolicOrthogonal_ext
  · exact hBracket_orthogonal (D_hyperbolicOrthogonal hK)
      (N_hyperbolicOrthogonal y)
  · exact N_hyperbolicOrthogonal _
  · simp [disassemble, hBracket, D, N, matVec, Matrix.mul_apply,
      Matrix.mulVec, sum_HIndex]
    funext i
    simp [dotProduct]
    ring

/-- Full spin-factor Jordan triple on the common real carrier. -/
def spinFactorTriple (x y z : HVector) : HVector :=
  beta44 x y • z + beta44 z y • x - beta44 x z • y

theorem rankTwo_mulVec (x y z : HVector) :
    matVec (rankTwo x y) z =
      beta44 x z • y - beta44 y z • x := by
  funext i
  simp [matVec, rankTwo, Matrix.mulVec, dotProduct, ← beta44_flat]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem mixed_double_bracket (x y z : HVector) :
    hBracket (hBracket (N y) (P x)) (P z) =
      P (spinFactorTriple x y z) := by
  have hNP : hBracket (N y) (P x) =
      -(D (beta44 x y) (rankTwo x y)) := by
    rw [show hBracket (N y) (P x) = -hBracket (P x) (N y) by
      unfold hBracket; noncomm_ring, P_N_bracket]
  rw [hNP]
  rw [show hBracket (-(D (beta44 x y) (rankTwo x y))) (P z) =
      -(hBracket (D (beta44 x y) (rankTwo x y)) (P z)) by
    unfold hBracket; noncomm_ring]
  rw [D_P_bracket (rankTwo_betaSkew x y), rankTwo_mulVec]
  rw [show -(P (beta44 x z • y - beta44 y z • x - beta44 x y • z)) =
      P (-(beta44 x z • y - beta44 y z • x - beta44 x y • z)) by
    ext r c; cases r <;> cases c <;> simp [P, flat]
    all_goals split_ifs <;> ring]
  apply congrArg P
  funext i
  simp [spinFactorTriple]
  rw [beta44_symmetric z y]
  ring

theorem D_D_bracket (a b : ℝ) (K L : Matrix (Fin 8) (Fin 8) ℝ) :
    hBracket (D a K) (D b L) = D 0 (K * L - L * K) := by
  ext r c
  cases r <;> cases c <;>
    simp [hBracket, D, Matrix.mul_apply, sum_HIndex]
  all_goals ring_nf

/-- The constrained orthogonal carrier is closed under commutators. -/
theorem hBracket_hyperbolicOrthogonal {A B : HMatrix}
    (hA : hyperbolicOrthogonal A) (hB : hyperbolicOrthogonal B) :
    hyperbolicOrthogonal (hBracket A B) := by
  exact hBracket_orthogonal hA hB

end SplitOctonionTKK55Blocks

end noncomputable section
