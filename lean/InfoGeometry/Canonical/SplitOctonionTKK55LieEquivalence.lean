import InfoGeometry.Canonical.SplitOctonionTKK55Blocks

/-!
# Independent component TKK bracket

The source bracket below is defined from the `(x,a,K,y)` component formula.
The matrix carrier is used only as the target of the bracket-preservation
theorem; it is not used to define the source operation.
-/

namespace InfoGeometry.Canonical.SplitOctonionTKK55LieEquivalence

open SplitOctonionJordanForm
open SplitOctonionSkew28
open SplitOctonionTKK55
open SplitOctonionTKK55Blocks

abbrev TKKCarrier := BlockData
abbrev TKKMiddle := SplitOctonionTKK55.Middle

def tkkBracket (d e : TKKCarrier) : TKKCarrier :=
  let a := d.1
  let K := d.2.1
  let x := d.2.2.1
  let y := d.2.2.2
  let b := e.1
  let L := e.2.1
  let u := e.2.2.1
  let v := e.2.2.2
  (beta44 x v - beta44 u y,
    (orthogonal44Bracket K L +
        rankTwoOrthogonal x v - rankTwoOrthogonal u y,
      (K.1.mulVec u - L.1.mulVec x - a • u + b • x,
        K.1.mulVec v - L.1.mulVec y + a • v - b • y)))

theorem tkkBracket_apply (d e : TKKCarrier) :
    tkkBracket d e =
      (beta44 d.2.2.1 e.2.2.2 - beta44 e.2.2.1 d.2.2.2,
        (orthogonal44Bracket d.2.1 e.2.1 +
            rankTwoOrthogonal d.2.2.1 e.2.2.2 -
              rankTwoOrthogonal e.2.2.1 d.2.2.2,
          (d.2.1.1.mulVec e.2.2.1 - e.2.1.1.mulVec d.2.2.1 -
              d.1 • e.2.2.1 + e.1 • d.2.2.1,
            d.2.1.1.mulVec e.2.2.2 - e.2.1.1.mulVec d.2.2.2 +
              d.1 • e.2.2.2 - e.1 • d.2.2.2))) := by
  rfl

def dMap (a : ℝ) (K : OrthogonalMiddle) :
    Module.End ℝ SplitOctonionTKK55.Carrier where
  toFun := D a K
  map_add' z w := by
    rcases z with ⟨s, x, t⟩
    rcases w with ⟨r, y, q⟩
    change (a * (s + r), ((K.1).mulVec (x + y), -a * (t + q))) =
      (a * s + a * r,
        (K.1.mulVec x + K.1.mulVec y, -a * t + -a * q))
    apply Prod.ext
    · change a * (s + r) = a * s + a * r
      ring
    · apply Prod.ext
      · change K.1.mulVec (x + y) = K.1.mulVec x + K.1.mulVec y
        rw [Matrix.mulVec_add]
      · change -a * (t + q) = -a * t + -a * q
        ring
  map_smul' r z := by
    rcases z with ⟨s, x, t⟩
    change (a * (r * s), ((K.1).mulVec (r • x), -a * (r * t))) =
      (r * (a * s), (r • (K.1.mulVec x), r * (-a * t)))
    apply Prod.ext
    · change a * (r * s) = r * (a * s)
      ring
    · apply Prod.ext
      · change K.1.mulVec (r • x) = r • K.1.mulVec x
        rw [Matrix.mulVec_smul]
      · change -a * (r * t) = r * (-a * t)
        ring

theorem dMap_apply (a : ℝ) (K : OrthogonalMiddle)
    (z : SplitOctonionTKK55.Carrier) :
    dMap a K z = D a K z := rfl

theorem blockOperator_decomposition (d : TKKCarrier) :
    blockOperator d =
      pMap d.2.2.1 + dMap d.1 d.2.1 + nMap d.2.2.2 := by
  apply LinearMap.ext
  intro z
  rw [blockOperator_eq_P_add_D_add_N]
  simp [pMap_apply, nMap_apply, dMap_apply]

theorem p_comm (x u : TKKMiddle) :
    pMap x * pMap u - pMap u * pMap x = 0 := by
  apply LinearMap.ext
  intro z
  simpa [Module.End.mul_apply, pMap_apply] using P_bracket_P_apply x u z

theorem n_comm (y v : TKKMiddle) :
    nMap y * nMap v - nMap v * nMap y = 0 := by
  apply LinearMap.ext
  intro z
  simpa [Module.End.mul_apply, nMap_apply] using N_bracket_N_apply y v z

theorem d_p_comm (a : ℝ) (K : OrthogonalMiddle) (u : TKKMiddle) :
    dMap a K * pMap u - pMap u * dMap a K =
      pMap (K.1.mulVec u - a • u) := by
  apply LinearMap.ext
  intro z
  change D a K (P u z) - P u (D a K z) =
    P (K.1.mulVec u - a • u) z
  exact D_bracket_P_apply_verified a K u z

theorem d_n_comm (a : ℝ) (K : OrthogonalMiddle) (v : TKKMiddle) :
    dMap a K * nMap v - nMap v * dMap a K =
      nMap (K.1.mulVec v + a • v) := by
  apply LinearMap.ext
  intro z
  change D a K (N v z) - N v (D a K z) =
    N (K.1.mulVec v + a • v) z
  exact D_bracket_N_apply a K v z

theorem d_d_comm (a b : ℝ) (K L : OrthogonalMiddle) :
    dMap a K * dMap b L - dMap b L * dMap a K =
      dMap 0 (orthogonal44Bracket K L) := by
  apply LinearMap.ext
  intro z
  simpa [Module.End.mul_apply, dMap_apply] using
    D_bracket_D_apply a b K L z

theorem p_n_comm (x v : TKKMiddle) :
    pMap x * nMap v - nMap v * pMap x =
      dMap (beta44 x v) (rankTwoOrthogonal x v) := by
  apply LinearMap.ext
  intro z
  change P x (N v z) - N v (P x z) =
    D (beta44 x v) (rankTwoOrthogonal x v) z
  rcases z with ⟨s, w, t⟩
  rw [P_bracket_N_apply]
  simp [D, rankTwoOrthogonal_apply, smul_eq_mul]
  constructor
  · ring
  · constructor
    · ext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · ring

theorem p_d_comm (x : TKKMiddle) (b : ℝ) (L : OrthogonalMiddle) :
    pMap x * dMap b L - dMap b L * pMap x =
      -pMap (L.1.mulVec x - b • x) := by
  calc
    pMap x * dMap b L - dMap b L * pMap x =
        -(dMap b L * pMap x - pMap x * dMap b L) := by
          noncomm_ring
    _ = -pMap (L.1.mulVec x - b • x) := by rw [d_p_comm]

theorem n_p_comm (y : TKKMiddle) (u : TKKMiddle) :
    nMap y * pMap u - pMap u * nMap y =
      -dMap (beta44 u y) (rankTwoOrthogonal u y) := by
  calc
    nMap y * pMap u - pMap u * nMap y =
        -(pMap u * nMap y - nMap y * pMap u) := by
          noncomm_ring
    _ = -dMap (beta44 u y) (rankTwoOrthogonal u y) := by rw [p_n_comm]

theorem n_d_comm (y : TKKMiddle) (b : ℝ) (L : OrthogonalMiddle) :
    nMap y * dMap b L - dMap b L * nMap y =
      -nMap (L.1.mulVec y + b • y) := by
  calc
    nMap y * dMap b L - dMap b L * nMap y =
        -(dMap b L * nMap y - nMap y * dMap b L) := by
          noncomm_ring
    _ = -nMap (L.1.mulVec y + b • y) := by rw [d_n_comm]

theorem block_commutator_expansion (a b : ℝ)
    (K L : OrthogonalMiddle) (x y u v : TKKMiddle) :
    blockOperator (a, (K, (x, y))) * blockOperator (b, (L, (u, v))) -
        blockOperator (b, (L, (u, v))) * blockOperator (a, (K, (x, y))) =
      (pMap x * pMap u - pMap u * pMap x) +
      (pMap x * dMap b L - dMap b L * pMap x) +
      (pMap x * nMap v - nMap v * pMap x) +
      (dMap a K * pMap u - pMap u * dMap a K) +
      (dMap a K * dMap b L - dMap b L * dMap a K) +
      (dMap a K * nMap v - nMap v * dMap a K) +
      (nMap y * pMap u - pMap u * nMap y) +
      (nMap y * dMap b L - dMap b L * nMap y) +
      (nMap y * nMap v - nMap v * nMap y) := by
  rw [blockOperator_decomposition, blockOperator_decomposition]
  noncomm_ring

theorem tkkCarrier_finrank_eq_45 :
    Module.finrank ℝ TKKCarrier = 45 := by
  exact blockData_finrank

theorem hyperbolicSO55_finrank_eq_45 :
    Module.finrank ℝ hyperbolicSkewSubmodule = 45 := by
  exact hyperbolicSkewSubmodule_finrank

set_option maxHeartbeats 1000000 in
theorem blockOperator_tkkBracket (d e : TKKCarrier) :
    blockOperator (tkkBracket d e) =
      blockOperator d * blockOperator e - blockOperator e * blockOperator d := by
  rcases d with ⟨a, K, x, y⟩
  rcases e with ⟨b, L, u, v⟩
  rw [blockOperator_decomposition, block_commutator_expansion]
  rw [p_comm, p_d_comm, p_n_comm, d_p_comm, d_d_comm, d_n_comm,
    n_p_comm, n_d_comm, n_comm]
  apply LinearMap.ext
  intro z
  rcases z with ⟨s, w, t⟩
  have hM :
      (orthogonal44Bracket K L + rankTwoOrthogonal x v -
        rankTwoOrthogonal u y).1.mulVec w =
        (orthogonal44Bracket K L).1.mulVec w +
        (rankTwoOrthogonal x v).1.mulVec w -
            (rankTwoOrthogonal u y).1.mulVec w := by
    ext i
    change (∑ j, ((orthogonal44Bracket K L).1 i j +
      (rankTwoOrthogonal x v).1 i j - (rankTwoOrthogonal u y).1 i j) * w j) = _
    calc
      (∑ j, ((orthogonal44Bracket K L).1 i j +
        (rankTwoOrthogonal x v).1 i j - (rankTwoOrthogonal u y).1 i j) * w j) =
          ∑ j, (((orthogonal44Bracket K L).1 i j * w j +
            (rankTwoOrthogonal x v).1 i j * w j) -
              (rankTwoOrthogonal u y).1 i j * w j) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        simp [Matrix.mulVec, dotProduct]
  simp only [tkkBracket, LinearMap.map_sub, LinearMap.map_add,
    LinearMap.map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.zero_apply, LinearMap.neg_apply,
    dMap_apply, pMap_apply, nMap_apply, D, P, N]
  rw [hM]
  simp
  constructor
  · ring
  · constructor
    · ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
        smul_eq_mul]
      ring
    · ring

theorem tkkBracket_eq_abstractTKKBracket (d e : TKKCarrier) :
    tkkBracket d e = abstractTKKBracket d e := by
  apply blockOperatorLinearSubmodule_injective
  change blockOperatorLinearSubmoduleEquiv (tkkBracket d e) =
    blockOperatorLinearSubmoduleEquiv (abstractTKKBracket d e)
  rw [abstractTKKBracket_equiv]
  apply Subtype.ext
  exact blockOperator_tkkBracket d e

noncomputable def tkkHyperbolicLieEquiv :
    TKKCarrier ≃ₗ⁅ℝ⁆ hyperbolicSkewSubmodule :=
  abstractTKKLieEquiv

theorem tkkHyperbolicLieEquiv_map_tkkBracket (d e : TKKCarrier) :
    tkkHyperbolicLieEquiv (tkkBracket d e) =
      hyperbolicSkewBracket
        (tkkHyperbolicLieEquiv d) (tkkHyperbolicLieEquiv e) := by
  rw [tkkHyperbolicLieEquiv, tkkBracket_eq_abstractTKKBracket]
  exact abstractTKKLieEquiv_map_lie d e

/-- The finite noncommutative TKK equivalence and its dimension datum. -/
theorem tkk_hyperbolic_lie_equivalence_packet :
    Module.finrank ℝ TKKCarrier = 45 ∧
      Module.finrank ℝ hyperbolicSkewSubmodule = 45 ∧
      (∀ d e : TKKCarrier,
        tkkHyperbolicLieEquiv (tkkBracket d e) =
          hyperbolicSkewBracket
            (tkkHyperbolicLieEquiv d) (tkkHyperbolicLieEquiv e)) := by
  exact ⟨tkkCarrier_finrank_eq_45, hyperbolicSkewSubmodule_finrank,
    tkkHyperbolicLieEquiv_map_tkkBracket⟩

def spinFactorTriple (x y z : TKKMiddle) : TKKMiddle :=
  beta44 x y • z + beta44 z y • x - beta44 x z • y

theorem spinFactorTriple_eq_doubleBracket (x y z : TKKMiddle)
    (w : SplitOctonionTKK55.Carrier) :
    ((nMap y * pMap x - pMap x * nMap y) * pMap z -
        pMap z * (nMap y * pMap x - pMap x * nMap y)) w =
      P (spinFactorTriple x y z) w := by
  rw [n_p_comm]
  have h :
      (-dMap (beta44 x y) (rankTwoOrthogonal x y)) * pMap z -
          pMap z * (-dMap (beta44 x y) (rankTwoOrthogonal x y)) =
        -pMap
          ((rankTwoOrthogonal x y).1.mulVec z - beta44 x y • z) := by
    apply LinearMap.ext
    intro q
    calc
      ((-dMap (beta44 x y) (rankTwoOrthogonal x y)) * pMap z -
            pMap z * (-dMap (beta44 x y) (rankTwoOrthogonal x y))) q =
          (-(dMap (beta44 x y) (rankTwoOrthogonal x y) * pMap z -
            pMap z * dMap (beta44 x y) (rankTwoOrthogonal x y))) q := by
              simp [Module.End.mul_apply, map_neg] ; ring
      _ = (-pMap
          ((rankTwoOrthogonal x y).1.mulVec z - beta44 x y • z)) q := by
            rw [d_p_comm]
  rw [h]
  have hvec :
      (rankTwoOrthogonal x y).1.mulVec z - beta44 x y • z =
        beta44 x z • y - beta44 y z • x - beta44 x y • z := by
    rw [rankTwoOrthogonal_apply]
  rw [hvec]
  have hcoef :
      -(beta44 x z • y - beta44 y z • x - beta44 x y • z) =
        spinFactorTriple x y z := by
    ext i
    fin_cases i <;>
      simp [spinFactorTriple, beta44,
        Fin.sum_univ_succ, smul_eq_mul]
      <;> ring
  have hmap :
      -pMap (beta44 x z • y - beta44 y z • x - beta44 x y • z) =
        pMap (spinFactorTriple x y z) := by
    calc
      -pMap (beta44 x z • y - beta44 y z • x - beta44 x y • z) =
          pMap (-(beta44 x z • y - beta44 y z • x - beta44 x y • z)) :=
        (map_neg (pMap) _).symm
      _ = pMap (spinFactorTriple x y z) := congrArg pMap hcoef
  rw [hmap]
  rfl

end InfoGeometry.Canonical.SplitOctonionTKK55LieEquivalence
