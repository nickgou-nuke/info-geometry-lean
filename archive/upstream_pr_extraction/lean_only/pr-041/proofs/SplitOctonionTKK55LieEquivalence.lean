import proofs.SplitOctonionTKK55Blocks

/-!
# Native block carrier for `so(5,5)`

This file turns the verified hyperbolic block equations into Mathlib-native
linear and Lie carriers.  The source is the independently typed
`J ⊕ (R ⊕ so(4,4)) ⊕ J` block space; the target is the constrained
hyperbolic orthogonal Lie subalgebra.
-/

noncomputable section
namespace SplitOctonionTKK55LieEquivalence

open SplitOctonionTKK55Blocks

def middleSO44 : Submodule ℝ (Matrix (Fin 8) (Fin 8) ℝ) where
  carrier := {K | betaSkew K}
  zero_mem' := by intro i j; simp [betaSkew]
  add_mem' := by
    intro K L hK hL i j
    simp only [Matrix.add_apply, mul_add]
    rw [hK i j, hL i j]
    ring
  smul_mem' := by
    intro c K hK i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    calc
      (if i.val < 4 then 1 else -1) * (c * K i j) =
          c * ((if i.val < 4 then 1 else -1) * K i j) := by ring
      _ = c * (-((if j.val < 4 then 1 else -1) * K j i)) := by rw [hK i j]
      _ = -((if j.val < 4 then 1 else -1) * (c * K j i)) := by ring

def hyperbolicSO55Submodule : Submodule ℝ HMatrix where
  carrier := {A | hyperbolicOrthogonal A}
  zero_mem' := by unfold hyperbolicOrthogonal; simp
  add_mem' := by
    intro A B hA hB
    change hyperbolicOrthogonal A at hA
    change hyperbolicOrthogonal B at hB
    change hyperbolicOrthogonal (A + B)
    unfold hyperbolicOrthogonal at *
    simp only [Matrix.transpose_add, add_mul, mul_add]
    calc
      (A.transpose * metric55 + B.transpose * metric55) +
          (metric55 * A + metric55 * B) =
        (A.transpose * metric55 + metric55 * A) +
          (B.transpose * metric55 + metric55 * B) := by abel
      _ = 0 := by rw [hA, hB]; simp
  smul_mem' := by
    intro c A hA
    change hyperbolicOrthogonal A at hA
    change hyperbolicOrthogonal (c • A)
    unfold hyperbolicOrthogonal at *
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul]
    rw [← smul_add, hA, smul_zero]

def hyperbolicSO55 : LieSubalgebra ℝ HMatrix :=
  LieSubalgebra.mk hyperbolicSO55Submodule (by
    intro A B hA hB
    change hyperbolicOrthogonal (hBracket A B)
    exact hBracket_hyperbolicOrthogonal hA hB)

/-- Independently typed three-graded TKK block carrier. -/
abbrev TKKBlockCarrier := HVector × ((ℝ × middleSO44) × HVector)

def blockLinearMap : TKKBlockCarrier →ₗ[ℝ] hyperbolicSO55Submodule where
  toFun q := ⟨P q.1 + D q.2.1.1 q.2.1.2.1 + N q.2.2,
    by
      apply hyperbolicSO55Submodule.add_mem
      · apply hyperbolicSO55Submodule.add_mem
        · exact P_hyperbolicOrthogonal q.1
        · exact D_hyperbolicOrthogonal q.2.1.2.2
      · exact N_hyperbolicOrthogonal q.2.2⟩
  map_add' q r := by
    ext i j
    cases i <;> cases j <;>
      simp [P, D, N, flat]
    all_goals (try split_ifs) <;> ring
  map_smul' c q := by
    ext i j
    cases i <;> cases j <;>
      simp [P, D, N, flat]
    all_goals (try split_ifs) <;> ring

theorem blockLinearMap_injective : Function.Injective blockLinearMap := by
  intro q r h
  have hm : (blockLinearMap q : HMatrix) = blockLinearMap r :=
    congrArg Subtype.val h
  apply Prod.ext
  · funext i
    have hi := congrArg (fun A : HMatrix => A (.middle i) .minus) hm
    simpa [blockLinearMap, P, D, N] using hi
  apply Prod.ext
  · apply Prod.ext
    · have hi := congrArg (fun A : HMatrix => A .minus .minus) hm
      simpa [blockLinearMap, P, D, N] using hi
    · apply Subtype.ext
      funext i j
      have hij := congrArg (fun A : HMatrix => A (.middle i) (.middle j)) hm
      simpa [blockLinearMap, P, D, N] using hij
  · funext i
    have hi := congrArg (fun A : HMatrix => A (.middle i) .plus) hm
    simpa [blockLinearMap, P, D, N] using hi

theorem blockLinearMap_surjective : Function.Surjective blockLinearMap := by
  intro A
  let b := disassemble (A : HMatrix)
  let K : middleSO44 := ⟨b.K, disassemble_betaSkew A.property⟩
  refine ⟨(b.x, (b.a, K), b.y), ?_⟩
  apply Subtype.ext
  exact assemble_disassemble_of_hyperbolicOrthogonal A.property

/-- Unique structural block equivalence
`J ⊕ (R ⊕ so(4,4)) ⊕ J ≃ so(5,5)` at the linear level. -/
def tkkBlockLinearEquiv : TKKBlockCarrier ≃ₗ[ℝ] hyperbolicSO55Submodule :=
  LinearEquiv.ofBijective blockLinearMap
    ⟨blockLinearMap_injective, blockLinearMap_surjective⟩

theorem tkkBlockLinearEquiv_apply (q : TKKBlockCarrier) :
    ((tkkBlockLinearEquiv q : hyperbolicSO55Submodule) : HMatrix) =
      P q.1 + D q.2.1.1 q.2.1.2.1 + N q.2.2 := rfl

theorem middleCommutator_betaSkew (K L : middleSO44) :
    betaSkew (K.1 * L.1 - L.1 * K.1) := by
  have horth : hyperbolicOrthogonal
      (hBracket (D 0 K.1) (D 0 L.1)) :=
    hBracket_hyperbolicOrthogonal
      (D_hyperbolicOrthogonal K.2) (D_hyperbolicOrthogonal L.2)
  rw [D_D_bracket] at horth
  simpa [disassemble, D] using disassemble_betaSkew horth

def middleCommutator (K L : middleSO44) : middleSO44 :=
  ⟨K.1 * L.1 - L.1 * K.1, middleCommutator_betaSkew K L⟩

def rankTwoSO44 (x y : HVector) : middleSO44 :=
  ⟨rankTwo x y, rankTwo_betaSkew x y⟩

/-- Explicit source TKK bracket in the independent block coordinates. -/
def tkkBracket (q r : TKKBlockCarrier) : TKKBlockCarrier :=
  (matVec q.2.1.2.1 r.1 - matVec r.2.1.2.1 q.1 - q.2.1.1 • r.1 +
      r.2.1.1 • q.1,
    ((beta44 q.1 r.2.2 - beta44 r.1 q.2.2,
      middleCommutator q.2.1.2 r.2.1.2 +
        rankTwoSO44 q.1 r.2.2 - rankTwoSO44 r.1 q.2.2),
      matVec q.2.1.2.1 r.2.2 - matVec r.2.1.2.1 q.2.2 +
        q.2.1.1 • r.2.2 - r.2.1.1 • q.2.2))

theorem blockLinearMap_tkkBracket (q r : TKKBlockCarrier) :
    ((blockLinearMap (tkkBracket q r) : hyperbolicSO55Submodule) : HMatrix) =
      hBracket (blockLinearMap q : HMatrix) (blockLinearMap r : HMatrix) := by
  apply hyperbolicOrthogonal_ext
  · exact (blockLinearMap (tkkBracket q r)).property
  · exact hBracket_hyperbolicOrthogonal
      (blockLinearMap q).property (blockLinearMap r).property
  · simp [blockLinearMap, tkkBracket, middleCommutator, rankTwoSO44,
      disassemble, hBracket, P, D, N, matVec, rankTwo,
      Matrix.mul_apply, Matrix.mulVec, sum_HIndex, dotProduct]
    constructor
    · funext i
      ring
    constructor
    · rw [beta44_symmetric q.1 r.2.2, beta44_symmetric r.1 q.2.2,
        ← beta44_flat r.2.2 q.1, ← beta44_flat q.2.2 r.1]
      ring
    constructor
    · funext i j
      ring
    · funext i
      ring

instance : Bracket TKKBlockCarrier TKKBlockCarrier := ⟨tkkBracket⟩

instance : Bracket hyperbolicSO55Submodule hyperbolicSO55Submodule :=
  ⟨fun A B => ⟨hBracket A.1 B.1,
    hBracket_hyperbolicOrthogonal A.2 B.2⟩⟩

theorem blockLinearMap_lie (q r : TKKBlockCarrier) :
    ((blockLinearMap ⁅q, r⁆ : hyperbolicSO55Submodule) : HMatrix) =
      ⁅(blockLinearMap q : HMatrix), (blockLinearMap r : HMatrix)⁆ := by
  exact blockLinearMap_tkkBracket q r

def blockMatrixLinearMap : TKKBlockCarrier →ₗ[ℝ] HMatrix :=
  hyperbolicSO55Submodule.subtype.comp blockLinearMap

theorem blockMatrixLinearMap_injective : Function.Injective blockMatrixLinearMap := by
  intro q r h
  apply blockLinearMap_injective
  apply Subtype.ext
  exact h

theorem blockMatrixLinearMap_lie (q r : TKKBlockCarrier) :
    blockMatrixLinearMap ⁅q, r⁆ =
      ⁅blockMatrixLinearMap q, blockMatrixLinearMap r⁆ :=
  blockLinearMap_lie q r

instance : LieRing TKKBlockCarrier where
  add_lie q r s := by
    apply blockMatrixLinearMap_injective
    simpa only [LinearMap.map_add, blockMatrixLinearMap_lie] using
      add_lie (blockMatrixLinearMap q) (blockMatrixLinearMap r)
        (blockMatrixLinearMap s)
  lie_add q r s := by
    apply blockMatrixLinearMap_injective
    simpa only [LinearMap.map_add, blockMatrixLinearMap_lie] using
      lie_add (blockMatrixLinearMap q) (blockMatrixLinearMap r)
        (blockMatrixLinearMap s)
  lie_self q := by
    apply blockMatrixLinearMap_injective
    simpa only [LinearMap.map_zero, blockMatrixLinearMap_lie] using
      lie_self (blockMatrixLinearMap q)
  leibniz_lie q r s := by
    apply blockMatrixLinearMap_injective
    simpa only [LinearMap.map_add, blockMatrixLinearMap_lie] using
      leibniz_lie (blockMatrixLinearMap q) (blockMatrixLinearMap r)
        (blockMatrixLinearMap s)

instance : LieAlgebra ℝ TKKBlockCarrier where
  lie_smul c q r := by
    apply blockMatrixLinearMap_injective
    simpa only [LinearMap.map_smul, blockMatrixLinearMap_lie] using
      lie_smul c (blockMatrixLinearMap q) (blockMatrixLinearMap r)

def tkkBlockLieHom : TKKBlockCarrier →ₗ⁅ℝ⁆ hyperbolicSO55 where
  toLinearMap :=
    { toFun := fun q => ⟨(blockLinearMap q).1, (blockLinearMap q).2⟩
      map_add' := by
        intro q r
        apply Subtype.ext
        exact congrArg Subtype.val (LinearMap.map_add blockLinearMap q r)
      map_smul' := by
        intro c q
        apply Subtype.ext
        exact congrArg Subtype.val (LinearMap.map_smul blockLinearMap c q) }
  map_lie' := by
    intro q r
    apply Subtype.ext
    exact blockLinearMap_lie q r

theorem tkkBlockLieHom_bijective : Function.Bijective tkkBlockLieHom := by
  constructor
  · intro q r h
    apply blockLinearMap_injective
    apply Subtype.ext
    exact congrArg Subtype.val h
  · intro A
    let A' : hyperbolicSO55Submodule := ⟨A.1, A.2⟩
    rcases blockLinearMap_surjective A' with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    apply Subtype.ext
    exact congrArg Subtype.val hq

/-- The independently bracketed TKK block carrier is the full real
hyperbolic orthogonal Lie algebra. -/
def tkkHyperbolicLieEquiv : TKKBlockCarrier ≃ₗ⁅ℝ⁆ hyperbolicSO55 :=
  LieEquiv.ofBijective tkkBlockLieHom tkkBlockLieHom_bijective

theorem tkkHyperbolicLieEquiv_apply (q : TKKBlockCarrier) :
    ((tkkHyperbolicLieEquiv q : hyperbolicSO55) : HMatrix) =
      P q.1 + D q.2.1.1 q.2.1.2.1 + N q.2.2 := rfl

end SplitOctonionTKK55LieEquivalence
end noncomputable section
