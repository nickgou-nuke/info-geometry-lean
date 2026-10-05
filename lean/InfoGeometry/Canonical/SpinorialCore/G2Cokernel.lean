import InfoGeometry.Canonical.SpinorialCore.G2Certificate

/-!
# The integer cokernel, constructed as a native quotient module

The quotient is identified with ZMod 2 × ZMod 2 × ZMod 364 by a surjective
linear map with the exact required kernel. This file does not assert a
Cuntz-Krieger K-theory theorem or a Pin bordism identification.
-/

namespace InfoGeometry.Canonical.SpinorialCore.G2
open Matrix

noncomputable section

abbrev Lattice := Fin 12 → ℤ
abbrev SmithGroup := ZMod 2 × ZMod 2 × ZMod 364
abbrev TwoPrimary := ZMod 2 × ZMod 2 × ZMod 4
abbrev Cokernel := Lattice ⧸ LinearMap.range relation.toLin'
abbrev TransposeCokernel := Lattice ⧸ LinearMap.range relation.transpose.toLin'

/-- Reduction of the three non-unit Smith coordinates. -/
def coordinateResidue : Lattice →ₗ[ℤ] SmithGroup where
  toFun x := ((x 9 : ZMod 2), (x 10 : ZMod 2), (x 11 : ZMod 364))
  map_add' x y := by ext <;> simp
  map_smul' a x := by ext <;> simp [zsmul_eq_mul]

theorem coordinateResidue_surjective : Function.Surjective coordinateResidue := by
  intro y
  refine ⟨![0, 0, 0, 0, 0, 0, 0, 0, 0,
    (y.1.val : ℤ), (y.2.1.val : ℤ), (y.2.2.val : ℤ)], ?_⟩
  simp [coordinateResidue]

/-- Explicit coordinate exactness for the diagonal presentation. -/
theorem coordinateResidue_zero_iff (x : Lattice) :
    coordinateResidue x = 0 ↔ ∃ w : Lattice, smithDiagonal *ᵥ w = x := by
  constructor
  · intro hx
    have h9 : (x 9 : ZMod 2) = 0 := congrArg Prod.fst hx
    have h10 : (x 10 : ZMod 2) = 0 := congrArg (fun y : SmithGroup => y.2.1) hx
    have h11 : (x 11 : ZMod 364) = 0 := congrArg (fun y : SmithGroup => y.2.2) hx
    have d9 : (2 : ℤ) ∣ x 9 := by
      simpa only [ZMod.intCast_zmod_eq_zero_iff_dvd] using h9
    have d10 : (2 : ℤ) ∣ x 10 := by
      simpa only [ZMod.intCast_zmod_eq_zero_iff_dvd] using h10
    have d11 : (364 : ℤ) ∣ x 11 := by
      simpa only [ZMod.intCast_zmod_eq_zero_iff_dvd] using h11
    obtain ⟨a, ha⟩ := d9
    obtain ⟨b, hb⟩ := d10
    obtain ⟨c, hc⟩ := d11
    let w : Lattice := fun i =>
      if i = 9 then a else if i = 10 then b else if i = 11 then c else x i
    refine ⟨w, ?_⟩
    funext i
    change (Matrix.diagonal diagonalEntries *ᵥ w) i = x i
    rw [Matrix.mulVec_diagonal]
    fin_cases i <;> simp [w, diagonalEntries, ha, hb, hc]
  · rintro ⟨w, rfl⟩
    apply Prod.ext
    · change (((Matrix.diagonal diagonalEntries *ᵥ w) 9 : ℤ) : ZMod 2) = 0
      rw [Matrix.mulVec_diagonal]
      change ((2 * w 9 : ℤ) : ZMod 2) = 0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact ⟨w 9, rfl⟩
    · apply Prod.ext
      · change (((Matrix.diagonal diagonalEntries *ᵥ w) 10 : ℤ) : ZMod 2) = 0
        rw [Matrix.mulVec_diagonal]
        change ((2 * w 10 : ℤ) : ZMod 2) = 0
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact ⟨w 10, rfl⟩
      · change (((Matrix.diagonal diagonalEntries *ᵥ w) 11 : ℤ) : ZMod 364) = 0
        rw [Matrix.mulVec_diagonal]
        change ((364 * w 11 : ℤ) : ZMod 364) = 0
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact ⟨w 11, rfl⟩

/-- The certificate transports image membership without invoking determinants. -/
theorem image_smith_iff (x : Lattice) :
    (∃ z : Lattice, relation *ᵥ z = x) ↔
      ∃ w : Lattice, smithDiagonal *ᵥ w = U *ᵥ x := by
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨VInv *ᵥ z, ?_⟩
    rw [← smith_certificate]
    simp only [Matrix.mulVec_mulVec, mul_assoc, V_mul_VInv, mul_one]
  · rintro ⟨w, hw⟩
    refine ⟨V *ᵥ w, ?_⟩
    have h := congrArg (fun y : Lattice => UInv *ᵥ y) hw
    rw [← smith_certificate] at h
    simpa only [Matrix.mulVec_mulVec, ← mul_assoc, UInv_mul_U,
      one_mul, Matrix.one_mulVec] using h

/-- Residues in the original vertex coordinates, with the actual U transport. -/
def graphResidue : Lattice →ₗ[ℤ] SmithGroup := coordinateResidue.comp U.toLin'

theorem graphResidue_surjective : Function.Surjective graphResidue := by
  intro y
  obtain ⟨x, hx⟩ := coordinateResidue_surjective y
  refine ⟨UInv *ᵥ x, ?_⟩
  change coordinateResidue (U *ᵥ (UInv *ᵥ x)) = y
  rw [Matrix.mulVec_mulVec, U_mul_UInv, Matrix.one_mulVec]
  exact hx

theorem graphResidue_exact :
    LinearMap.ker graphResidue = LinearMap.range relation.toLin' := by
  apply Submodule.ext
  intro x
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  change coordinateResidue (U *ᵥ x) = 0 ↔ ∃ z : Lattice, relation *ᵥ z = x
  exact (coordinateResidue_zero_iff _).trans (image_smith_iff x).symm

/-- The actual cokernel equivalence, not a cardinality comparison. -/
def cokernelEquiv : Cokernel ≃ₗ[ℤ] SmithGroup := by
  change (Lattice ⧸ LinearMap.range relation.toLin') ≃ₗ[ℤ] SmithGroup
  rw [← graphResidue_exact]
  exact graphResidue.quotKerEquivOfSurjective graphResidue_surjective

/-! ## The transposed presentation used by the graph boundary matrix

The Cuntz--Krieger boundary map is `I - Aᵀ`, while `relation` above is
`I - A`. Transposing the integral equivalence swaps the two unimodular
coordinate changes. This gives the actual cokernel of the boundary map,
not merely the determinant or the cokernel of a different orientation.
-/

theorem transpose_smith_certificate :
    V.transpose * relation.transpose * U.transpose = smithDiagonal := by
  have h := congrArg Matrix.transpose smith_certificate
  simpa only [Matrix.transpose_mul, Matrix.diagonal_transpose] using h

theorem UTranspose_mul_UInvTranspose :
    U.transpose * UInv.transpose = 1 := by
  have h := congrArg Matrix.transpose UInv_mul_U
  simpa only [Matrix.transpose_mul] using h

theorem UInvTranspose_mul_UTranspose :
    UInv.transpose * U.transpose = 1 := by
  have h := congrArg Matrix.transpose U_mul_UInv
  simpa only [Matrix.transpose_mul] using h

theorem VTranspose_mul_VInvTranspose :
    V.transpose * VInv.transpose = 1 := by
  have h := congrArg Matrix.transpose VInv_mul_V
  simpa only [Matrix.transpose_mul] using h

theorem VInvTranspose_mul_VTranspose :
    VInv.transpose * V.transpose = 1 := by
  have h := congrArg Matrix.transpose V_mul_VInv
  simpa only [Matrix.transpose_mul] using h

theorem transpose_image_smith_iff (x : Lattice) :
    (∃ z : Lattice, relation.transpose *ᵥ z = x) ↔
      ∃ w : Lattice, smithDiagonal *ᵥ w = V.transpose *ᵥ x := by
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨UInv.transpose *ᵥ z, ?_⟩
    rw [← transpose_smith_certificate]
    simp only [Matrix.mulVec_mulVec, mul_assoc,
      UTranspose_mul_UInvTranspose, mul_one]
  · rintro ⟨w, hw⟩
    refine ⟨U.transpose *ᵥ w, ?_⟩
    have h := congrArg (fun y : Lattice => VInv.transpose *ᵥ y) hw
    rw [← transpose_smith_certificate] at h
    simpa only [Matrix.mulVec_mulVec, ← mul_assoc,
      VInvTranspose_mul_VTranspose, one_mul, Matrix.one_mulVec] using h

def transposeGraphResidue : Lattice →ₗ[ℤ] SmithGroup :=
  coordinateResidue.comp V.transpose.toLin'

theorem transposeGraphResidue_surjective :
    Function.Surjective transposeGraphResidue := by
  intro y
  obtain ⟨x, hx⟩ := coordinateResidue_surjective y
  refine ⟨VInv.transpose *ᵥ x, ?_⟩
  change coordinateResidue (V.transpose *ᵥ (VInv.transpose *ᵥ x)) = y
  rw [Matrix.mulVec_mulVec, VTranspose_mul_VInvTranspose,
    Matrix.one_mulVec]
  exact hx

theorem transposeGraphResidue_exact :
    LinearMap.ker transposeGraphResidue =
      LinearMap.range relation.transpose.toLin' := by
  apply Submodule.ext
  intro x
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  change coordinateResidue (V.transpose *ᵥ x) = 0 ↔
    ∃ z : Lattice, relation.transpose *ᵥ z = x
  exact (coordinateResidue_zero_iff _).trans
    (transpose_image_smith_iff x).symm

/-- The cokernel of the oriented graph boundary map has the certified Smith
group. This is an integer-module result; it does not assert a
Cuntz--Krieger K-theory classification. -/
def transposeCokernelEquiv : TransposeCokernel ≃ₗ[ℤ] SmithGroup := by
  change (Lattice ⧸ LinearMap.range relation.transpose.toLin') ≃ₗ[ℤ] SmithGroup
  rw [← transposeGraphResidue_exact]
  exact transposeGraphResidue.quotKerEquivOfSurjective
    transposeGraphResidue_surjective

theorem smithGroup_card : Fintype.card SmithGroup = 1456 := by
  norm_num [SmithGroup, Fintype.card_prod, ZMod.card]

theorem smithDiagonal_injective : Function.Injective smithDiagonal.mulVec := by
  intro x y h
  funext i
  have hi := congrFun h i
  change (Matrix.diagonal diagonalEntries *ᵥ x) i =
    (Matrix.diagonal diagonalEntries *ᵥ y) i at hi
  simp only [Matrix.mulVec_diagonal] at hi
  exact mul_left_cancel₀ (diagonal_nonzero i) hi

theorem relation_injective : Function.Injective relation.mulVec := by
  intro x y h
  have ht : smithDiagonal *ᵥ (VInv *ᵥ x) = smithDiagonal *ᵥ (VInv *ᵥ y) := by
    rw [← smith_certificate]
    simp only [Matrix.mulVec_mulVec, mul_assoc, V_mul_VInv, mul_one]
    simpa only [Matrix.mulVec_mulVec] using congrArg (fun z : Lattice => U *ᵥ z) h
  have hi := congrArg (fun z : Lattice => V *ᵥ z) (smithDiagonal_injective ht)
  simpa only [Matrix.mulVec_mulVec, V_mul_VInv, Matrix.one_mulVec] using hi

theorem relation_kernel_zero : LinearMap.ker relation.toLin' = ⊥ :=
  LinearMap.ker_eq_bot.mpr relation_injective

/-- CRT splits the cyclic 364 factor into its 4-primary and 91-primary factors. -/
def cyclic364Equiv : ZMod 364 ≃+ (ZMod 4 × ZMod 91) :=
  (ZMod.chineseRemainder (show Nat.Coprime 4 91 by decide)).toAddEquiv

/-- Explicit primary decomposition; the 2-primary part is not cyclic of order 16. -/
def primaryDecomposition : SmithGroup ≃+ (TwoPrimary × ZMod 91) where
  toFun x := ((x.1, x.2.1, (cyclic364Equiv x.2.2).1), (cyclic364Equiv x.2.2).2)
  invFun y := (y.1.1, y.1.2.1, cyclic364Equiv.symm (y.1.2.2, y.2))
  left_inv x := by
    rcases x with ⟨a, b, c⟩
    simp
  right_inv y := by
    rcases y with ⟨⟨a, b, c⟩, d⟩
    simp
  map_add' x y := by
    ext <;> simp

theorem twoPrimary_card : Fintype.card TwoPrimary = 16 := by decide

theorem twoPrimary_four_smul : ∀ x : TwoPrimary, (4 : ℕ) • x = 0 := by decide

theorem twoPrimary_not_elementary : ∃ x : TwoPrimary, (2 : ℕ) • x ≠ 0 := by
  exact ⟨(0, 0, 1), by decide⟩

/-- No additive surjection can identify this 2-primary group with ZMod 16. -/
theorem no_surjection_to_zmod16 (f : TwoPrimary →+ ZMod 16) :
    ¬ Function.Surjective f := by
  intro hf
  obtain ⟨x, hx⟩ := hf 1
  have h : (4 : ℕ) • (1 : ZMod 16) = 0 := by
    calc
      (4 : ℕ) • (1 : ZMod 16) = f ((4 : ℕ) • x) := by rw [map_nsmul, hx]
      _ = 0 := by rw [twoPrimary_four_smul, map_zero]
  exact (by decide : (4 : ℕ) • (1 : ZMod 16) ≠ 0) h

end
end InfoGeometry.Canonical.SpinorialCore.G2
