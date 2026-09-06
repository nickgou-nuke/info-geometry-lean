/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2PeirceFibration

/-!
# Explicit fixed-prefix residual constraints

This owner exposes the five residual coordinates of a Peirce fiber as an
explicit dependent subtype.  The predicate is exactly the native
`admissibleBasis7` predicate applied to the reconstructed seven-tuple; no PC
normal form or cardinality assertion is introduced here.
-/

namespace InfoGeometry.Algebra.Zorn.G2FixedPrefixResidualConstraints

open _root_.InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2PeirceFibration

abbrev ResidualTuple :=
  SplitOctF2 × SplitOctF2 × SplitOctF2 × SplitOctF2 × SplitOctF2

def residualTupleBasis
    (p : NontrivialIdempotent)
    (x : PeircePlusFiber p)
    (r : ResidualTuple) : Fin 7 → SplitOctF2 :=
  ![p.1, x.1.1, r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2]

def IsResidualTuple
    (p : NontrivialIdempotent)
    (x : PeircePlusFiber p)
    (r : ResidualTuple) : Prop :=
  admissibleBasis7 (residualTupleBasis p x r)

abbrev ResidualTupleCarrier
    (p : NontrivialIdempotent)
    (x : PeircePlusFiber p) :=
  {r : ResidualTuple // IsResidualTuple p x r}

noncomputable instance residualFiber_finite
    (p : NontrivialIdempotent) (x : PeircePlusFiber p) :
    Finite (ResidualFiber p x) :=
  Finite.of_injective
    (fun v : ResidualFiber p x => residualCoordinates v.1)
    (fun v w h => residualCoordinates_injective_on_fiber v w h)

noncomputable instance residualFiber_fintype
    (p : NontrivialIdempotent) (x : PeircePlusFiber p) :
    Fintype (ResidualFiber p x) :=
  Fintype.ofFinite (ResidualFiber p x)

def residualTupleOfFiber
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (v : ResidualFiber p x) : ResidualTuple :=
  residualCoordinates v.1

/-! The following predicate records only native relations already exposed by
the admissible-basis constraint owner.  It is deliberately a necessary
predicate: no classification by Boolean or PC coordinates is asserted here. -/

def NativeResidualConstraints
    (p : NontrivialIdempotent)
    (x : PeircePlusFiber p)
    (r : ResidualTuple) : Prop :=
  mul r.1 r.1 = zero ∧
  mul r.2.1 r.2.1 = zero ∧
  mul r.2.2.1 r.2.2.1 = zero ∧
  mul r.2.2.2.1 r.2.2.2.1 = zero ∧
  mul r.2.2.2.2 r.2.2.2.2 = zero ∧
  mul x.1.1 r.2.2.1 = p.1 ∧
  mul r.2.2.1 x.1.1 = peirceComplement p.1 ∧
  mul x.1.1 r.2.2.2.1 = zero

theorem residualTupleOfFiber_nativeConstraints
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (v : ResidualFiber p x) :
    NativeResidualConstraints p x (residualTupleOfFiber v) := by
  have hp : basisPrefix1 v.1 = p.1 := congrArg Subtype.val v.2.1
  have hx : basisPrefix2 v.1 = x.1.1 := congrArg Subtype.val v.2.2
  rcases admissibleBasis7_all_prefixes_square_zero v.1 with
    ⟨_, h₃, h₄, h₅, h₆, h₇⟩
  refine ⟨h₃, h₄, h₅, h₆, h₇, ?_, ?_, ?_⟩
  · change mul x.1.1 (basisPrefix5 v.1) = p.1
    calc
      mul x.1.1 (basisPrefix5 v.1) = mul (basisPrefix2 v.1) (basisPrefix5 v.1) :=
        congrArg (fun z => mul z (basisPrefix5 v.1)) hx.symm
      _ = basisPrefix1 v.1 := admissibleBasis7_second_fifth_product_eq_first v.1
      _ = p.1 := hp
  · change mul (basisPrefix5 v.1) x.1.1 = peirceComplement p.1
    calc
      mul (basisPrefix5 v.1) x.1.1 = mul (basisPrefix5 v.1) (basisPrefix2 v.1) :=
        congrArg (fun z => mul (basisPrefix5 v.1) z) hx.symm
      _ = peirceComplement (basisPrefix1 v.1) :=
        admissibleBasis7_fifth_second_product_eq_complement v.1
      _ = peirceComplement p.1 := congrArg peirceComplement hp
  · change mul x.1.1 (basisPrefix6 v.1) = zero
    calc
      mul x.1.1 (basisPrefix6 v.1) = mul (basisPrefix2 v.1) (basisPrefix6 v.1) :=
        congrArg (fun z => mul z (basisPrefix6 v.1)) hx.symm
      _ = zero := admissibleBasis7_second_sixth_product_eq_zero v.1

theorem residualTupleBasis_of_fiber
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (v : ResidualFiber p x) :
    residualTupleBasis p x (residualTupleOfFiber v) = v.1.1 := by
  funext i
  fin_cases i
  · simpa [residualTupleBasis, residualTupleOfFiber, residualCoordinates,
      basisPrefix1] using (congrArg Subtype.val v.2.1).symm
  · simpa [residualTupleBasis, residualTupleOfFiber, residualCoordinates,
      basisPrefix2] using (congrArg Subtype.val v.2.2).symm
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem residualTupleOfFiber_mem
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (v : ResidualFiber p x) :
    IsResidualTuple p x (residualTupleOfFiber v) := by
  change admissibleBasis7 (residualTupleBasis p x (residualTupleOfFiber v))
  rw [residualTupleBasis_of_fiber v]
  exact v.1.2

def residualTupleOfFiberCarrier
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (v : ResidualFiber p x) : ResidualTupleCarrier p x :=
  ⟨residualTupleOfFiber v, residualTupleOfFiber_mem v⟩

def residualTupleToFiber
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (r : ResidualTupleCarrier p x) : ResidualFiber p x :=
  ⟨⟨residualTupleBasis p x r.1, r.2⟩, by
    constructor
    · apply Subtype.ext
      rfl
    · rfl⟩

theorem residualTupleToFiber_leftInverse
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (v : ResidualFiber p x) :
    residualTupleToFiber (residualTupleOfFiberCarrier v) = v := by
  apply Subtype.ext
  apply Subtype.ext
  exact residualTupleBasis_of_fiber v

theorem residualTupleToFiber_rightInverse
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (r : ResidualTupleCarrier p x) :
    residualTupleOfFiber (residualTupleToFiber r) = r.1 := by
  rfl

noncomputable def residualFiberEquivResidualTuple
    (p : NontrivialIdempotent) (x : PeircePlusFiber p) :
    ResidualFiber p x ≃ ResidualTupleCarrier p x where
  toFun := residualTupleOfFiberCarrier
  invFun := residualTupleToFiber
  left_inv := by
    intro v
    exact residualTupleToFiber_leftInverse v
  right_inv := by
    intro r
    apply Subtype.ext
    exact residualTupleToFiber_rightInverse r

theorem residualTupleCarrier_all_square_zero
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (r : ResidualTupleCarrier p x) :
    mul r.1.1 r.1.1 = zero ∧
    mul r.1.2.1 r.1.2.1 = zero ∧
    mul r.1.2.2.1 r.1.2.2.1 = zero ∧
    mul r.1.2.2.2.1 r.1.2.2.2.1 = zero ∧
    mul r.1.2.2.2.2 r.1.2.2.2.2 = zero := by
  simpa [residualTupleOfFiber, residualCoordinates, residualTupleToFiber] using
    (admissibleBasis7_all_prefixes_square_zero
      (residualTupleToFiber r).1).2

theorem residualTupleCarrier_nativeConstraints
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (r : ResidualTupleCarrier p x) :
    NativeResidualConstraints p x r.1 := by
  have h := residualTupleOfFiber_nativeConstraints (residualTupleToFiber r)
  rw [residualTupleToFiber_rightInverse r] at h
  exact h

theorem admissibleBasis7_third_fourth_product_eq_fifth
    (v : AdmissibleBasis7Carrier) :
    mul (basisPrefix3 v) (basisPrefix4 v) = basisPrefix5 v := by
  have h := admissibleBasis7_prefix_map_mul v up1 up2
  have he : mul up1 up2 = down0 := by
    rfl
  rw [he] at h
  have h₃ :
      extendBasisMap (basis8From7 (basisCoordinates v)) up1 =
        basisPrefix3 v := by
    simpa [basisPrefix3, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 3)
  have h₄ :
      extendBasisMap (basis8From7 (basisCoordinates v)) up2 =
        basisPrefix4 v := by
    simpa [basisPrefix4, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 4)
  have h₅ :
      extendBasisMap (basis8From7 (basisCoordinates v)) down0 =
        basisPrefix5 v := by
    simpa [basisPrefix5, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 5)
  rw [h₃, h₄, h₅] at h
  exact h.symm

theorem admissibleBasis7_second_third_product_eq_seventh
    (v : AdmissibleBasis7Carrier) :
    mul (basisPrefix2 v) (basisPrefix3 v) = basisPrefix7 v := by
  have h := admissibleBasis7_prefix_map_mul v up0 up1
  have he : mul up0 up1 = down2 := by
    rfl
  rw [he] at h
  have h₂ :
      extendBasisMap (basis8From7 (basisCoordinates v)) up0 =
        basisPrefix2 v := by
    simpa [basisPrefix2, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 2)
  have h₃ :
      extendBasisMap (basis8From7 (basisCoordinates v)) up1 =
        basisPrefix3 v := by
    simpa [basisPrefix3, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 3)
  have h₇ :
      extendBasisMap (basis8From7 (basisCoordinates v)) down2 =
        basisPrefix7 v := by
    simpa [basisPrefix7, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 7)
  rw [h₂, h₃, h₇] at h
  exact h.symm

theorem admissibleBasis7_fourth_second_product_eq_sixth
    (v : AdmissibleBasis7Carrier) :
    mul (basisPrefix4 v) (basisPrefix2 v) = basisPrefix6 v := by
  have h := admissibleBasis7_prefix_map_mul v up2 up0
  have he : mul up2 up0 = down1 := by
    rfl
  rw [he] at h
  have h₄ :
      extendBasisMap (basis8From7 (basisCoordinates v)) up2 =
        basisPrefix4 v := by
    simpa [basisPrefix4, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 4)
  have h₂ :
      extendBasisMap (basis8From7 (basisCoordinates v)) up0 =
        basisPrefix2 v := by
    simpa [basisPrefix2, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 2)
  have h₆ :
      extendBasisMap (basis8From7 (basisCoordinates v)) down1 =
        basisPrefix6 v := by
    simpa [basisPrefix6, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 6)
  rw [h₄, h₂, h₆] at h
  exact h.symm

theorem admissibleBasis7_eq_of_first_four_eq
    (v w : AdmissibleBasis7Carrier)
    (h₁ : basisPrefix1 v = basisPrefix1 w)
    (h₂ : basisPrefix2 v = basisPrefix2 w)
    (h₃ : basisPrefix3 v = basisPrefix3 w)
    (h₄ : basisPrefix4 v = basisPrefix4 w) :
    v = w := by
  have h₅ : basisPrefix5 v = basisPrefix5 w := by
    calc
      basisPrefix5 v = mul (basisPrefix3 v) (basisPrefix4 v) :=
        (admissibleBasis7_third_fourth_product_eq_fifth v).symm
      _ = mul (basisPrefix3 w) (basisPrefix4 w) := by rw [h₃, h₄]
      _ = basisPrefix5 w := admissibleBasis7_third_fourth_product_eq_fifth w
  have h₆ : basisPrefix6 v = basisPrefix6 w := by
    calc
      basisPrefix6 v = mul (basisPrefix4 v) (basisPrefix2 v) :=
        (admissibleBasis7_fourth_second_product_eq_sixth v).symm
      _ = mul (basisPrefix4 w) (basisPrefix2 w) := by rw [h₄, h₂]
      _ = basisPrefix6 w := admissibleBasis7_fourth_second_product_eq_sixth w
  have h₇ : basisPrefix7 v = basisPrefix7 w := by
    calc
      basisPrefix7 v = mul (basisPrefix2 v) (basisPrefix3 v) :=
        (admissibleBasis7_second_third_product_eq_seventh v).symm
      _ = mul (basisPrefix2 w) (basisPrefix3 w) := by rw [h₂, h₃]
      _ = basisPrefix7 w := admissibleBasis7_second_third_product_eq_seventh w
  apply admissibleBasis7_eq_of_prefixes v w h₁ h₂
  simp [residualCoordinates, h₃, h₄, h₅, h₆, h₇]

theorem residualFiber_eq_of_third_fourth_eq
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (v w : ResidualFiber p x)
    (h₃ : basisPrefix3 v.1 = basisPrefix3 w.1)
    (h₄ : basisPrefix4 v.1 = basisPrefix4 w.1) :
    v = w := by
  apply Subtype.ext
  apply admissibleBasis7_eq_of_first_four_eq v.1 w.1
  · exact congrArg Subtype.val v.2.1 |>.trans
      (congrArg Subtype.val w.2.1).symm
  · exact congrArg Subtype.val v.2.2 |>.trans
      (congrArg Subtype.val w.2.2).symm
  · exact h₃
  · exact h₄

def residualFiberUpperPair
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (v : ResidualFiber p x) : SplitOctF2 × SplitOctF2 :=
  (basisPrefix3 v.1, basisPrefix4 v.1)

theorem residualFiberUpperPair_injective
    {p : NontrivialIdempotent} {x : PeircePlusFiber p} :
    Function.Injective (@residualFiberUpperPair p x) := by
  intro v w h
  apply residualFiber_eq_of_third_fourth_eq v w
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

def residualUpperPairBasis
    (p : NontrivialIdempotent)
    (x : PeircePlusFiber p)
    (yz : SplitOctF2 × SplitOctF2) : Fin 7 → SplitOctF2 :=
  ![p.1, x.1.1, yz.1, yz.2, mul yz.1 yz.2,
    mul yz.2 x.1.1, mul x.1.1 yz.1]

def IsResidualUpperPair
    (p : NontrivialIdempotent)
    (x : PeircePlusFiber p)
    (yz : SplitOctF2 × SplitOctF2) : Prop :=
  admissibleBasis7 (residualUpperPairBasis p x yz)

abbrev ResidualUpperPair
    (p : NontrivialIdempotent)
    (x : PeircePlusFiber p) :=
  {yz : SplitOctF2 × SplitOctF2 // IsResidualUpperPair p x yz}

theorem residualUpperPair_first_square_zero
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (yz : ResidualUpperPair p x) :
    mul yz.1.1 yz.1.1 = zero := by
  exact admissibleBasis7_third_prefix_square_zero
    ⟨residualUpperPairBasis p x yz.1, yz.2⟩

theorem residualUpperPair_second_square_zero
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (yz : ResidualUpperPair p x) :
    mul yz.1.2 yz.1.2 = zero := by
  exact admissibleBasis7_fourth_prefix_square_zero
    ⟨residualUpperPairBasis p x yz.1, yz.2⟩

theorem residualUpperPair_first_peirce_eigenvalue
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (yz : ResidualUpperPair p x) :
    mul p.1 yz.1.1 = yz.1.1 := by
  let v : AdmissibleBasis7Carrier :=
    ⟨residualUpperPairBasis p x yz.1, yz.2⟩
  have h := admissibleBasis7_prefix_map_mul v ePlus up1
  have he : mul ePlus up1 = up1 := by rfl
  rw [he] at h
  have hp : extendBasisMap (basis8From7 (basisCoordinates v)) ePlus = p.1 := by
    simpa [basisPrefix1, basisCoordinates, basis8, v,
      residualUpperPairBasis] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 0)
  have hy : extendBasisMap (basis8From7 (basisCoordinates v)) up1 = yz.1.1 := by
    simpa [basisPrefix3, basisCoordinates, basis8, v,
      residualUpperPairBasis] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 3)
  rw [hp, hy] at h
  exact h.symm

theorem residualUpperPair_second_peirce_eigenvalue
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (yz : ResidualUpperPair p x) :
    mul p.1 yz.1.2 = yz.1.2 := by
  let v : AdmissibleBasis7Carrier :=
    ⟨residualUpperPairBasis p x yz.1, yz.2⟩
  have h := admissibleBasis7_prefix_map_mul v ePlus up2
  have he : mul ePlus up2 = up2 := by rfl
  rw [he] at h
  have hp : extendBasisMap (basis8From7 (basisCoordinates v)) ePlus = p.1 := by
    simpa [basisPrefix1, basisCoordinates, basis8, v,
      residualUpperPairBasis] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 0)
  have hz : extendBasisMap (basis8From7 (basisCoordinates v)) up2 = yz.1.2 := by
    simpa [basisPrefix4, basisCoordinates, basis8, v,
      residualUpperPairBasis] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 4)
  rw [hp, hz] at h
  exact h.symm

theorem residualUpperPair_first_right_peirce_zero
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (yz : ResidualUpperPair p x) :
    mul yz.1.1 p.1 = zero := by
  let v : AdmissibleBasis7Carrier :=
    ⟨residualUpperPairBasis p x yz.1, yz.2⟩
  have h := admissibleBasis7_prefix_map_mul v up1 ePlus
  have he : mul up1 ePlus = zero := by rfl
  rw [he] at h
  have hy : extendBasisMap (basis8From7 (basisCoordinates v)) up1 = yz.1.1 := by
    simpa [basisPrefix3, basisCoordinates, basis8, v,
      residualUpperPairBasis] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 3)
  have hp : extendBasisMap (basis8From7 (basisCoordinates v)) ePlus = p.1 := by
    simpa [basisPrefix1, basisCoordinates, basis8, v,
      residualUpperPairBasis] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 0)
  rw [hy, hp] at h
  exact h.symm

theorem residualUpperPair_second_right_peirce_zero
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (yz : ResidualUpperPair p x) :
    mul yz.1.2 p.1 = zero := by
  let v : AdmissibleBasis7Carrier :=
    ⟨residualUpperPairBasis p x yz.1, yz.2⟩
  have h := admissibleBasis7_prefix_map_mul v up2 ePlus
  have he : mul up2 ePlus = zero := by rfl
  rw [he] at h
  have hz : extendBasisMap (basis8From7 (basisCoordinates v)) up2 = yz.1.2 := by
    simpa [basisPrefix4, basisCoordinates, basis8, v,
      residualUpperPairBasis] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 4)
  have hp : extendBasisMap (basis8From7 (basisCoordinates v)) ePlus = p.1 := by
    simpa [basisPrefix1, basisCoordinates, basis8, v,
      residualUpperPairBasis] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 0)
  rw [hz, hp] at h
  exact h.symm

theorem residualUpperPair_second_mul_second_upper_mul_zero
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (yz : ResidualUpperPair p x) :
    mul x.1.1 (mul yz.1.2 x.1.1) = zero := by
  exact admissibleBasis7_second_sixth_product_eq_zero
    ⟨residualUpperPairBasis p x yz.1, yz.2⟩

theorem residualUpperPair_second_mul_upper_product_eq_first
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (yz : ResidualUpperPair p x) :
    mul x.1.1 (mul yz.1.1 yz.1.2) = p.1 := by
  exact admissibleBasis7_second_fifth_product_eq_first
    ⟨residualUpperPairBasis p x yz.1, yz.2⟩

theorem residualUpperPair_upper_product_mul_second_eq_complement
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (yz : ResidualUpperPair p x) :
    mul (mul yz.1.1 yz.1.2) x.1.1 =
      peirceComplement p.1 := by
  exact admissibleBasis7_fifth_second_product_eq_complement
    ⟨residualUpperPairBasis p x yz.1, yz.2⟩

def ResidualUpperPairNativeConstraints
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (yz : ResidualUpperPair p x) : Prop :=
  mul yz.1.1 yz.1.1 = zero ∧
  mul yz.1.2 yz.1.2 = zero ∧
  mul p.1 yz.1.1 = yz.1.1 ∧
  mul p.1 yz.1.2 = yz.1.2 ∧
  mul yz.1.1 p.1 = zero ∧
  mul yz.1.2 p.1 = zero ∧
  mul x.1.1 (mul yz.1.2 x.1.1) = zero ∧
  mul x.1.1 (mul yz.1.1 yz.1.2) = p.1 ∧
  mul (mul yz.1.1 yz.1.2) x.1.1 = peirceComplement p.1

theorem ePlus_square_zero_left_eigenvalue_support
    (y : SplitOctF2)
    (he : mul ePlus y = y)
    (hsq : mul y y = zero) :
    y = ⟨false, false, y.x0, y.x1, y.x2, false, false, false⟩ := by
  cases y
  simp [mul, ePlus, zero, dot3, cross0, cross1, cross2,
    add2, mul2] at he hsq ⊢
  rcases he with ⟨_, _, _, _⟩
  simp_all

theorem ePlus_two_sided_peirce_upper_support
    (y : SplitOctF2)
    (hL : mul ePlus y = y)
    (hR : mul y ePlus = zero) :
    y = ⟨false, false, y.x0, y.x1, y.x2, false, false, false⟩ := by
  cases y
  simp [mul, ePlus, zero, dot3, cross0, cross1, cross2,
    add2, mul2] at hL hR ⊢
  rcases hL with ⟨_, hL1, hL2, hL3⟩
  rcases hR with ⟨hR0, _, hR5, hR6, hR7⟩
  simp_all

theorem residualUpperPair_first_support_of_ePlus
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (hp : p.1 = ePlus) (yz : ResidualUpperPair p x) :
    yz.1.1 =
      ⟨false, false, yz.1.1.x0, yz.1.1.x1, yz.1.1.x2,
        false, false, false⟩ := by
  apply ePlus_square_zero_left_eigenvalue_support yz.1.1
  · rw [← hp]
    exact residualUpperPair_first_peirce_eigenvalue yz
  · exact residualUpperPair_first_square_zero yz

theorem residualUpperPair_second_support_of_ePlus
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (hp : p.1 = ePlus) (yz : ResidualUpperPair p x) :
    yz.1.2 =
      ⟨false, false, yz.1.2.x0, yz.1.2.x1, yz.1.2.x2,
        false, false, false⟩ := by
  apply ePlus_square_zero_left_eigenvalue_support yz.1.2
  · rw [← hp]
    exact residualUpperPair_second_peirce_eigenvalue yz
  · exact residualUpperPair_second_square_zero yz

def residualUpperPairBits
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (yz : ResidualUpperPair p x) : Fin 6 → Bool :=
  ![yz.1.1.x0, yz.1.1.x1, yz.1.1.x2,
    yz.1.2.x0, yz.1.2.x1, yz.1.2.x2]

theorem residualUpperPairBits_injective_of_ePlus
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (hp : p.1 = ePlus) :
    Function.Injective (@residualUpperPairBits p x) := by
  intro a b h
  have ha := residualUpperPair_first_support_of_ePlus hp a
  have hb := residualUpperPair_first_support_of_ePlus hp b
  have hza := residualUpperPair_second_support_of_ePlus hp a
  have hzb := residualUpperPair_second_support_of_ePlus hp b
  have hya0 : a.1.1.x0 = b.1.1.x0 := by
    simpa [residualUpperPairBits] using congrFun h 0
  have hya1 : a.1.1.x1 = b.1.1.x1 := by
    simpa [residualUpperPairBits] using congrFun h 1
  have hya2 : a.1.1.x2 = b.1.1.x2 := by
    simpa [residualUpperPairBits] using congrFun h 2
  have hza0 : a.1.2.x0 = b.1.2.x0 := by
    simpa [residualUpperPairBits] using congrFun h 3
  have hza1 : a.1.2.x1 = b.1.2.x1 := by
    simpa [residualUpperPairBits] using congrFun h 4
  have hza2 : a.1.2.x2 = b.1.2.x2 := by
    simpa [residualUpperPairBits] using congrFun h 5
  apply Subtype.ext
  apply Prod.ext
  · rw [ha, hb]
    congr
  · rw [hza, hzb]
    congr

theorem residualUpperPair_nativeConstraints
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (yz : ResidualUpperPair p x) :
    ResidualUpperPairNativeConstraints yz := by
  exact ⟨residualUpperPair_first_square_zero yz,
    residualUpperPair_second_square_zero yz,
    residualUpperPair_first_peirce_eigenvalue yz,
    residualUpperPair_second_peirce_eigenvalue yz,
    residualUpperPair_first_right_peirce_zero yz,
    residualUpperPair_second_right_peirce_zero yz,
    residualUpperPair_second_mul_second_upper_mul_zero yz,
    residualUpperPair_second_mul_upper_product_eq_first yz,
    residualUpperPair_upper_product_mul_second_eq_complement yz⟩

noncomputable instance residualUpperPair_fintype
    (p : NontrivialIdempotent) (x : PeircePlusFiber p) :
    Fintype (ResidualUpperPair p x) :=
  Fintype.ofFinite (ResidualUpperPair p x)

def residualUpperPairOfFiber
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (v : ResidualFiber p x) : SplitOctF2 × SplitOctF2 :=
  (basisPrefix3 v.1, basisPrefix4 v.1)

theorem residualUpperPairBasis_of_fiber
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (v : ResidualFiber p x) :
    residualUpperPairBasis p x (residualUpperPairOfFiber v) = v.1.1 := by
  funext i
  fin_cases i
  · simpa [residualUpperPairBasis, residualUpperPairOfFiber,
      basisPrefix1] using (congrArg Subtype.val v.2.1).symm
  · simpa [residualUpperPairBasis, residualUpperPairOfFiber,
      basisPrefix2] using (congrArg Subtype.val v.2.2).symm
  · rfl
  · rfl
  · simpa [residualUpperPairBasis, residualUpperPairOfFiber,
      basisPrefix5] using
      (admissibleBasis7_third_fourth_product_eq_fifth v.1)
  · change mul (basisPrefix4 v.1) x.1.1 = basisPrefix6 v.1
    have hx : basisPrefix2 v.1 = x.1.1 := congrArg Subtype.val v.2.2
    calc
      mul (basisPrefix4 v.1) x.1.1 =
          mul (basisPrefix4 v.1) (basisPrefix2 v.1) :=
        congrArg (fun z => mul (basisPrefix4 v.1) z) hx.symm
      _ = basisPrefix6 v.1 :=
        admissibleBasis7_fourth_second_product_eq_sixth v.1
  · change mul x.1.1 (basisPrefix3 v.1) = basisPrefix7 v.1
    have hx : basisPrefix2 v.1 = x.1.1 := congrArg Subtype.val v.2.2
    calc
      mul x.1.1 (basisPrefix3 v.1) =
          mul (basisPrefix2 v.1) (basisPrefix3 v.1) :=
        congrArg (fun z => mul z (basisPrefix3 v.1)) hx.symm
      _ = basisPrefix7 v.1 :=
        admissibleBasis7_second_third_product_eq_seventh v.1

theorem residualUpperPairOfFiber_mem
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (v : ResidualFiber p x) :
    IsResidualUpperPair p x (residualUpperPairOfFiber v) := by
  change admissibleBasis7
    (residualUpperPairBasis p x (residualUpperPairOfFiber v))
  rw [residualUpperPairBasis_of_fiber v]
  exact v.1.2

def residualUpperPairOfFiberCarrier
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (v : ResidualFiber p x) : ResidualUpperPair p x :=
  ⟨residualUpperPairOfFiber v, residualUpperPairOfFiber_mem v⟩

def residualUpperPairToFiber
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (yz : ResidualUpperPair p x) : ResidualFiber p x :=
  ⟨⟨residualUpperPairBasis p x yz.1, yz.2⟩, by
    constructor
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl⟩

theorem residualUpperPairToFiber_leftInverse
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (v : ResidualFiber p x) :
    residualUpperPairToFiber (residualUpperPairOfFiberCarrier v) = v := by
  apply Subtype.ext
  apply Subtype.ext
  exact residualUpperPairBasis_of_fiber v

theorem residualUpperPairToFiber_rightInverse
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (yz : ResidualUpperPair p x) :
    residualUpperPairOfFiber (residualUpperPairToFiber yz) = yz.1 := by
  rfl

noncomputable def residualFiberEquivResidualUpperPair
    (p : NontrivialIdempotent) (x : PeircePlusFiber p) :
    ResidualFiber p x ≃ ResidualUpperPair p x where
  toFun := residualUpperPairOfFiberCarrier
  invFun := residualUpperPairToFiber
  left_inv := residualUpperPairToFiber_leftInverse
  right_inv := by
    intro yz
    apply Subtype.ext
    exact residualUpperPairToFiber_rightInverse yz

theorem residualUpperPair_card_le_64_of_ePlus
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (hp : p.1 = ePlus) :
    Fintype.card (ResidualUpperPair p x) ≤ 64 := by
  apply Fintype.card_le_of_injective
    (@residualUpperPairBits p x)
    (residualUpperPairBits_injective_of_ePlus hp)

theorem residualFiber_card_eq_upperPair_card
    (p : NontrivialIdempotent) (x : PeircePlusFiber p) :
    Fintype.card (ResidualFiber p x) =
      Fintype.card (ResidualUpperPair p x) := by
  exact Fintype.card_congr (residualFiberEquivResidualUpperPair p x)

theorem residualFiber_card_le_64_of_ePlus
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (hp : p.1 = ePlus) :
    Fintype.card (ResidualFiber p x) ≤ 64 := by
  rw [residualFiber_card_eq_upperPair_card]
  exact residualUpperPair_card_le_64_of_ePlus hp

theorem admissibleBasis7_to_aut_maps_standard_prefixes
    (v : AdmissibleBasis7Carrier) :
    (admissibleBasis7_to_aut v.1 v.2).1
        (basisPrefix1 standardAdmissibleBasis7) = basisPrefix1 v ∧
    (admissibleBasis7_to_aut v.1 v.2).1
        (basisPrefix2 standardAdmissibleBasis7) = basisPrefix2 v := by
  have hv := admissibleBasis7Equiv.right_inv v
  constructor
  · have h := congrArg basisPrefix1 hv
    simpa [admissibleBasis7Equiv, basisRestriction7, basisPrefix1,
      standardAdmissibleBasis7] using h
  · have h := congrArg basisPrefix2 hv
    simpa [admissibleBasis7Equiv, basisRestriction7, basisPrefix2,
      standardAdmissibleBasis7] using h

theorem admissibleBasis7_to_aut_maps_standard_basis
    (v : AdmissibleBasis7Carrier) :
    basisRestriction7 (admissibleBasis7_to_aut v.1 v.2) = v.1 := by
  have hv := admissibleBasis7Equiv.right_inv v
  exact congrArg Subtype.val hv

@[simp] theorem admissibleBasis7Equiv_symm_maps_ePlus
    (v : AdmissibleBasis7Carrier) :
    (admissibleBasis7Equiv.symm v).1 ePlus = basisPrefix1 v := by
  have h := admissibleBasis7_to_aut_maps_standard_prefixes v
  simpa [admissibleBasis7Equiv, standardAdmissibleBasis7] using h.1

@[simp] theorem admissibleBasis7Equiv_symm_maps_up0
    (v : AdmissibleBasis7Carrier) :
    (admissibleBasis7Equiv.symm v).1 up0 = basisPrefix2 v := by
  have h := admissibleBasis7_to_aut_maps_standard_prefixes v
  simpa [admissibleBasis7Equiv, standardAdmissibleBasis7] using h.2

def canonicalP : NontrivialIdempotent :=
  ⟨ePlus, by rfl, by decide, by decide⟩

def canonicalX : PeircePlusFiber canonicalP :=
  ⟨⟨up0, by rfl, by decide⟩, by rfl⟩

@[simp] theorem canonicalP_value : canonicalP.1 = ePlus :=
  rfl

@[simp] theorem canonicalX_value : canonicalX.1.1 = up0 :=
  rfl

theorem canonicalResidualFiber_card_le_64 :
    Fintype.card (ResidualFiber canonicalP canonicalX) ≤ 64 := by
  apply residualFiber_card_le_64_of_ePlus
  rfl

theorem basisRestriction7_mul_apply
    (f g : SplitOctF2Aut) (i : Fin 7) :
    basisRestriction7 (f * g) i = g.1 (basisRestriction7 f i) := by
  rfl

noncomputable def admissibleBasis7ActionCarrier
    (f : SplitOctF2Aut) (v : AdmissibleBasis7Carrier) :
    AdmissibleBasis7Carrier :=
  ⟨admissibleBasis7Action f v.1 v.2,
    admissibleBasis7Action_admissible f v.1 v.2⟩

theorem admissibleBasis7ActionCarrier_firstPrefix
    (f : SplitOctF2Aut) (v : AdmissibleBasis7Carrier) :
    basisPrefix1 (admissibleBasis7ActionCarrier f v) =
      f.1 (basisPrefix1 v) := by
  change (admissibleBasis7Action f v.1 v.2) 0 = _
  simpa [basisPrefix1] using
    (admissibleBasis7Action_apply f v.1 v.2 0)

theorem admissibleBasis7ActionCarrier_secondPrefix
    (f : SplitOctF2Aut) (v : AdmissibleBasis7Carrier) :
    basisPrefix2 (admissibleBasis7ActionCarrier f v) =
      f.1 (basisPrefix2 v) := by
  change (admissibleBasis7Action f v.1 v.2) 1 = _
  simpa [basisPrefix2] using
    (admissibleBasis7Action_apply f v.1 v.2 1)

theorem admissibleBasis7ActionCarrier_inv
    (f : SplitOctF2Aut) (v : AdmissibleBasis7Carrier) :
    admissibleBasis7ActionCarrier f⁻¹
        (admissibleBasis7ActionCarrier f v) = v := by
  apply Subtype.ext
  exact admissibleBasis7Action_inv f v.1 v.2

def residualUpperPairBitCode
    {p : NontrivialIdempotent} {x : PeircePlusFiber p} :
    ResidualUpperPair p x →
      (Fin 8 → Bool) × (Fin 8 → Bool) :=
  fun yz => (splitOctF2ToBits yz.1.1, splitOctF2ToBits yz.1.2)

theorem residualUpperPairBitCode_injective
    {p : NontrivialIdempotent} {x : PeircePlusFiber p} :
    Function.Injective (@residualUpperPairBitCode p x) := by
  intro a b h
  apply Subtype.ext
  apply Prod.ext
  · exact splitOctF2EquivBits.injective (congrArg Prod.fst h)
  · exact splitOctF2EquivBits.injective (congrArg Prod.snd h)

theorem residualFiber_card_le_upperPairBitCarrier
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    :
    Fintype.card (ResidualFiber p x) ≤
      Fintype.card ((Fin 8 → Bool) × (Fin 8 → Bool)) := by
  apply Fintype.card_le_of_injective
    (fun v => residualUpperPairBitCode (residualUpperPairOfFiberCarrier v))
  intro v w h
  apply residualFiberUpperPair_injective
  exact congrArg Subtype.val
    (residualUpperPairBitCode_injective h)

end InfoGeometry.Algebra.Zorn.G2FixedPrefixResidualConstraints
