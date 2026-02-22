import InfoGeometry.Krein.Automorphisms
import InfoGeometry.Architecture.SymmetricSpace

open InfoGeometry.Core

/-!
# Cartan Decomposition of the Krein Lie Algebra

Cartan decomposition for doubled-space endomorphisms induced by conjugation with `modularJ`.
-/

section KreinCartan

variable {E : Type}
variable [NormedAddCommGroup E]

open ContinuousLinearMap

section Metric

variable [InnerProductSpace ℝ E]

/-- Lie subalgebra of infinitesimal isometries of the neutral Hessian form. -/
abbrev kreinLieAlgebra :
    LieSubalgebra ℝ (DoubledSpace E →L[ℝ] DoubledSpace E) :=
  kreinLieSubalgebra (E := E)

end Metric

section Endomorphism

variable [NormedSpace ℝ E]

/-- Cartan involution `θ(A) = J ∘ A ∘ J`. -/
def cartanInvolution
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  (modularJ (E := E)).comp
    (A.comp (modularJ (E := E)))

lemma cartanInvolution_add
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    cartanInvolution (E := E) (A + B)
      = cartanInvolution (E := E) A + cartanInvolution (E := E) B := by
  apply ContinuousLinearMap.ext
  intro v
  simp [cartanInvolution]

lemma cartanInvolution_sub
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    cartanInvolution (E := E) (A - B)
      = cartanInvolution (E := E) A - cartanInvolution (E := E) B := by
  apply ContinuousLinearMap.ext
  intro v
  simp [cartanInvolution]

lemma cartanInvolution_smul
    (a : ℝ)
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    cartanInvolution (E := E) (a • A)
      = a • cartanInvolution (E := E) A := by
  apply ContinuousLinearMap.ext
  intro v
  simp [cartanInvolution]

lemma cartanInvolution_involutive
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    cartanInvolution (E := E) (cartanInvolution (E := E) A) = A := by
  apply ContinuousLinearMap.ext
  intro v
  rcases v with ⟨x, y⟩
  simp [cartanInvolution, modularJ]

/-- `cartanInvolution` packaged as an involution on doubled-space endomorphisms. -/
def cartanInvolutionAuto :
    InvolutiveAutomorphism (DoubledSpace E →L[ℝ] DoubledSpace E) where
  toFun := cartanInvolution (E := E)
  involutive := cartanInvolution_involutive (E := E)

instance cartanInvolutionAuto_preservesLinear :
    PreservesLinear
      (DoubledSpace E →L[ℝ] DoubledSpace E)
      (cartanInvolutionAuto (E := E)) where
  map_add := cartanInvolution_add (E := E)
  map_smul := cartanInvolution_smul (E := E)

lemma cartanInvolution_comp
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    cartanInvolution (E := E) (A.comp B)
      = (cartanInvolution (E := E) A).comp (cartanInvolution (E := E) B) := by
  apply ContinuousLinearMap.ext
  intro v
  rcases v with ⟨x, y⟩
  simp [cartanInvolution, modularJ, ContinuousLinearMap.comp_apply]

/-- `+1` eigenspace projection for the Cartan involution. -/
noncomputable def cartanPlus
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  Projector.plus (θ := cartanInvolutionAuto (E := E)) A

/-- `-1` eigenspace projection for the Cartan involution. -/
noncomputable def cartanMinus
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  Projector.minus (θ := cartanInvolutionAuto (E := E)) A

lemma cartan_decomposition
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    A = cartanPlus (E := E) A + cartanMinus (E := E) A := by
  simpa [_root_.cartanPlus, _root_.cartanMinus] using
    (Projector.decomposition (θ := cartanInvolutionAuto (E := E)) A)

lemma cartanPlus_eigen
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    cartanInvolution (E := E) (cartanPlus (E := E) A) =
      cartanPlus (E := E) A := by
  simpa [_root_.cartanPlus, cartanInvolutionAuto] using
    (Projector.plus_fixed (θ := cartanInvolutionAuto (E := E)) A)

lemma cartanMinus_eigen
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    cartanInvolution (E := E) (cartanMinus (E := E) A) =
      -(cartanMinus (E := E) A) := by
  simpa [_root_.cartanMinus, cartanInvolutionAuto] using
    (Projector.minus_neg_fixed (θ := cartanInvolutionAuto (E := E)) A)

/-- Cartan involution is compatible with the commutator. -/
lemma cartanInvolution_comm
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    cartanInvolution (E := E) (clmComm A B) =
      clmComm
        (cartanInvolution (E := E) A)
        (cartanInvolution (E := E) B) := by
  unfold clmComm
  rw [cartanInvolution_sub, cartanInvolution_comp, cartanInvolution_comp]

/-- Cartan involution intertwines the ambient Lie bracket. -/
lemma cartanInvolution_lie
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    cartanInvolution (E := E) ⁅A, B⁆
      = ⁅cartanInvolution (E := E) A, cartanInvolution (E := E) B⁆ := by
  simpa [clmComm] using cartanInvolution_comm (E := E) A B

lemma clmComm_neg_right
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    clmComm A (-B) = -clmComm A B := by
  unfold clmComm
  calc
    A.comp (-B) - (-B).comp A
        = -(A.comp B) - (-(B.comp A)) := by simp
    _ = -(A.comp B - B.comp A) := by abel_nf

lemma clmComm_neg_neg
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    clmComm (-A) (-B) = clmComm A B := by
  unfold clmComm
  simp [sub_eq_add_neg]

lemma cartan_bracket_kk
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : cartanInvolution (E := E) A = A)
    (hB : cartanInvolution (E := E) B = B) :
    cartanInvolution (E := E) (clmComm A B) = clmComm A B := by
  simp [cartanInvolution_comm, hA, hB]

lemma cartan_bracket_kp
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : cartanInvolution (E := E) A = A)
    (hB : cartanInvolution (E := E) B = -B) :
    cartanInvolution (E := E) (clmComm A B) = -(clmComm A B) := by
  calc
    cartanInvolution (E := E) (clmComm A B)
        = clmComm (cartanInvolution (E := E) A) (cartanInvolution (E := E) B) := by
            rw [cartanInvolution_comm]
    _ = clmComm A (-B) := by rw [hA, hB]
    _ = -(clmComm A B) := clmComm_neg_right (E := E) A B

lemma cartan_bracket_pp
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E)
    (hA : cartanInvolution (E := E) A = -A)
    (hB : cartanInvolution (E := E) B = -B) :
    cartanInvolution (E := E) (clmComm A B) = clmComm A B := by
  calc
    cartanInvolution (E := E) (clmComm A B)
        = clmComm (cartanInvolution (E := E) A) (cartanInvolution (E := E) B) := by
            rw [cartanInvolution_comm]
    _ = clmComm (-A) (-B) := by rw [hA, hB]
    _ = clmComm A B := clmComm_neg_neg (E := E) A B

end Endomorphism

section Metric

variable [InnerProductSpace ℝ E]

/-- `cartanInvolution` is conjugation by `modularJEquiv`. -/
lemma cartanInvolution_eq_conjugateCLM
    (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    cartanInvolution (E := E) A
      = conjugateCLM (E := E) (modularJEquiv (E := E)) A := by
  have hSymm :
      ((modularJEquiv (E := E)).symm : DoubledSpace E →L[ℝ] DoubledSpace E)
        = modularJ (E := E) := by
    apply ContinuousLinearMap.ext
    intro v
    rcases v with ⟨x, y⟩
    have hfst : ((modularJEquiv (E := E)).symm (x, y)).2 = x := by
      exact congrArg Prod.fst ((modularJEquiv (E := E)).right_inv (x, y))
    have hsnd : ((modularJEquiv (E := E)).symm (x, y)).1 = y := by
      exact congrArg Prod.snd ((modularJEquiv (E := E)).right_inv (x, y))
    exact Prod.ext hsnd hfst
  rw [conjugateCLM, hSymm]
  rfl

/-- Cartan involution preserves infinitesimal isometries. -/
lemma cartanInvolution_preserves
    {A : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hA : IsInfinitesimalIsometry (E := E) A) :
    IsInfinitesimalIsometry (E := E) (cartanInvolution (E := E) A) := by
  rw [cartanInvolution_eq_conjugateCLM (E := E) A]
  exact infinitesimalIsometry_conjugate
    (E := E)
    (U := modularJEquiv (E := E))
    (hU := by
      simpa [modularJEquiv] using modularJ_preservesMetric (E := E))
    hA

/-- Cartan involution as a Lie endomorphism on the infinitesimal-isometry Lie algebra. -/
def cartanInvolutionLie :
    kreinLieAlgebra (E := E) →ₗ⁅ℝ⁆ kreinLieAlgebra (E := E) where
  toLinearMap :=
    { toFun := fun A =>
        ⟨cartanInvolution (E := E) (A : DoubledSpace E →L[ℝ] DoubledSpace E),
          cartanInvolution_preserves (E := E) A.property⟩
      map_add' := by
        intro A B
        apply Subtype.ext
        simp [cartanInvolution_add]
      map_smul' := by
        intro a A
        apply Subtype.ext
        simp [cartanInvolution_smul] }
  map_lie' := by
    intro A B
    apply Subtype.ext
    simpa [clmComm] using
      cartanInvolution_comm
        (E := E)
        (A : DoubledSpace E →L[ℝ] DoubledSpace E)
        (B : DoubledSpace E →L[ℝ] DoubledSpace E)

lemma cartanInvolutionLie_involutive
    (A : kreinLieAlgebra (E := E)) :
    cartanInvolutionLie (E := E) (cartanInvolutionLie (E := E) A) = A := by
  apply Subtype.ext
  change cartanInvolution (E := E)
      (cartanInvolution (E := E) (A : DoubledSpace E →L[ℝ] DoubledSpace E))
      = (A : DoubledSpace E →L[ℝ] DoubledSpace E)
  exact cartanInvolution_involutive (E := E) (A : DoubledSpace E →L[ℝ] DoubledSpace E)

/-- Group-level Cartan involution `Θ(U) = J ∘ U ∘ J` on the Hessian orthogonal group. -/
def cartanInvolutionGroup
    (U : HessianOrthogonalGroup E) :
    HessianOrthogonalGroup E :=
  modularJHessianOrthogonal (E := E) * U * modularJHessianOrthogonal (E := E)

lemma modularJHessianOrthogonal_sq :
    (modularJHessianOrthogonal (E := E) : HessianOrthogonalGroup E)
      * modularJHessianOrthogonal (E := E) = 1 := by
  have hSymm : (modularJEquiv (E := E)).symm = modularJEquiv (E := E) := by
    apply DFunLike.ext
    intro v
    rcases v with ⟨x, y⟩
    have hfst : ((modularJEquiv (E := E)).symm (x, y)).2 = x := by
      exact congrArg Prod.fst ((modularJEquiv (E := E)).right_inv (x, y))
    have hsnd : ((modularJEquiv (E := E)).symm (x, y)).1 = y := by
      exact congrArg Prod.snd ((modularJEquiv (E := E)).right_inv (x, y))
    exact Prod.ext hsnd hfst
  have hInv :
      (modularJHessianOrthogonal (E := E) : HessianOrthogonalGroup E)⁻¹
        = modularJHessianOrthogonal (E := E) := by
    apply Subtype.ext
    simpa [modularJHessianOrthogonal] using hSymm
  let J : HessianOrthogonalGroup E := modularJHessianOrthogonal (E := E)
  calc
    J * J = J⁻¹ * J := by rw [hInv]
    _ = 1 := inv_mul_cancel J

lemma cartanInvolutionGroup_mul
    (U V : HessianOrthogonalGroup E) :
    cartanInvolutionGroup (E := E) (U * V)
      = cartanInvolutionGroup (E := E) U * cartanInvolutionGroup (E := E) V := by
  let J : HessianOrthogonalGroup E := modularJHessianOrthogonal (E := E)
  have hJ2 : J * J = (1 : HessianOrthogonalGroup E) := by
    simpa [J] using modularJHessianOrthogonal_sq (E := E)
  calc
    cartanInvolutionGroup (E := E) (U * V)
        = J * U * V * J := by
            simp [cartanInvolutionGroup, J, mul_assoc]
    _ = J * U * ((J * J) * V) * J := by simp [hJ2]
    _ = (J * U * J) * (J * V * J) := by simp [mul_assoc]
    _ = cartanInvolutionGroup (E := E) U * cartanInvolutionGroup (E := E) V := by
          simp [cartanInvolutionGroup, J, mul_assoc]

lemma cartanInvolutionGroup_involutive
    (U : HessianOrthogonalGroup E) :
    cartanInvolutionGroup (E := E) (cartanInvolutionGroup (E := E) U) = U := by
  let J : HessianOrthogonalGroup E := modularJHessianOrthogonal (E := E)
  have hJ2 : J * J = (1 : HessianOrthogonalGroup E) := by
    simpa [J] using modularJHessianOrthogonal_sq (E := E)
  calc
    cartanInvolutionGroup (E := E) (cartanInvolutionGroup (E := E) U)
        = J * (J * U * J) * J := by
            simp [cartanInvolutionGroup, J]
    _ = (J * J) * U * (J * J) := by
          simp [mul_assoc]
    _ = U := by simp [hJ2]

/-- Cartan involution on `HessianOrthogonalGroup E` from conjugation by `modularJ`. -/
def hessianOrthogonalInvolutiveMulAut :
    InfoGeometry.Architecture.InvolutiveMulAut (HessianOrthogonalGroup E) := by
  refine ⟨?_, ?_⟩
  · exact
      { toEquiv :=
          { toFun := cartanInvolutionGroup (E := E)
            invFun := cartanInvolutionGroup (E := E)
            left_inv := by
              intro U
              exact cartanInvolutionGroup_involutive (E := E) U
            right_inv := by
              intro U
              exact cartanInvolutionGroup_involutive (E := E) U }
        map_mul' := by
          intro U V
          exact cartanInvolutionGroup_mul (E := E) U V }
  · intro U
    exact cartanInvolutionGroup_involutive (E := E) U

/-- Cartan involution on `HessianOrthogonalGroup E` from conjugation by `modularJ`. -/
def hessianOrthogonalCartanInvolution :
    InfoGeometry.Architecture.CartanInvolution (HessianOrthogonalGroup E) :=
  InfoGeometry.Architecture.CartanInvolution.ofMulAutInvolution
    (hessianOrthogonalInvolutiveMulAut (E := E)).1
    (hessianOrthogonalInvolutiveMulAut (E := E)).2

/-- Cartan-Loos reflection on the Hessian orthogonal group. -/
def hessianSymmetry
    (x y : HessianOrthogonalGroup E) :
    HessianOrthogonalGroup E :=
  InfoGeometry.Architecture.cartanSymmetry
    (G := HessianOrthogonalGroup E)
    (hessianOrthogonalCartanInvolution (E := E)) x y

lemma hessianSymmetry_involutive
    (x y : HessianOrthogonalGroup E) :
    hessianSymmetry (E := E) x (hessianSymmetry (E := E) x y) = y := by
  simpa [hessianSymmetry] using
    InfoGeometry.Architecture.cartanSymmetry_involutive
      (G := HessianOrthogonalGroup E)
      (hessianOrthogonalCartanInvolution (E := E)) x y

lemma hessianSymmetry_fixpoint
    (x : HessianOrthogonalGroup E) :
    hessianSymmetry (E := E) x x = x := by
  simpa [hessianSymmetry] using
    InfoGeometry.Architecture.cartanSymmetry_fixpoint
      (G := HessianOrthogonalGroup E)
      (hessianOrthogonalCartanInvolution (E := E)) x

/-- Symmetric space structure induced by the group-level Cartan involution. -/
def symmetricSpaceHessian :
    InfoGeometry.Architecture.SymmetricSpace (HessianOrthogonalGroup E) where
  symmetry := hessianSymmetry (E := E)
  symm_involutive := hessianSymmetry_involutive (E := E)
  symm_fixpoint := hessianSymmetry_fixpoint (E := E)

/-- Fixed-point subgroup `K = Fix(Θ)` of the group-level Cartan involution. -/
def hessianFixedSubgroup : Subgroup (HessianOrthogonalGroup E) :=
  InfoGeometry.Architecture.fixedSubgroup
    (hessianOrthogonalInvolutiveMulAut (E := E)).1

@[simp]
lemma mem_hessianFixedSubgroup_iff
    (g : HessianOrthogonalGroup E) :
    g ∈ hessianFixedSubgroup (E := E) ↔ cartanInvolutionGroup (E := E) g = g := by
  simp [hessianFixedSubgroup, hessianOrthogonalInvolutiveMulAut]

/-- Symmetric pair `(G, K)` with `K = Fix(Θ)` on the Hessian orthogonal group. -/
def hessianSymmetricPair :
    InfoGeometry.Architecture.SymmetricPair (HessianOrthogonalGroup E) :=
  InfoGeometry.Architecture.symmetricPairOfInvolutiveMulAut
    (hessianOrthogonalInvolutiveMulAut (E := E))

/-- Right-coset equivalence for `G / K` with `K = Fix(Θ)`. -/
def hessianRightCosetSetoid : Setoid (HessianOrthogonalGroup E) where
  r x y := ∃ k : HessianOrthogonalGroup E,
    k ∈ hessianFixedSubgroup (E := E) ∧ y = x * k
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro x
      refine ⟨1, (hessianFixedSubgroup (E := E)).one_mem, by simp⟩
    · intro x y hxy
      rcases hxy with ⟨k, hk, rfl⟩
      refine ⟨k⁻¹, (hessianFixedSubgroup (E := E)).inv_mem hk, ?_⟩
      calc
        x = x * (k * k⁻¹) := by simp
        _ = (x * k) * k⁻¹ := by simp [mul_assoc]
    · intro x y z hxy hyz
      rcases hxy with ⟨k₁, hk₁, rfl⟩
      rcases hyz with ⟨k₂, hk₂, rfl⟩
      refine ⟨k₁ * k₂, (hessianFixedSubgroup (E := E)).mul_mem hk₁ hk₂, ?_⟩
      simp [mul_assoc]

/-- Quotient model of the symmetric space `G / K` (right cosets). -/
def HessianQuotient : Type _ :=
  Quotient (hessianRightCosetSetoid (E := E))

/-- Canonical projection `G → G / K`. -/
def toHessianQuotient
    (g : HessianOrthogonalGroup E) : HessianQuotient (E := E) :=
  Quotient.mk'' g

lemma hessianSymmetry_mul_right
    (x y : HessianOrthogonalGroup E)
    {k : HessianOrthogonalGroup E}
    (hk : k ∈ hessianFixedSubgroup (E := E)) :
    hessianSymmetry (E := E) x (y * k) = hessianSymmetry (E := E) x y * k := by
  have hkfix : (hessianOrthogonalCartanInvolution (E := E)).toMulAut k = k := by
    simpa [hessianFixedSubgroup] using hk
  unfold hessianSymmetry InfoGeometry.Architecture.cartanSymmetry
  simp [mul_assoc, hkfix]

lemma hessianSymmetry_mul_left
    (x y : HessianOrthogonalGroup E)
    {k : HessianOrthogonalGroup E}
    (hk : k ∈ hessianFixedSubgroup (E := E)) :
    hessianSymmetry (E := E) (x * k) y = hessianSymmetry (E := E) x y := by
  have hkfix : (hessianOrthogonalCartanInvolution (E := E)).toMulAut k = k := by
    simpa [hessianFixedSubgroup] using hk
  unfold hessianSymmetry InfoGeometry.Architecture.cartanSymmetry
  simp [mul_assoc, hkfix]

/-- Symmetry descended to the quotient `G / K`. -/
def hessianQuotientSymmetry :
    HessianQuotient (E := E) → HessianQuotient (E := E) → HessianQuotient (E := E) :=
  Quotient.lift₂
    (fun x y => Quotient.mk'' (hessianSymmetry (E := E) x y))
    (by
      intro x₁ y₁ x₂ y₂ hx hy
      rcases hx with ⟨kx, hkx, rfl⟩
      rcases hy with ⟨ky, hky, rfl⟩
      apply Quotient.sound
      refine ⟨ky, hky, ?_⟩
      calc
        hessianSymmetry (E := E) (x₁ * kx) (y₁ * ky)
            = hessianSymmetry (E := E) x₁ (y₁ * ky) := by
                simpa using
                  hessianSymmetry_mul_left
                    (E := E) (x := x₁) (y := y₁ * ky) hkx
        _ = hessianSymmetry (E := E) x₁ y₁ * ky := by
              simpa using
                hessianSymmetry_mul_right
                  (E := E) (x := x₁) (y := y₁) hky)

lemma hessianQuotientSymmetry_mk
    (x y : HessianOrthogonalGroup E) :
    hessianQuotientSymmetry (E := E) (toHessianQuotient (E := E) x)
      (toHessianQuotient (E := E) y)
      = toHessianQuotient (E := E) (hessianSymmetry (E := E) x y) := rfl

lemma hessianQuotientSymmetry_involutive
    (x y : HessianQuotient (E := E)) :
    hessianQuotientSymmetry (E := E) x (hessianQuotientSymmetry (E := E) x y) = y := by
  refine Quotient.inductionOn₂ x y ?_
  intro a b
  simpa [hessianQuotientSymmetry_mk] using
    congrArg (toHessianQuotient (E := E))
      (hessianSymmetry_involutive (E := E) a b)

lemma hessianQuotientSymmetry_fixpoint
    (x : HessianQuotient (E := E)) :
    hessianQuotientSymmetry (E := E) x x = x := by
  refine Quotient.inductionOn x ?_
  intro a
  simpa [hessianQuotientSymmetry_mk] using
    congrArg (toHessianQuotient (E := E))
      (hessianSymmetry_fixpoint (E := E) a)

/-- Symmetric-space structure on the quotient model `G / K`. -/
def symmetricSpaceHessianQuotient :
    InfoGeometry.Architecture.SymmetricSpace (HessianQuotient (E := E)) where
  symmetry := hessianQuotientSymmetry (E := E)
  symm_involutive := hessianQuotientSymmetry_involutive (E := E)
  symm_fixpoint := hessianQuotientSymmetry_fixpoint (E := E)

end Metric

end KreinCartan
