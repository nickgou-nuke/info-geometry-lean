import InfoGeometry.External.Auto.QuadraticConfiguration3
import InfoGeometry.External.Auto.NonIsoConf3OrlikSolomon
/-!
# De Rham/cooperad candidates for three non-isotropic quadric configurations

For

`F_Q(ℂ^D,3) = {(x₁,x₂,x₃) : q(xᵢ-xⱼ) ≠ 0}`

this file formalizes the finite algebraic alternatives that must be separated
before claiming a de Rham computation:

* the translation-reduced problem is already represented by
  `QuadraticConfiguration3.Reduced3`;
* the **product/Leray-collapse candidate** has formal Poincare signature
  `(1+t)^3(1+t^(D-1))^2`, total rank `32`;
* the **Orlik--Solomon alpha-relation candidate** has alpha basis of size `6`
  and, after two flux bits, total rank `24`;
* the arity-three cooperad edge bookkeeping is inherited from
  `QuadraticConfiguration3`.

No analytic de Rham theorem is asserted here.  The finite data below records the
two algebraic models and the arity-three edge maps used for later comparison.
-/

namespace NonIsoConf3DeRhamCooperad

open QuadraticConfiguration3

/-- The two finite candidate presentations currently under comparison. -/
inductive ModelChoice where
  | productLeray
  | osAlpha
  deriving DecidableEq, Repr

/-- Exterior-product signature for `(1+t)^3(1+t^(D-1))^2`: three phase bits and
two flux bits. -/
structure ProductBasis where
  phase : Fin 3 → Bool
  flux : Fin 2 → Bool
  deriving DecidableEq, Fintype, Repr

/-- The product/Leray-collapse candidate has total rank `32`. -/
theorem productBasis_card : Fintype.card ProductBasis = 32 := by
  rw [show Fintype.card ProductBasis = Fintype.card ((Fin 3 → Bool) × (Fin 2 → Bool)) from ?_]
  · simp [Fintype.card_prod]
  · exact Fintype.card_congr
      { toFun := fun b => (b.phase, b.flux)
        invFun := fun p => ⟨p.1, p.2⟩
        left_inv := by
          intro b
          cases b
          rfl
        right_inv := by
          intro p
          cases p
          rfl }

/-- Degree of a product-basis monomial for ambient dimension `D`. -/
def productDegree (D : ℕ) (b : ProductBasis) : ℕ :=
  (Finset.univ.filter (fun i : Fin 3 => b.phase i)).card +
    (Finset.univ.filter (fun i : Fin 2 => b.flux i)).card * (D - 1)

/-- Alpha normal forms after imposing one Arnold triangle relation in degree two.
This is the standard arity-three Orlik--Solomon vector-space skeleton:
`1`, three degree-one edges, and two degree-two normal forms. -/
inductive OSAlphaBasis where
  | one
  | a12
  | a13
  | a23
  | a12a13
  | a12a23
  deriving DecidableEq, Fintype, Repr

/-- Degree in the alpha Orlik--Solomon skeleton. -/
def osAlphaDegree : OSAlphaBasis → ℕ
  | OSAlphaBasis.one => 0
  | OSAlphaBasis.a12 => 1
  | OSAlphaBasis.a13 => 1
  | OSAlphaBasis.a23 => 1
  | OSAlphaBasis.a12a13 => 2
  | OSAlphaBasis.a12a23 => 2

/-- The arity-three alpha Orlik--Solomon skeleton has rank `6`, not `8`. -/
theorem osAlphaBasis_card : Fintype.card OSAlphaBasis = 6 := by
  rw [show Fintype.card OSAlphaBasis = Fintype.card (Fin 6) from ?_]
  · simp
  · exact Fintype.card_congr
      { toFun := fun x =>
          match x with
          | OSAlphaBasis.one => 0
          | OSAlphaBasis.a12 => 1
          | OSAlphaBasis.a13 => 2
          | OSAlphaBasis.a23 => 3
          | OSAlphaBasis.a12a13 => 4
          | OSAlphaBasis.a12a23 => 5
        invFun := fun i =>
          match i with
          | ⟨0, _⟩ => OSAlphaBasis.one
          | ⟨1, _⟩ => OSAlphaBasis.a12
          | ⟨2, _⟩ => OSAlphaBasis.a13
          | ⟨3, _⟩ => OSAlphaBasis.a23
          | ⟨4, _⟩ => OSAlphaBasis.a12a13
          | ⟨_, _⟩ => OSAlphaBasis.a12a23
        left_inv := by
          intro x
          cases x <;> rfl
        right_inv := by
          intro i
          fin_cases i <;> rfl }

/-- Two independent flux bits, contributing `(1+t^(D-1))^2`. -/
structure FluxBasis where
  flux : Fin 2 → Bool
  deriving DecidableEq, Fintype, Repr

/-- The two-flux exterior skeleton has total rank `4`. -/
theorem fluxBasis_card : Fintype.card FluxBasis = 4 := by
  rw [show Fintype.card FluxBasis = Fintype.card (Fin 2 → Bool) from ?_]
  · simp
  · exact Fintype.card_congr
      { toFun := fun b => b.flux
        invFun := fun f => ⟨f⟩
        left_inv := by
          intro b
          cases b
          rfl
        right_inv := by
          intro f
          rfl }

/-- OS-alpha plus two flux bits: rank `6*4=24`. -/
structure OSFluxBasis where
  alpha : OSAlphaBasis
  flux : FluxBasis
  deriving DecidableEq, Fintype, Repr

/-- The OS-alpha candidate has total rank `24`. -/
theorem osFluxBasis_card : Fintype.card OSFluxBasis = 24 := by
  rw [show Fintype.card OSFluxBasis = Fintype.card (OSAlphaBasis × FluxBasis) from ?_]
  · rw [Fintype.card_prod, osAlphaBasis_card, fluxBasis_card]
  · exact Fintype.card_congr
      { toFun := fun b => (b.alpha, b.flux)
        invFun := fun p => ⟨p.1, p.2⟩
        left_inv := by
          intro b
          cases b
          rfl
        right_inv := by
          intro p
          cases p
          rfl }

/-- Degree in the OS-alpha plus flux skeleton. -/
def osFluxDegree (D : ℕ) (b : OSFluxBasis) : ℕ :=
  osAlphaDegree b.alpha +
    (Finset.univ.filter (fun i : Fin 2 => b.flux.flux i)).card * (D - 1)

/-- The product model has two more alpha monomials than the OS-alpha model. -/
theorem product_vs_os_rank_gap :
    Fintype.card ProductBasis - Fintype.card OSFluxBasis = 8 := by
  rw [productBasis_card, osFluxBasis_card]

/-- The three formal alpha generators. -/
inductive AlphaEdge where
  | a12 | a13 | a23
  deriving DecidableEq, Fintype, Repr

/-- The three formal beta/flux edge labels.  A complete de Rham theorem must
explain whether there are three independent beta edge classes or only two
independent flux classes after relations/Gysin constraints. -/
inductive BetaEdge where
  | b12 | b13 | b23
  deriving DecidableEq, Fintype, Repr

/-- Named Arnold triangle relation in degree two. -/
structure ArnoldRelation where
  name : String
  degree : ℕ
  deriving Repr

/-- The alpha Arnold relation in degree two. -/
def alphaArnold : ArnoldRelation where
  name := "alpha12*alpha23 - alpha12*alpha13 + alpha23*alpha13 = 0"
  degree := 2

@[simp] theorem alphaArnold_degree : alphaArnold.degree = 2 := rfl

/-- Reuse the arity-three cooperad edge bookkeeping from `QuadraticConfiguration3`. -/
def cooperadOnAlpha (b : BlockDecomp3) (e : Edge3) : TargetFactor × GenKind :=
  cooperadGen b ⟨e, GenKind.alpha⟩

/-- Reuse the arity-three cooperad edge bookkeeping for beta generators. -/
def cooperadOnBeta (b : BlockDecomp3) (e : Edge3) : TargetFactor × GenKind :=
  cooperadGen b ⟨e, GenKind.beta⟩

/-- Every two-point insertion has an internal alpha edge. -/
theorem cooperad_alpha_has_internal_edge (b : BlockDecomp3) :
    ∃ e : Edge3, cooperadOnAlpha b e = (TargetFactor.internal, GenKind.alpha) := by
  cases b
  · exact ⟨Edge3.e12, rfl⟩
  · exact ⟨Edge3.e13, rfl⟩
  · exact ⟨Edge3.e23, rfl⟩

/-- Every two-point insertion has an internal beta edge. -/
theorem cooperad_beta_has_internal_edge (b : BlockDecomp3) :
    ∃ e : Edge3, cooperadOnBeta b e = (TargetFactor.internal, GenKind.beta) := by
  cases b
  · exact ⟨Edge3.e12, rfl⟩
  · exact ⟨Edge3.e13, rfl⟩
  · exact ⟨Edge3.e23, rfl⟩

/-- Data needed to select one finite model for an even-dimensional configuration
problem after translation reduction. -/
structure ConcreteDeRhamCooperadData (D : ℕ) where
  evenD : D % 2 = 0
  dimensionAtLeastFour : 4 ≤ D
  translationReduction : Nonempty (Config3 D ≃ Reduced3 D)
  relationChoice : ModelChoice

/-- If the Leray product candidate is the correct analytic theorem, the total
rank is `32`.  This theorem only packages the finite conclusion under that
explicit choice. -/
theorem product_candidate_rank {D : ℕ} (S : ConcreteDeRhamCooperadData D)
    (_hChoice : S.relationChoice = ModelChoice.productLeray) :
    Fintype.card ProductBasis = 32 :=
  productBasis_card

/-- If the OS-alpha candidate is the correct analytic theorem, the finite
normal-form rank is `24`. -/
theorem os_alpha_candidate_rank {D : ℕ} (S : ConcreteDeRhamCooperadData D)
    (_hChoice : S.relationChoice = ModelChoice.osAlpha) :
    Fintype.card OSFluxBasis = 24 :=
  osFluxBasis_card

end NonIsoConf3DeRhamCooperad
