import InfoGeometry.Canonical.HypercomplexOneParameterFlows
import InfoGeometry.Canonical.MeanValueInvariant
import InfoGeometry.Clifford.Cl55RotorMonodromyBridge
import InfoGeometry.External.Auto.JordanBlock2
import InfoGeometry.LLM.TransformerArchitecture
import InfoGeometry.Modular.SchrodingerFlow
import Mathlib.Tactic

/-!
# Positional encodings as representations of translation

This module extracts the exact algebraic and analytic content of linear,
translation-covariant positional encodings.

The formalization is organized in four layers.

1. A raw matrix calculation rewrites the transformed query-key score through
   the relative operator `F(t)ᵀ * G(s)`.
2. A normalized invertible factorization whose score operator is invariant
   under simultaneous translation canonically determines a group
   representation of `(ℝ, +)`.
3. If that representation is differentiable at zero, its value at every time
   is the Banach-algebra exponential of its infinitesimal generator.
4. The existing rotor theorem is exposed through the repository's
   `RotaryPositionalLayer` interface, and the existing square-zero Jordan block
   gives an exact parabolic realization of a linear ALiBi penalty.

No diagonalization or spectral-decomposition hypothesis is used.  The
elliptic, hyperbolic, and parabolic normal modes already owned by
`HypercomplexOneParameterFlows` remain the concrete low-dimensional models.
-/

noncomputable section

namespace InfoGeometry.LLM.PositionalEncodingRepresentation

open Matrix
open Multiplicative
open InfoGeometry.Canonical.HypercomplexOneParameterFlows

universe u v w

/-! ## 1. Raw score transport -/

/-- The bilinear query-key score used before softmax normalization. -/
def attentionScore {ι : Type u} {R : Type v} [Fintype ι] [CommSemiring R]
    (q k : ι → R) : R :=
  dotProduct q k

/-- Applying linear query and key modifiers transports their score through
`FᵀG`. -/
theorem transformed_attentionScore_eq_relative
    {ι : Type u} {R : Type v} [Fintype ι] [CommSemiring R]
    (F G : Matrix ι ι R) (q k : ι → R) :
    attentionScore (F *ᵥ q) (G *ᵥ k) =
      attentionScore q ((F.transpose * G) *ᵥ k) := by
  unfold attentionScore
  rw [← Matrix.vecMul_transpose]
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.vecMul_vecMul]
  rw [← Matrix.dotProduct_mulVec]

/-- If `F(t)ᵀG(s)` is a function of `t - s`, then every transformed score is a
function of the same relative position. -/
theorem transformed_attentionScore_depends_only_on_difference
    {T : Type w} [AddGroup T]
    {ι : Type u} {R : Type v} [Fintype ι] [CommSemiring R]
    (F G A : T → Matrix ι ι R)
    (hrelative : ∀ t s, (F t).transpose * G s = A (t - s))
    (t s : T) (q k : ι → R) :
    attentionScore ((F t) *ᵥ q) ((G s) *ᵥ k) =
      attentionScore q ((A (t - s)) *ᵥ k) := by
  rw [transformed_attentionScore_eq_relative, hrelative]

/-! ## 2. Translation covariance forces a representation -/

/--
A normalized invertible factorization of a translation-covariant score
operator.

`queryFactor` represents the already-transposed query modifier `F(t)ᵀ`, while
`keyFactor` represents `G(t)`.  The factors are stored as units because the
normalization `F(t)ᵀG(t)=1` is precisely the invertible regime in which the
relative operator can be composed without one-sided-cancellation assumptions.
-/
structure TranslationCovariantModifiers (A : Type u) [Monoid A] where
  queryFactor : ℝ → Units A
  keyFactor : ℝ → Units A
  shift_invariant :
    ∀ t s r,
      queryFactor (t + r) * keyFactor (s + r) =
        queryFactor t * keyFactor s
  normalized : ∀ t, queryFactor t * keyFactor t = 1

namespace TranslationCovariantModifiers

variable {A : Type u} [Monoid A]

/-- Equal-time normalization identifies the key factor with the inverse query
factor. -/
theorem keyFactor_eq_inv_queryFactor
    (M : TranslationCovariantModifiers A) (t : ℝ) :
    M.keyFactor t = (M.queryFactor t)⁻¹ := by
  calc
    M.keyFactor t = 1 * M.keyFactor t := by simp
    _ = ((M.queryFactor t)⁻¹ * M.queryFactor t) * M.keyFactor t := by simp
    _ = (M.queryFactor t)⁻¹ * (M.queryFactor t * M.keyFactor t) := by
      rw [mul_assoc]
    _ = (M.queryFactor t)⁻¹ * 1 := by rw [M.normalized t]
    _ = (M.queryFactor t)⁻¹ := by simp

@[simp]
theorem keyFactor_mul_queryFactor
    (M : TranslationCovariantModifiers A) (t : ℝ) :
    M.keyFactor t * M.queryFactor t = 1 := by
  rw [M.keyFactor_eq_inv_queryFactor]
  exact inv_mul _

/-- Relative transport from time zero to time `t`. -/
def relativeUnit (M : TranslationCovariantModifiers A) (t : ℝ) : Units A :=
  M.queryFactor t * M.keyFactor 0

/-- The relative transport coerced to the ambient monoid. -/
def relativeModifier (M : TranslationCovariantModifiers A) (t : ℝ) : A :=
  M.relativeUnit t

@[simp]
theorem relativeUnit_zero (M : TranslationCovariantModifiers A) :
    M.relativeUnit 0 = 1 := by
  exact M.normalized 0

/-- Simultaneous-translation invariance and equal-time normalization force the
one-parameter group law. -/
theorem relativeUnit_add
    (M : TranslationCovariantModifiers A) (s t : ℝ) :
    M.relativeUnit (s + t) = M.relativeUnit s * M.relativeUnit t := by
  have hshift :
      M.queryFactor (s + t) * M.keyFactor t =
        M.queryFactor s * M.keyFactor 0 := by
    simpa using M.shift_invariant s 0 t
  calc
    M.relativeUnit (s + t) =
        M.queryFactor (s + t) *
          ((M.keyFactor t * M.queryFactor t) * M.keyFactor 0) := by
      simp [relativeUnit]
    _ = (M.queryFactor (s + t) * M.keyFactor t) *
          (M.queryFactor t * M.keyFactor 0) := by
      simp only [mul_assoc]
    _ = (M.queryFactor s * M.keyFactor 0) *
          (M.queryFactor t * M.keyFactor 0) := by
      rw [hshift]
    _ = M.relativeUnit s * M.relativeUnit t := rfl

/-- The relative positional operator as a native monoid homomorphism from the
multiplicative wrapper of `(ℝ, +)`. -/
def relativeHom (M : TranslationCovariantModifiers A) :
    Multiplicative ℝ →* Units A where
  toFun t := M.relativeUnit (toAdd t)
  map_one' := by
    simpa using M.relativeUnit_zero
  map_mul' s t := by
    simpa using M.relativeUnit_add (toAdd s) (toAdd t)

/-- Translation-covariant modifiers determine the canonical repository-owned
real one-parameter flow. -/
def toRealOneParameterFlow (M : TranslationCovariantModifiers A) :
    RealOneParameterFlow A where
  flowHom := M.relativeHom

@[simp]
theorem toRealOneParameterFlow_evalUnit
    (M : TranslationCovariantModifiers A) (t : ℝ) :
    M.toRealOneParameterFlow.evalUnit t = M.relativeUnit t := rfl

@[simp]
theorem toRealOneParameterFlow_eval
    (M : TranslationCovariantModifiers A) (t : ℝ) :
    M.toRealOneParameterFlow.eval t = M.relativeModifier t := rfl

@[simp]
theorem flow_evalUnit_zero (F : RealOneParameterFlow A) :
    F.evalUnit 0 = 1 := by
  apply Units.ext
  simpa [RealOneParameterFlow.eval] using F.eval_zero

theorem flow_evalUnit_add (F : RealOneParameterFlow A) (s t : ℝ) :
    F.evalUnit (s + t) = F.evalUnit s * F.evalUnit t := by
  apply Units.ext
  simpa [RealOneParameterFlow.eval] using F.eval_add s t

/-- Every canonical one-parameter flow yields a normalized
translation-covariant query/key factorization. -/
def ofFlow (F : RealOneParameterFlow A) : TranslationCovariantModifiers A where
  queryFactor t := F.evalUnit t
  keyFactor t := F.evalUnit (-t)
  shift_invariant t s r := by
    calc
      F.evalUnit (t + r) * F.evalUnit (-(s + r)) =
          F.evalUnit ((t + r) + -(s + r)) :=
        (flow_evalUnit_add F (t + r) (-(s + r))).symm
      _ = F.evalUnit (t + -s) := by congr 1 <;> ring
      _ = F.evalUnit t * F.evalUnit (-s) :=
        flow_evalUnit_add F t (-s)
  normalized t := by
    calc
      F.evalUnit t * F.evalUnit (-t) = F.evalUnit (t + -t) :=
        (flow_evalUnit_add F t (-t)).symm
      _ = 1 := by simp

@[simp]
theorem relativeUnit_ofFlow (F : RealOneParameterFlow A) (t : ℝ) :
    (ofFlow F).relativeUnit t = F.evalUnit t := by
  simp [ofFlow, relativeUnit]

@[simp]
theorem relativeModifier_ofFlow (F : RealOneParameterFlow A) (t : ℝ) :
    (ofFlow F).relativeModifier t = F.eval t := by
  simp [relativeModifier, RealOneParameterFlow.eval]

end TranslationCovariantModifiers

/-! ## 3. Differentiable representations are exponentials -/

section ExponentialClassification

open InfoGeometry.Modular.SchrodingerFlow
open InfoGeometry.Canonical.MeanValueInvariant

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

local notation "EndE" => E →L[ℝ] E

noncomputable local instance : NormedRing EndE := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndE := inferInstance
noncomputable local instance : NormedAlgebra ℚ EndE :=
  NormedAlgebra.restrictScalars ℚ ℝ EndE

/-- The operator exponential together with its value at negative time as an
explicit unit. -/
def exponentialUnit (L : EndE) (t : ℝ) : Units EndE where
  val := flow L t
  inv := flow L (-t)
  val_inv := by
    calc
      flow L t * flow L (-t) = flow L (t + -t) :=
        (flow_add L t (-t)).symm
      _ = 1 := by simp
  inv_val := by
    calc
      flow L (-t) * flow L t = flow L (-t + t) :=
        (flow_add L (-t) t).symm
      _ = 1 := by simp

/-- The exponential representation as a native monoid homomorphism. -/
def exponentialHom (L : EndE) : Multiplicative ℝ →* Units EndE where
  toFun t := exponentialUnit L (toAdd t)
  map_one' := by
    apply Units.ext
    simp [exponentialUnit]
  map_mul' s t := by
    apply Units.ext
    change flow L (toAdd (s * t)) =
      flow L (toAdd s) * flow L (toAdd t)
    simpa using flow_add L (toAdd s) (toAdd t)

/-- The Banach-algebra exponential packaged in the canonical flow interface. -/
def exponentialOneParameterFlow (L : EndE) : RealOneParameterFlow EndE where
  flowHom := exponentialHom L

@[simp]
theorem exponentialOneParameterFlow_eval (L : EndE) (t : ℝ) :
    (exponentialOneParameterFlow L).eval t = flow L t := rfl

/-- Differentiating the group law transports the derivative at zero to every
point on the right. -/
theorem hasDerivAt_eval_mul_generator
    (F : RealOneParameterFlow EndE) (L : EndE)
    (hzero : HasDerivAt F.eval L 0) (t : ℝ) :
    HasDerivAt F.eval (F.eval t * L) t := by
  have hmul :
      HasDerivAt (fun u : ℝ => F.eval t * F.eval u)
        (F.eval t * L) 0 := by
    simpa using
      (hasDerivAt_const (x := (0 : ℝ)) (c := F.eval t)).mul hzero
  have htranslated :
      HasDerivAt (fun u : ℝ => F.eval (t + u))
        (F.eval t * L) 0 := by
    simpa only [RealOneParameterFlow.eval_add] using hmul
  have htranslatedAt :
      HasDerivAt (fun u : ℝ => F.eval (t + u))
        (F.eval t * L) (t - t) := by
    simpa using htranslated
  convert htranslatedAt.comp t ((hasDerivAt_id t).sub_const t) using 1 <;> simp

/-- The negative exponential flow is a left inverse of the positive flow. -/
theorem flow_neg_generator_mul (L : EndE) (t : ℝ) :
    flow (-L) t * flow L t = 1 := by
  have hneg : flow (-L) t = flow L (-t) := by
    simp [flow, smul_neg, neg_smul]
  calc
    flow (-L) t * flow L t = flow L (-t) * flow L t := by rw [hneg]
    _ = flow L (-t + t) := (flow_add L (-t) t).symm
    _ = 1 := by simp

/--
A differentiable real one-parameter representation of bounded operators is
exactly the exponential of its derivative at zero.
-/
theorem eval_eq_exponential_of_hasDerivAt_zero
    (F : RealOneParameterFlow EndE) (L : EndE)
    (hzero : HasDerivAt F.eval L 0) (t : ℝ) :
    F.eval t = flow L t := by
  have hinteraction :
      ∀ s : ℝ,
        HasFDerivAt (fun u : ℝ => F.eval u * flow (-L) u)
          (0 : ℝ →L[ℝ] EndE) s := by
    intro s
    have hprod :=
      (hasDerivAt_eval_mul_generator F L hzero s).mul
        (hasStrictDerivAt_flow_left (-L) s).hasDerivAt
    have hzeroDeriv :
        HasDerivAt (fun u : ℝ => F.eval u * flow (-L) u) 0 s := by
      simpa [mul_assoc] using hprod
    simpa using hzeroDeriv.hasFDerivAt
  have hconst := eq_zero_time_of_hasFDerivAt_zero hinteraction t
  have hleft : F.eval t * flow (-L) t = 1 := by
    simpa using hconst
  calc
    F.eval t = F.eval t * 1 := by simp
    _ = F.eval t * (flow (-L) t * flow L t) := by
      rw [flow_neg_generator_mul]
    _ = (F.eval t * flow (-L) t) * flow L t := by
      rw [← mul_assoc]
    _ = flow L t := by rw [hleft, one_mul]

/-- Function-level classification of the entire representation. -/
theorem eval_eq_exponential
    (F : RealOneParameterFlow EndE) (L : EndE)
    (hzero : HasDerivAt F.eval L 0) :
    F.eval = flow L := by
  funext t
  exact eval_eq_exponential_of_hasDerivAt_zero F L hzero t

/-- Complete synthesis for a translation-covariant factorization: its relative
operator is the exponential of its derivative at zero. -/
theorem relativeModifier_eq_exponential_of_hasDerivAt_zero
    (M : TranslationCovariantModifiers EndE) (L : EndE)
    (hzero : HasDerivAt M.relativeModifier L 0) (t : ℝ) :
    M.relativeModifier t = flow L t := by
  simpa using
    eval_eq_exponential_of_hasDerivAt_zero M.toRealOneParameterFlow L
      (by simpa using hzero) t

end ExponentialClassification

/-! ## 4. Exact RoPE and ALiBi realizations -/

section RoPE

open InfoGeometry.Clifford.RotorMonodromy

variable {n : ℕ}

/-- The existing continuous rotor as a repository-native rotary positional
layer. -/
def continuousRopeLayer (cs : RealComplexStructure n) :
    RotaryPositionalLayer ℝ (Fin n → ℝ) where
  rotateQ t q := rotor cs t *ᵥ q
  rotateK t k := rotor cs t *ᵥ k

/-- Continuous RoPE scores depend exactly on relative position. -/
theorem continuousRopeLayer_relative_attentionScore
    (cs : RealComplexStructure n) (s t : ℝ) (q k : Fin n → ℝ) :
    attentionScore ((continuousRopeLayer cs).rotateQ s q)
        ((continuousRopeLayer cs).rotateK t k) =
      attentionScore q ((continuousRopeLayer cs).rotateK (t - s) k) := by
  unfold continuousRopeLayer attentionScore
  rw [← Matrix.vecMul_transpose]
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.vecMul_vecMul]
  rw [← Matrix.dotProduct_mulVec]
  rw [rotor_transpose, ← rotor_add]
  have h : -s + t = t - s := by ring
  rw [h]

/-- The existing integer rotor as a repository-native rotary positional layer. -/
def discreteRopeLayer (cs : RealComplexStructure n) (theta0 : ℝ) :
    RotaryPositionalLayer ℤ (Fin n → ℝ) where
  rotateQ m q := discreteRotor cs theta0 m *ᵥ q
  rotateK m k := discreteRotor cs theta0 m *ᵥ k

/-- The pre-existing rotor-monodromy theorem transported directly to the LLM
interface. -/
theorem discreteRopeLayer_relative_attentionScore
    (cs : RealComplexStructure n) (theta0 : ℝ)
    (m k : ℤ) (q v : Fin n → ℝ) :
    attentionScore ((discreteRopeLayer cs theta0).rotateQ m q)
        ((discreteRopeLayer cs theta0).rotateK k v) =
      attentionScore q
        ((discreteRopeLayer cs theta0).rotateK (k - m) v) := by
  simpa [attentionScore, discreteRopeLayer, standardPairing] using
    rope_relative_pairing_invariance cs theta0 m k q v

end RoPE

section ALiBi

/-- The exact square-zero Jordan block already verified in the external-auto
proof layer, reused as the parabolic positional generator. -/
abbrev AlibiMat := JordanBlock2.M2C

/-- Canonical parabolic relative-position flow generated by the verified Jordan
nilpotent. -/
def alibiRelativeFlow : RealOneParameterFlow AlibiMat :=
  parabolicFlow_of_sq_eq_zero JordanBlock2.N2 JordanBlock2.N2_sq

@[simp]
theorem alibiRelativeFlow_eval (t : ℝ) :
    alibiRelativeFlow.eval t = parabolicMat JordanBlock2.N2 t := rfl

/-- Fixed extra query lane carrying the ALiBi slope. -/
def alibiPenaltyQuery (p : ℝ) : Fin 2 → ℂ :=
  ![-(p : ℂ), 0]

/-- Fixed extra key lane whose parabolic orbit exposes the relative time. -/
def alibiClockKey : Fin 2 → ℂ :=
  ![0, 1]

/-- The square-zero flow sends the clock key to `(t,1)`. -/
theorem alibiRelativeFlow_mulVec_clockKey (t : ℝ) :
    (alibiRelativeFlow.eval t) *ᵥ alibiClockKey = ![(t : ℂ), 1] := by
  rw [alibiRelativeFlow_eval]
  funext i
  fin_cases i <;>
    simp [parabolicMat, JordanBlock2.N2, alibiClockKey,
      Matrix.mulVec, Fin.sum_univ_two]

/-- Pairing the fixed slope lane with the parabolic clock gives exactly the
linear relative-position penalty `-p t`. -/
theorem alibi_parabolic_bias (p t : ℝ) :
    attentionScore (alibiPenaltyQuery p)
        ((alibiRelativeFlow.eval t) *ᵥ alibiClockKey) =
      -((p : ℂ) * (t : ℂ)) := by
  rw [alibiRelativeFlow_mulVec_clockKey]
  simp [attentionScore, alibiPenaltyQuery, dotProduct, Fin.sum_univ_two]
  ring

/-- Direct-sum score: the original content score plus the two-dimensional
parabolic positional lane. -/
def alibiAugmentedScore
    {ι : Type u} [Fintype ι]
    (q k : ι → ℂ) (p t : ℝ) : ℂ :=
  attentionScore q k +
    attentionScore (alibiPenaltyQuery p)
      ((alibiRelativeFlow.eval t) *ᵥ alibiClockKey)

/-- The augmented bilinear score is exactly the ALiBi score
`qᵀk - p t`. -/
theorem alibiAugmentedScore_eq
    {ι : Type u} [Fintype ι]
    (q k : ι → ℂ) (p t : ℝ) :
    alibiAugmentedScore q k p t =
      attentionScore q k - (p : ℂ) * (t : ℂ) := by
  rw [alibiAugmentedScore, alibi_parabolic_bias]
  ring

end ALiBi

end InfoGeometry.LLM.PositionalEncodingRepresentation

end noncomputable section
