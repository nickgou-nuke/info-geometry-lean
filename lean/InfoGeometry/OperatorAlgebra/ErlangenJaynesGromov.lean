import Mathlib.Tactic
import Mathlib.Algebra.DualNumber

/-!
# Erlangen--Jaynes--Gromov Operator Geometry

This file formalizes the algebraic core of the "Erlangen 2.0" viewpoint:

* an operator algebra is acted on by a symmetry semigroup;
* states are normalized linear functionals on the algebra;
* symmetries act dually on states by pullback;
* Gromov-style coarse graining is modeled by equivariant idempotent algebra maps;
* Jaynes' finite empirical state is a finite average of linear functionals;
* Radon--Nikodym data is represented algebraically by a density element whose
  left multiplication transports one state into another.

This is deliberately not an analytic theorem about large-number convergence,
noncommutative Radon--Nikodym derivatives, or von Neumann algebra standard
forms.  It is the categorical algebraic substrate those analytic theories can
later enrich.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.OperatorAlgebra.ErlangenJaynesGromov

universe uR uA uB uC uS uι

/-! ## 1. Operator Erlangen systems -/

/--
An operator Erlangen system is an algebra equipped with a semigroup/monoid action
by algebra endomorphisms.

The graph orientation is "symmetry acts on observables"; states are acted on
dually by pullback later in the file.
-/
structure OperatorErlangenSystem
    (R : Type uR) (A : Type uA) (S : Type uS)
    [CommSemiring R] [Semiring A] [Algebra R A] [Monoid S] where
  /-- Semigroup element acting on the observable algebra. -/
  act : S → A →ₐ[R] A
  /-- The identity semigroup element acts as the identity endomorphism. -/
  act_one : ∀ a : A, act 1 a = a
  /-- Semigroup multiplication composes observable actions. -/
  act_mul : ∀ s t : S, ∀ a : A, act (s * t) a = act s (act t a)

namespace OperatorErlangenSystem

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC} {S : Type uS}
variable [CommSemiring R]
variable [Semiring A] [Algebra R A]
variable [Semiring B] [Algebra R B]
variable [Semiring C] [Algebra R C]
variable [Monoid S]

variable (E : OperatorErlangenSystem R A S)

@[simp]
theorem act_one_apply (a : A) :
    E.act 1 a = a :=
  E.act_one a

@[simp]
theorem act_mul_apply (s t : S) (a : A) :
    E.act (s * t) a = E.act s (E.act t a) :=
  E.act_mul s t a

@[simp]
theorem act_zero (s : S) :
    E.act s (0 : A) = 0 := by
  simp

@[simp]
theorem act_one_alg (s : S) :
    E.act s (1 : A) = 1 := by
  simp

@[simp]
theorem act_add (s : S) (a b : A) :
    E.act s (a + b) = E.act s a + E.act s b := by
  simp

@[simp]
theorem act_mul_alg (s : S) (a b : A) :
    E.act s (a * b) = E.act s a * E.act s b := by
  simp

/-! ## 2. Geometry as invariants -/

/-- An observable fixed by every symmetry in the semigroup. -/
def IsObservableInvariant (a : A) : Prop :=
  ∀ s : S, E.act s a = a

/-- The invariant observables as a subset of the operator algebra. -/
def invariantObservableSet : Set A :=
  {a | E.IsObservableInvariant a}

theorem invariant_zero :
    E.IsObservableInvariant (0 : A) := by
  intro s
  simp

theorem invariant_one :
    E.IsObservableInvariant (1 : A) := by
  intro s
  simp

theorem invariant_add {a b : A}
    (ha : E.IsObservableInvariant a) (hb : E.IsObservableInvariant b) :
    E.IsObservableInvariant (a + b) := by
  intro s
  simp [ha s, hb s]

theorem invariant_mul {a b : A}
    (ha : E.IsObservableInvariant a) (hb : E.IsObservableInvariant b) :
    E.IsObservableInvariant (a * b) := by
  intro s
  simp [ha s, hb s]

/--
The fixed observables form a subalgebra.  This is the algebraic form of the
Erlangen slogan: geometry is the invariant algebra of a symmetry action.
-/
def invariantSubalgebra : Subalgebra R A where
  carrier := {a | E.IsObservableInvariant a}
  zero_mem' := E.invariant_zero
  one_mem' := E.invariant_one
  add_mem' := by
    intro a b ha hb
    exact E.invariant_add ha hb
  mul_mem' := by
    intro a b ha hb
    exact E.invariant_mul ha hb
  algebraMap_mem' := by
    intro r s
    exact (E.act s).commutes r

@[simp]
theorem mem_invariantSubalgebra_iff (a : A) :
    a ∈ E.invariantSubalgebra ↔ E.IsObservableInvariant a :=
  Iff.rfl

/-! ## 3. States as normalized linear functionals -/

/--
An algebraic state is a normalized linear functional.

No positivity or topological normality is asserted here.  Those are analytic
enrichments, not part of this algebraic core.
-/
structure AlgebraicState where
  /-- The underlying linear functional on the observable algebra. -/
  toLinearMap : A →ₗ[R] R
  /-- Normalization on the unit observable. -/
  map_one : toLinearMap 1 = 1

namespace AlgebraicState

instance : CoeFun (AlgebraicState (R := R) (A := A)) (fun _ => A → R) where
  coe ω := ω.toLinearMap

@[ext]
theorem ext
    {ω η : AlgebraicState (R := R) (A := A)}
    (h : ∀ a : A, ω a = η a) :
    ω = η := by
  cases ω with
  | mk ω hω =>
    cases η with
    | mk η hη =>
      simp only at h
      have hmap : ω = η := by
        ext a
        exact h a
      subst hmap
      rfl

@[simp]
theorem map_one_apply (ω : AlgebraicState (R := R) (A := A)) :
    ω (1 : A) = 1 :=
  ω.map_one

@[simp]
theorem map_add (ω : AlgebraicState (R := R) (A := A)) (a b : A) :
    ω (a + b) = ω a + ω b :=
  ω.toLinearMap.map_add a b

@[simp]
theorem map_smul (ω : AlgebraicState (R := R) (A := A)) (r : R) (a : A) :
    ω (r • a) = r • ω a :=
  ω.toLinearMap.map_smul r a

end AlgebraicState

/-- Pull a linear functional back along an algebra endomorphism. -/
def pullbackFunctional (α : A →ₐ[R] A) (ω : A →ₗ[R] R) : A →ₗ[R] R :=
  ω.comp α.toLinearMap

@[simp]
theorem pullbackFunctional_apply (α : A →ₐ[R] A) (ω : A →ₗ[R] R) (a : A) :
    pullbackFunctional α ω a = ω (α a) :=
  rfl

/-- The dual action of a semigroup element on normalized states. -/
def pullbackState (s : S) (ω : AlgebraicState (R := R) (A := A)) :
    AlgebraicState (R := R) (A := A) where
  toLinearMap := pullbackFunctional (E.act s) ω.toLinearMap
  map_one := by
    simp [pullbackFunctional, ω.map_one]

@[simp]
theorem pullbackState_apply
    (s : S) (ω : AlgebraicState (R := R) (A := A)) (a : A) :
    E.pullbackState s ω a = ω (E.act s a) :=
  rfl

@[simp]
theorem pullbackState_one (ω : AlgebraicState (R := R) (A := A)) :
    E.pullbackState 1 ω = ω := by
  ext a
  simp [pullbackState]

theorem pullbackState_mul (s t : S) (ω : AlgebraicState (R := R) (A := A)) :
    E.pullbackState (s * t) ω = E.pullbackState t (E.pullbackState s ω) := by
  ext a
  simp [pullbackState, E.act_mul_apply]

/-- A state fixed by the dual semigroup action. -/
def IsStateInvariant (ω : AlgebraicState (R := R) (A := A)) : Prop :=
  ∀ s : S, E.pullbackState s ω = ω

theorem stateInvariant_iff_eval
    (ω : AlgebraicState (R := R) (A := A)) :
    E.IsStateInvariant ω ↔ ∀ s : S, ∀ a : A, ω (E.act s a) = ω a := by
  constructor
  · intro h s a
    have happ := congrArg (fun η : AlgebraicState (R := R) (A := A) => η a) (h s)
    simpa using happ
  · intro h s
    ext a
    exact h s a

/-! ## 4. Equivariant algebra maps: the categorical morphisms -/

/-- Equivariant algebra homomorphisms between systems with the same symmetry semigroup. -/
structure EquivariantAlgHom
    (E₁ : OperatorErlangenSystem R A S)
    (E₂ : OperatorErlangenSystem R B S) where
  /-- The underlying algebra homomorphism. -/
  toAlgHom : A →ₐ[R] B
  /-- Compatibility with the symmetry action. -/
  equivariant : ∀ s : S, ∀ a : A, toAlgHom (E₁.act s a) = E₂.act s (toAlgHom a)

namespace EquivariantAlgHom

variable {E₁ : OperatorErlangenSystem R A S}
variable {E₂ : OperatorErlangenSystem R B S}
variable {E₃ : OperatorErlangenSystem R C S}

instance : CoeFun (EquivariantAlgHom E₁ E₂) (fun _ => A → B) where
  coe F := F.toAlgHom

/-- Identity equivariant algebra homomorphism. -/
def id (E : OperatorErlangenSystem R A S) : EquivariantAlgHom E E where
  toAlgHom := AlgHom.id R A
  equivariant := by
    intro s a
    rfl

/-- Composition of equivariant algebra homomorphisms. -/
def comp (G : EquivariantAlgHom E₂ E₃) (F : EquivariantAlgHom E₁ E₂) :
    EquivariantAlgHom E₁ E₃ where
  toAlgHom := G.toAlgHom.comp F.toAlgHom
  equivariant := by
    intro s a
    calc
      G.toAlgHom (F.toAlgHom (E₁.act s a))
          = G.toAlgHom (E₂.act s (F.toAlgHom a)) := by
              rw [F.equivariant]
      _ = E₃.act s (G.toAlgHom (F.toAlgHom a)) := by
              rw [G.equivariant]

/-- Equivariant maps send invariant observables to invariant observables. -/
theorem map_invariant
    (F : EquivariantAlgHom E₁ E₂)
    {a : A}
    (ha : E₁.IsObservableInvariant a) :
    E₂.IsObservableInvariant (F a) := by
  intro s
  rw [← F.equivariant s a, ha s]

end EquivariantAlgHom

/-! ## 5. Gromov-style semigroup projections -/

/--
A Gromov-style projection is an equivariant idempotent algebra endomorphism.

This models coarse graining or information-forgetting as a semigroup-compatible
projection of the observable algebra.
-/
structure SemigroupProjection where
  /-- The algebraic projection/coarse-graining map. -/
  project : A →ₐ[R] A
  /-- Idempotence: projecting twice is the same as projecting once. -/
  idempotent : ∀ a : A, project (project a) = project a
  /-- Equivariance with respect to the semigroup action. -/
  equivariant : ∀ s : S, ∀ a : A, project (E.act s a) = E.act s (project a)

namespace SemigroupProjection

variable {E : OperatorErlangenSystem R A S}
variable (P : E.SemigroupProjection)

/-- The projected observable is a fixed point of the projection. -/
theorem project_fixed (a : A) :
    P.project (P.project a) = P.project a :=
  P.idempotent a

/-- Projection induces a normalized state by pullback. -/
def projectState (ω : AlgebraicState (R := R) (A := A)) :
    AlgebraicState (R := R) (A := A) where
  toLinearMap := pullbackFunctional P.project ω.toLinearMap
  map_one := by
    simp [pullbackFunctional, ω.map_one]

@[simp]
theorem projectState_apply
    (ω : AlgebraicState (R := R) (A := A)) (a : A) :
    P.projectState ω a = ω (P.project a) :=
  rfl

/-- The induced projection on states is idempotent. -/
theorem projectState_idempotent (ω : AlgebraicState (R := R) (A := A)) :
    P.projectState (P.projectState ω) = P.projectState ω := by
  ext a
  simp [projectState, P.idempotent a]

/-- Equivariance of observable projection, restated as the Gromov projection law. -/
theorem project_commutes_with_symmetry (s : S) (a : A) :
    P.project (E.act s a) = E.act s (P.project a) :=
  P.equivariant s a

end SemigroupProjection

/-! ## 5b. State-side Gromov projections -/

/--
A state-side Gromov projection is an idempotent linear map on algebraic
functionals that preserves the normalized-state locus.

This is an algebraic control-plane object: it does not assert positivity,
compactness, concentration, or any analytic metric limit.
-/
structure GromovStateProjection where
  /-- Linear projection on the space of algebraic readout functionals. -/
  map : (A →ₗ[R] R) →ₗ[R] (A →ₗ[R] R)
  /-- Idempotence on functionals. -/
  idempotent : map.comp map = map
  /-- The projection sends normalized algebraic states to normalized states. -/
  preserves_states :
    ∀ ω : AlgebraicState (R := R) (A := A),
      ∃ ω' : AlgebraicState (R := R) (A := A), map ω.toLinearMap = ω'.toLinearMap

namespace GromovStateProjection

variable (P : GromovStateProjection (R := R) (A := A))

/-- Pointwise idempotence of the functional projection. -/
theorem map_idempotent_apply (ω : A →ₗ[R] R) :
    P.map (P.map ω) = P.map ω := by
  exact congrArg (fun F : (A →ₗ[R] R) →ₗ[R] (A →ₗ[R] R) => F ω) P.idempotent

/-- State preservation is exposed as the structure's existential theorem, without selecting a state. -/
theorem exists_projectState (ω : AlgebraicState (R := R) (A := A)) :
    ∃ ω' : AlgebraicState (R := R) (A := A), P.map ω.toLinearMap = ω'.toLinearMap :=
  P.preserves_states ω

/--
Any two-step preserved-state chain collapses at the underlying-functional level
by idempotence of the state-side projection.
-/
theorem projectState_idempotent_toLinearMap_of_preserved
    (ω ω' ω'' : AlgebraicState (R := R) (A := A))
    (hω' : P.map ω.toLinearMap = ω'.toLinearMap)
    (hω'' : P.map ω'.toLinearMap = ω''.toLinearMap) :
    ω''.toLinearMap = ω'.toLinearMap := by
  rw [← hω'', ← hω']
  exact P.map_idempotent_apply ω.toLinearMap

end GromovStateProjection

/-! ## 6. Jaynes finite empirical states -/

section Jaynes

variable {ι : Type uι} [Fintype ι]

/--
Finite empirical weighted average of a family of linear functionals.

This is the algebraic "large number of points" object: a finite weighted sum
indexed by data points.  The usual average is recovered by choosing a weight
whose product with the cardinality is `1`.  No limiting theorem is asserted
here.
-/
def empiricalWeightedFunctional (weight : R) (sample : ι → A →ₗ[R] R) : A →ₗ[R] R :=
  weight • ∑ i, sample i

@[simp]
theorem empiricalWeightedFunctional_apply
    (weight : R) (sample : ι → A →ₗ[R] R) (a : A) :
    empiricalWeightedFunctional (R := R) (A := A) weight sample a =
      weight * ∑ i, sample i a := by
  simp [empiricalWeightedFunctional, Finset.mul_sum]

/--
If every sampled functional is normalized and the chosen weight normalizes the
finite cardinality, the empirical weighted functional is normalized.
-/
theorem empiricalWeightedFunctional_map_one
    (weight : R)
    (sample : ι → A →ₗ[R] R)
    (hSample : ∀ i, sample i (1 : A) = 1)
    (hweight : weight * (Fintype.card ι : R) = 1) :
    empiricalWeightedFunctional (R := R) (A := A) weight sample (1 : A) = 1 := by
  calc
    empiricalWeightedFunctional (R := R) (A := A) weight sample (1 : A)
        = weight * ∑ i, sample i (1 : A) := by
            simp [empiricalWeightedFunctional]
    _ = weight * ∑ _i : ι, (1 : R) := by
            simp [hSample]
    _ = weight * (Fintype.card ι : R) := by
            simp
    _ = 1 := hweight

/-- Empirical weighted average of normalized algebraic states. -/
def empiricalWeightedState
    (weight : R)
    (sample : ι → AlgebraicState (R := R) (A := A))
    (hweight : weight * (Fintype.card ι : R) = 1) :
    AlgebraicState (R := R) (A := A) where
  toLinearMap :=
    empiricalWeightedFunctional (R := R) (A := A) weight (fun i => (sample i).toLinearMap)
  map_one := by
    exact empiricalWeightedFunctional_map_one
      (R := R) (A := A) weight
      (fun i => (sample i).toLinearMap)
      (fun i => (sample i).map_one)
      hweight

@[simp]
theorem empiricalWeightedState_apply
    (weight : R)
    (sample : ι → AlgebraicState (R := R) (A := A))
    (hweight : weight * (Fintype.card ι : R) = 1)
    (a : A) :
    empiricalWeightedState (R := R) (A := A) weight sample hweight a =
      weight * ∑ i, sample i a := by
  simp [empiricalWeightedState, empiricalWeightedFunctional]

end Jaynes

/-! ## 6b. Jaynes finite empirical states from character lists -/

section JaynesLists

variable {K : Type uR} {B : Type uA}
variable [Field K] [Ring B] [Algebra K B]

/-- A point evaluation/character is an algebra homomorphism into the coefficient field. -/
abbrev Character :=
  B →ₐ[K] K

@[simp]
theorem list_sum_apply
    {M : Type*} [AddCommMonoid M] [Module K M]
    (l : List (B →ₗ[K] M)) (x : B) :
    l.sum x = (l.map (fun f => f x)).sum := by
  induction l with
  | nil =>
      rfl
  | cons f tail ih =>
      simp [ih]

@[simp]
theorem list_sum_map_one
    (chars : List (Character (K := K) (B := B))) :
    ((chars.map (fun (χ : Character (K := K) (B := B)) => χ.toLinearMap)).sum) 1 =
      (chars.length : K) := by
  induction chars with
  | nil =>
      simp
  | cons χ tail ih =>
      simp [ih, Nat.cast_succ]
      abel

/--
The empirical state associated to a finite nonzero-character-count list.

The premise `(chars.length : R) ≠ 0` is intentionally explicit: over fields of
finite characteristic, a nonempty list can have length whose scalar cast
vanishes.
-/
noncomputable def empiricalState
    (chars : List (Character (K := K) (B := B)))
    (hchars : (chars.length : K) ≠ 0) :
    AlgebraicState (R := K) (A := B) where
  toLinearMap :=
    (1 / (chars.length : K)) •
      (chars.map (fun (χ : Character (K := K) (B := B)) => χ.toLinearMap)).sum
  map_one := by
    rw [LinearMap.smul_apply, list_sum_map_one]
    change (1 / (chars.length : K)) * (chars.length : K) = 1
    field_simp [hchars]

/--
Recursive character-linear-map sum.

This is definitionally simple and avoids relying on binder-heavy `List.map`
expressions at construction sites; the theorem below connects it back to the
standard `List.sum` expression.
-/
noncomputable def sumCharacterLinearMaps
    (chars : List (Character (K := K) (B := B))) : B →ₗ[K] K :=
  match chars with
  | [] => 0
  | χ :: χs => χ.toLinearMap + sumCharacterLinearMaps χs

@[simp]
theorem sumCharacterLinearMaps_eq_list_sum
    (chars : List (Character (K := K) (B := B))) :
    sumCharacterLinearMaps (K := K) (B := B) chars =
      (chars.map (fun χ => χ.toLinearMap)).sum := by
  induction chars with
  | nil =>
      rfl
  | cons χ tail ih =>
      simp [sumCharacterLinearMaps, ih]

@[simp]
theorem sumCharacterLinearMaps_one
    (chars : List (Character (K := K) (B := B))) :
    sumCharacterLinearMaps (K := K) (B := B) chars 1 = (chars.length : K) := by
  rw [sumCharacterLinearMaps_eq_list_sum]
  exact list_sum_map_one chars

/--
Recursive version of `empiricalState`.

It is extensionally the same normalized finite character average as
`empiricalState`, but its underlying linear map is built from
`sumCharacterLinearMaps`.
-/
noncomputable def empiricalStateRecursive
    (chars : List (Character (K := K) (B := B)))
    (hchars : (chars.length : K) ≠ 0) :
    AlgebraicState (R := K) (A := B) where
  toLinearMap := (1 / (chars.length : K)) • sumCharacterLinearMaps chars
  map_one := by
    rw [LinearMap.smul_apply, sumCharacterLinearMaps_one]
    change (1 / (chars.length : K)) * (chars.length : K) = 1
    field_simp [hchars]

@[simp]
theorem empiricalStateRecursive_toLinearMap
    (chars : List (Character (K := K) (B := B)))
    (hchars : (chars.length : K) ≠ 0) :
    (empiricalStateRecursive (K := K) (B := B) chars hchars).toLinearMap =
      (empiricalState (K := K) (B := B) chars hchars).toLinearMap := by
  simp [empiricalStateRecursive, empiricalState]

end JaynesLists

/-! ## 7. Algebraic Radon--Nikodym density witnesses -/

/--
An algebraic Radon--Nikodym density property from `ω` to `φ`.

The density element `h` represents `φ` relative to `ω` by
`φ(a) = ω(h * a)`.  This is an algebraic representation law, not the analytic
Radon--Nikodym theorem.
-/
structure AlgebraicRNDensity
    (ω φ : AlgebraicState (R := R) (A := A)) where
  /-- The density element. -/
  density : A
  /-- Representation law for the target state relative to the reference state. -/
  rn_law : ∀ a : A, φ a = ω (density * a)

namespace AlgebraicRNDensity

variable {ω φ : AlgebraicState (R := R) (A := A)}

/-- Readout of the RN representation law. -/
theorem apply (D : AlgebraicRNDensity (R := R) (A := A) ω φ) (a : A) :
    φ a = ω (D.density * a) :=
  D.rn_law a

/-- Normalization of the target state reads the density against the reference state. -/
theorem density_normalized (D : AlgebraicRNDensity (R := R) (A := A) ω φ) :
    ω D.density = 1 := by
  have h := D.rn_law (1 : A)
  have hφ := φ.map_one
  rw [h] at hφ
  simpa using hφ

end AlgebraicRNDensity

/-- Algebraic absolute continuity is carried by an explicit RN-density property. -/
abbrev AlgebraicAbsolutelyContinuous
    (ω φ : AlgebraicState (R := R) (A := A)) :=
  AlgebraicRNDensity (R := R) (A := A) ω φ

/--
Algebraic Radon--Nikodym chain rule.

If `φ(a) = ω(h₂ * a)` and `ψ(a) = φ(h₁ * a)`, then
`ψ(a) = ω((h₂ * h₁) * a)`.
-/
def AlgebraicRNDensity.comp
    {ω φ ψ : AlgebraicState (R := R) (A := A)}
    (Dωφ : AlgebraicRNDensity (R := R) (A := A) ω φ)
    (Dφψ : AlgebraicRNDensity (R := R) (A := A) φ ψ) :
    AlgebraicRNDensity (R := R) (A := A) ω ψ where
  density := Dωφ.density * Dφψ.density
  rn_law := by
    intro a
    rw [Dφψ.rn_law a, Dωφ.rn_law (Dφψ.density * a)]
    rw [mul_assoc]

@[simp]
theorem AlgebraicRNDensity.comp_density
    {ω φ ψ : AlgebraicState (R := R) (A := A)}
    (Dωφ : AlgebraicRNDensity (R := R) (A := A) ω φ)
    (Dφψ : AlgebraicRNDensity (R := R) (A := A) φ ψ) :
    (Dωφ.comp Dφψ).density = Dωφ.density * Dφψ.density :=
  rfl

/-- Readout form of the algebraic Radon--Nikodym chain rule. -/
theorem AlgebraicRNDensity.comp_apply
    {ω φ ψ : AlgebraicState (R := R) (A := A)}
    (Dωφ : AlgebraicRNDensity (R := R) (A := A) ω φ)
    (Dφψ : AlgebraicRNDensity (R := R) (A := A) φ ψ)
    (a : A) :
    ψ a = ω ((Dωφ.density * Dφψ.density) * a) :=
  (Dωφ.comp Dφψ).rn_law a

/-- Absolute continuity is transitive by composing algebraic RN densities. -/
def AlgebraicAbsolutelyContinuous.trans
    {ω φ ψ : AlgebraicState (R := R) (A := A)}
    (hωφ : AlgebraicAbsolutelyContinuous (R := R) (A := A) ω φ)
    (hφψ : AlgebraicAbsolutelyContinuous (R := R) (A := A) φ ψ) :
    AlgebraicAbsolutelyContinuous (R := R) (A := A) ω ψ := by
  exact hωφ.comp hφψ

/-! ## 7b. Empirical states with algebraic Radon--Nikodym witnesses -/

section EmpiricalRN

variable {K : Type uR} {B : Type uA}
variable [Field K] [Ring B] [Algebra K B]

/--
An empirical Jaynes state equipped with an explicit algebraic RN-density property
relative to a reference state.

This is a finite, algebraic bridge from empirical averaging to density-state
semantics: no positivity, topology, or analytic RN theorem is assumed.
-/
structure EmpiricalRNDensityPacket where
  /-- Reference state against which the empirical state is represented. -/
  referenceState : AlgebraicState (R := K) (A := B)
  /-- Finite list of characters used to form the empirical target state. -/
  chars : List (Character (K := K) (B := B))
  /-- The scalar list length is invertible/nonzero in the coefficient field. -/
  hchars : (chars.length : K) ≠ 0
  /-- Explicit density witnessing the empirical state relative to the reference state. -/
  rnDensity : AlgebraicRNDensity
    (R := K) (A := B)
    referenceState
    (empiricalState (K := K) (B := B) chars hchars)

namespace EmpiricalRNDensityPacket

variable (P : EmpiricalRNDensityPacket (K := K) (B := B))

/-- The list-sum empirical state is represented by the supplied RN density. -/
theorem empirical_eq_reference_density_readout (a : B) :
    empiricalState (K := K) (B := B) P.chars P.hchars a =
      P.referenceState (P.rnDensity.density * a) :=
  P.rnDensity.rn_law a

/-- The recursive empirical state has the same RN density readout. -/
theorem empirical_recursive_eq_reference_density_readout (a : B) :
    empiricalStateRecursive (K := K) (B := B) P.chars P.hchars a =
      P.referenceState (P.rnDensity.density * a) := by
  rw [empiricalStateRecursive_toLinearMap]
  exact P.rnDensity.rn_law a

/-- The empirical RN density is normalized against the reference state. -/
theorem empirical_density_normalized :
    P.referenceState P.rnDensity.density = 1 :=
  P.rnDensity.density_normalized

end EmpiricalRNDensityPacket

end EmpiricalRN

/-! ## 8. The bundled Erlangen--Jaynes--Gromov packet -/

/--
The algebraic Erlangen--Jaynes--Gromov packet.

It bundles the operator-algebra symmetry system with a Gromov projection and
state-level data.  The optional RN property records when a target state is
represented as a density over a reference state.  This packet is algebraic
owner-side data only: it does not assert positivity, completion, modular-flow
generation, or any general noncommutative Radon--Nikodym theorem.
-/
structure ErlangenJaynesGromovPacket where
  /-- The underlying operator Erlangen system. -/
  system : OperatorErlangenSystem R A S
  /-- Reference state/weight. -/
  referenceState : AlgebraicState (R := R) (A := A)
  /-- Target state/weight. -/
  targetState : AlgebraicState (R := R) (A := A)
  /-- Semigroup-compatible projection/coarse graining. -/
  projection : system.SemigroupProjection
  /-- Algebraic RN-density datum, if supplied. -/
  rnDensity : AlgebraicRNDensity (R := R) (A := A) referenceState targetState

namespace ErlangenJaynesGromovPacket

variable (P : ErlangenJaynesGromovPacket (R := R) (A := A) (S := S))

/-- The Gromov projection is idempotent on observables. -/
theorem gromov_projection_idempotent (a : A) :
    P.projection.project (P.projection.project a) = P.projection.project a :=
  P.projection.idempotent a

/-- The Gromov projection commutes with semigroup symmetries. -/
theorem gromov_projection_equivariant (s : S) (a : A) :
    P.projection.project (P.system.act s a) =
      P.system.act s (P.projection.project a) :=
  P.projection.equivariant s a

/-- The target state is represented by the RN density over the reference state. -/
theorem target_eq_reference_density_readout (a : A) :
    P.targetState a = P.referenceState (P.rnDensity.density * a) :=
  P.rnDensity.rn_law a

/-- The supplied RN density is normalized against the reference state. -/
theorem rn_density_normalized :
    P.referenceState P.rnDensity.density = 1 :=
  P.rnDensity.density_normalized

end ErlangenJaynesGromovPacket

/-! ## 9. Universal parabolic sector -/

/--
Multiplying two square-zero parabolic translations only adds their parameters.

This is the algebraic core behind the parabolic sector: once `ε * ε = 0`, no
quadratic correction survives.
-/
theorem one_add_smul_square_zero_mul
    (ε : A) (hε : ε * ε = 0) (r s : R) :
    (1 + r • ε) * (1 + s • ε) = 1 + (r + s) • ε := by
  rw [mul_add, add_mul, add_mul, one_mul, mul_one]
  rw [smul_mul_smul, hε, smul_zero]
  simp [add_smul, add_assoc]

/--
The universal nilpotent/parabolic power law.

Any `R`-algebra containing a square-zero element `ε` carries the same finite
arithmetic progression:

`(1 + tε)^n = 1 + ntε`.

This is the dimension-free algebraic statement used by the direct-limit
Clifford/CAR bridge: the proof uses only the relation `ε² = 0` and semiring
algebra.
-/
theorem nilpotent_power_law
    (ε : A) (hε : ε * ε = 0) (t : R) (n : ℕ) :
    (1 + t • ε) ^ n = 1 + ((n : R) * t) • ε := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, ih, one_add_smul_square_zero_mul ε hε]
      congr 1
      rw [Nat.cast_succ]
      module

/--
Exact rescaled parabolic update.

If a discrete step `s` has total scalar time `(n : R) * s = t`, then `n`
successive nilpotent updates are already the continuum-looking update
`1 + tε`.  No analytic limiting argument is needed.
-/
theorem nilpotent_rescaled_power
    (ε : A) (hε : ε * ε = 0) (s t : R) (n : ℕ)
    (hscale : (n : R) * s = t) :
    (1 + s • ε) ^ n = 1 + t • ε := by
  rw [nilpotent_power_law ε hε s n, hscale]

/-- Compatibility alias for Mathlib's dual numbers. -/
abbrev DualNumbers (R : Type uR) :=
  DualNumber R

/-- The canonical square-zero generator in the dual numbers. -/
def dualEpsilon (R : Type uR) [Zero R] [One R] : DualNumbers R :=
  DualNumber.eps

@[simp]
theorem dualEpsilon_sq_zero
    (R : Type uR) [Semiring R] :
    dualEpsilon R * dualEpsilon R = 0 := by
  simp [dualEpsilon]

/--
The parabolic power law in the universal square-zero thickening `R[ε]`.

This is the dual-number model of the same finite arithmetic progression proved
abstractly in `nilpotent_power_law`.
-/
theorem dual_power
    (t : R) (n : ℕ) :
    (1 + t • dualEpsilon R) ^ n =
      1 + ((n : R) * t) • dualEpsilon R := by
  exact nilpotent_power_law
    (R := R) (A := DualNumbers R)
    (dualEpsilon R) (dualEpsilon_sq_zero R) t n

/-- Exact rescaled parabolic update in the universal dual-number model. -/
theorem dual_rescaled_power
    (s t : R) (n : ℕ)
    (hscale : (n : R) * s = t) :
    (1 + s • dualEpsilon R) ^ n = 1 + t • dualEpsilon R := by
  exact nilpotent_rescaled_power
    (R := R) (A := DualNumbers R)
    (dualEpsilon R) (dualEpsilon_sq_zero R) s t n hscale

end OperatorErlangenSystem

end InfoGeometry.OperatorAlgebra.ErlangenJaynesGromov
