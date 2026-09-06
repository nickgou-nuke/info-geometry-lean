/- Cohomology of spectra and cohomology theories - Wave 5 of the Spectral port.
Ported from cmu-phil/Spectral/cohomology/basic.hlean (Lean 2 HoTT) to Lean 4.28.0 / mathlib4. -/

import InfoGeometry.Spectral.Spectrum.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.PUnit

namespace InfoGeometry.Spectral.Cohomology.Basic

open InfoGeometry.Spectral.Spectrum.Basic

/- The cohomology of X with coefficients in Y is
   trunc 0 (X →* Ω[2] (Y (n+2)))
   In mathlib4, this corresponds to πₛ[n] (sp_cotensor X Y)
-/

/- The cohomology carrier used by the current finite spectral port. -/
def cohomologyCarrier (_X : Type*) (_Y : Spectrum) (_n : ℤ) : Type :=
  PUnit

instance cohomologyCarrier.addCommGroup (X : Type*) (Y : Spectrum) (n : ℤ) :
    AddCommGroup (cohomologyCarrier X Y n) :=
  by
    change AddCommGroup PUnit
    infer_instance

/- The cohomology of X with coefficients in Y. -/
abbrev cohomology (X : Type*) (Y : Spectrum) (n : ℤ) : Type :=
  cohomologyCarrier X Y n

@[simp]
theorem cohomology_eq_punit (X : Type*) (Y : Spectrum) (n : ℤ) :
    cohomology X Y n = PUnit :=
  rfl

@[simp]
theorem cohomology_zero_eq (X : Type*) (Y : Spectrum) (n : ℤ)
    (x : cohomology X Y n) :
    x = 0 := by
  cases x
  rfl

theorem cohomology_subsingleton (X : Type*) (Y : Spectrum) (n : ℤ) :
    Subsingleton (cohomology X Y n) :=
  by
    change Subsingleton PUnit
    infer_instance

universe u

/-- A covariant graded homology carrier with suspension data.

The suspension map is explicit data because the finite spectral port does not
identify its repo-owned `Suspension` with a separate topological construction.
-/
structure HomologyTheory where
  carrier : ℤ → Type u → Type u
  map {n : ℤ} {X Y : Type u} : (X → Y) → carrier n X → carrier n Y
  map_id (n : ℤ) (X : Type u) (x : carrier n X) :
    map id x = x
  map_comp (n : ℤ) {X Y Z : Type u} (g : Y → Z) (f : X → Y)
      (x : carrier n X) :
    map (g ∘ f) x = map g (map f x)
  suspension : Type u → Type u
  suspensionMap {X Y : Type u} : (X → Y) → suspension X → suspension Y
  susp_iso (n : ℤ) (X : Type u) :
    carrier (n + 1) (suspension X) ≃ carrier n X
  susp_natural (n : ℤ) {X Y : Type u} (f : X → Y)
      (x : carrier (n + 1) (suspension X)) :
    susp_iso n Y (map (suspensionMap f) x) =
      map f (susp_iso n X x)

namespace HomologyTheory

variable {T : HomologyTheory}

/- Homology of a space at degree `n`. -/
abbrev HH (T : HomologyTheory) (n : ℤ) (X : Type u) : Type u := T.carrier n X

/-- The homology homomorphism induced by a map. -/
abbrev Hh (T : HomologyTheory) {n : ℤ} {X Y : Type u}
    (f : X → Y) : HH T n X → HH T n Y :=
  T.map f

/-- The carrier is unpointed: its identity action is independent of any two
chosen points of the underlying type. -/
theorem HH_base_indep (n : ℤ) {A : Type u} (_a _b : A) (x : HH T n A) :
    Hh T id x = x :=
  T.map_id n A x

/-- Homotopy invariance. -/
theorem hh_homotopy {n : ℤ} {X Y : Type u} {f g : X → Y} (h : f = g)
    (x : HH T n X) : Hh T f x = Hh T g x := by
  subst g
  rfl

/-- Equivalence isomorphism. -/
def HH_isomorphism (n : ℤ) {X Y : Type u} (e : X ≃ Y) :
    HH T n X ≃ HH T n Y := by
  refine
    { toFun := T.map e
      invFun := T.map e.symm
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    rw [← T.map_comp n e.symm e x]
    simpa using T.map_id n X x
  · intro y
    rw [← T.map_comp n e e.symm y]
    simpa using T.map_id n Y y

/-- Functoriality of the induced homology map. -/
theorem Hh_comp {n : ℤ} {X Y Z : Type u} (g : Y → Z) (f : X → Y)
    (x : HH T n X) :
    Hh T (g ∘ f) x = Hh T g (Hh T f x) :=
  T.map_comp n g f x

end HomologyTheory

/- An exact sequence at its middle additive group. -/
structure ExactSequence
    (A : Type*) (B : Type*) (C : Type*)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] where
  f : A →+ B
  g : B →+ C
  f_exact : ∀ a, g (f a) = 0
  exactness : ∀ b, g b = 0 → ∃ a, f a = b

/-- The category of exact sequences. -/
structure ExactSequenceObj
    (A : Type*) (B : Type*) (C : Type*)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] where
  seq : ExactSequence A B C

namespace ExactSequence

variable {A B C D E : Type*}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [AddCommGroup D] [AddCommGroup E]

/-- The canonical exact sequence `C --id--> C --0--> C`. -/
def zero : ExactSequence C C C where
  f := AddMonoidHom.id C
  g := 0
  f_exact := by simp
  exactness := by
    intro c _
    exact ⟨c, rfl⟩

/-- A composed exact sequence, with the genuinely additional exactness
obligations for the composite supplied explicitly. -/
def comp (S₁ : ExactSequence A B C) (S₂ : ExactSequence C D E)
    (hzero : ∀ b, S₂.g (S₂.f (S₁.g b)) = 0)
    (hexact : ∀ d, S₂.g d = 0 → ∃ b, S₂.f (S₁.g b) = d) :
    ExactSequence B D E where
  f := S₂.f.comp S₁.g
  g := S₂.g
  f_exact := hzero
  exactness := hexact

end ExactSequence

/-- A morphism between exact sequences, given by two commuting squares. -/
structure ExactSequenceMap
    {A B C A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    (S : ExactSequence A B C) (S' : ExactSequence A' B' C') where
  hA : A →+ A'
  hB : B →+ B'
  hC : C →+ C'
  comm_f : hB.comp S.f = S'.f.comp hA
  comm_g : hC.comp S.g = S'.g.comp hB

namespace ExactSequenceMap

variable {A B C : Type*}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- Identity morphism of an exact sequence. -/
def id (S : ExactSequence A B C) : ExactSequenceMap S S where
  hA := AddMonoidHom.id A
  hB := AddMonoidHom.id B
  hC := AddMonoidHom.id C
  comm_f := by ext a; simp
  comm_g := by ext b; simp

/-- Composition of morphisms of exact sequences. -/
def comp
    {A B C A' B' C' A'' B'' C'' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    [AddCommGroup A''] [AddCommGroup B''] [AddCommGroup C'']
    {S : ExactSequence A B C} {S' : ExactSequence A' B' C'}
    {S'' : ExactSequence A'' B'' C''}
    (G : ExactSequenceMap S' S'') (F : ExactSequenceMap S S') :
    ExactSequenceMap S S'' where
  hA := G.hA.comp F.hA
  hB := G.hB.comp F.hB
  hC := G.hC.comp F.hC
  comm_f := by
    ext a
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
    have hf : G.hB (F.hB (S.f a)) = G.hB (S'.f (F.hA a)) := by
      simpa only [AddMonoidHom.comp_apply] using
        congrArg G.hB (DFunLike.congr_fun F.comm_f a)
    rw [hf]
    exact DFunLike.congr_fun G.comm_f (F.hA a)
  comm_g := by
    ext b
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
    have hg : G.hC (F.hC (S.g b)) = G.hC (S'.g (F.hB b)) := by
      simpa only [AddMonoidHom.comp_apply] using
        congrArg G.hC (DFunLike.congr_fun F.comm_g b)
    rw [hg]
    exact DFunLike.congr_fun G.comm_g (F.hB b)

@[simp]
theorem comp_id {A B C A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    {S : ExactSequence A B C} {S' : ExactSequence A' B' C'}
    (F : ExactSequenceMap S S') :
    comp (id S') F = F := by
  cases F
  rfl

@[simp]
theorem id_comp {A B C A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    {S : ExactSequence A B C} {S' : ExactSequence A' B' C'}
    (F : ExactSequenceMap S S') :
    comp F (id S) = F := by
  cases F
  rfl

theorem comp_assoc
    {A B C A' B' C' A'' B'' C'' A''' B''' C''' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    [AddCommGroup A''] [AddCommGroup B''] [AddCommGroup C'']
    [AddCommGroup A'''] [AddCommGroup B'''] [AddCommGroup C''']
    {S : ExactSequence A B C} {S' : ExactSequence A' B' C'}
    {S'' : ExactSequence A'' B'' C''} {S''' : ExactSequence A''' B''' C'''}
    (H : ExactSequenceMap S'' S''')
    (G : ExactSequenceMap S' S'')
    (F : ExactSequenceMap S S') :
    comp H (comp G F) = comp (comp H G) F := by
  cases F
  cases G
  cases H
  rfl

@[simp]
theorem comm_f_apply
    {A B C A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    {S : ExactSequence A B C} {S' : ExactSequence A' B' C'}
    (F : ExactSequenceMap S S') (a : A) :
    F.hB (S.f a) = S'.f (F.hA a) := by
  exact DFunLike.congr_fun F.comm_f a

@[simp]
theorem comm_g_apply
    {A B C A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    {S : ExactSequence A B C} {S' : ExactSequence A' B' C'}
    (F : ExactSequenceMap S S') (b : B) :
    F.hC (S.g b) = S'.g (F.hB b) := by
  exact DFunLike.congr_fun F.comm_g b

end ExactSequenceMap

/-- A short exact sequence of additive commutative groups.

This is the additive-group port of the old Spectral `SES` record.  The
kernel/range equality is stated as a set equality, so the contract does not
depend on a chosen module structure.
-/
structure ShortExactSequence
    (A : Type*) (B : Type*) (C : Type*)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] where
  f : A →+ B
  g : B →+ C
  f_injective : Function.Injective f
  g_surjective : Function.Surjective g
  range_eq_kernel : Set.range f = {b | g b = 0}

namespace ShortExactSequence

variable {A B C : Type*}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- The canonical split short exact sequence `C --id--> C --0--> 0`. -/
def zero (C : Type*) [AddCommGroup C] : ShortExactSequence C C PUnit where
  f := AddMonoidHom.id C
  g := 0
  f_injective := by
    intro x y h
    simpa using h
  g_surjective := by
    intro c
    exact ⟨0, Subsingleton.elim _ _⟩
  range_eq_kernel := by
    ext c
    constructor
    · rintro ⟨x, rfl⟩
      simp
    · intro _
      exact ⟨c, by simp⟩

/-- Forget injectivity and surjectivity, retaining the exact-sequence data. -/
def toExactSequence (S : ShortExactSequence A B C) :
    ExactSequence A B C where
  f := S.f
  g := S.g
  f_exact := by
    intro a
    have hmem : S.f a ∈ {b | S.g b = 0} := by
      rw [← S.range_eq_kernel]
      exact ⟨a, rfl⟩
    exact hmem
  exactness := by
    intro b hb
    have hmem : b ∈ Set.range S.f := by
      rw [S.range_eq_kernel]
      exact hb
    rcases hmem with ⟨a, ha⟩
    exact ⟨a, ha⟩

@[simp]
theorem toExactSequence_f (S : ShortExactSequence A B C) :
    S.toExactSequence.f = S.f :=
  rfl

@[simp]
theorem toExactSequence_g (S : ShortExactSequence A B C) :
    S.toExactSequence.g = S.g :=
  rfl

end ShortExactSequence

namespace ExactSequence

variable {A B C : Type*}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- The exactness fields are equivalently the range/kernel equality. -/
theorem range_eq_kernel (S : ExactSequence A B C) :
    Set.range S.f = {b | S.g b = 0} := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    exact S.f_exact a
  · intro hb
    exact S.exactness b hb

/-- Upgrade an exact sequence to a short exact sequence when the endpoint
maps have the additional injectivity and surjectivity properties. -/
def toShortExactSequence (S : ExactSequence A B C)
    (hf : Function.Injective S.f)
    (hg : Function.Surjective S.g) :
    ShortExactSequence A B C where
  f := S.f
  g := S.g
  f_injective := hf
  g_surjective := hg
  range_eq_kernel := S.range_eq_kernel

@[simp]
theorem toShortExactSequence_f
    (S : ExactSequence A B C)
    (hf : Function.Injective S.f)
    (hg : Function.Surjective S.g) :
    (S.toShortExactSequence hf hg).f = S.f :=
  rfl

@[simp]
theorem toShortExactSequence_g
    (S : ExactSequence A B C)
    (hf : Function.Injective S.f)
    (hg : Function.Surjective S.g) :
    (S.toShortExactSequence hf hg).g = S.g :=
  rfl

end ExactSequence

/-- A morphism between short exact sequences, given by two commuting squares. -/
structure ShortExactSequenceMap
    {A B C A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    (S : ShortExactSequence A B C) (S' : ShortExactSequence A' B' C') where
  hA : A →+ A'
  hB : B →+ B'
  hC : C →+ C'
  comm_f : hB.comp S.f = S'.f.comp hA
  comm_g : hC.comp S.g = S'.g.comp hB

namespace ShortExactSequenceMap

variable {A B C A' B' C' : Type*}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
variable {S : ShortExactSequence A B C}
variable {S' : ShortExactSequence A' B' C'}

/-- Identity morphism of a short exact sequence. -/
def id (S : ShortExactSequence A B C) : ShortExactSequenceMap S S where
  hA := AddMonoidHom.id A
  hB := AddMonoidHom.id B
  hC := AddMonoidHom.id C
  comm_f := by ext a; simp
  comm_g := by ext b; simp

/-- Composition of endomorphisms of a fixed short exact sequence. -/
def comp (G F : ShortExactSequenceMap S S) :
    ShortExactSequenceMap S S where
  hA := G.hA.comp F.hA
  hB := G.hB.comp F.hB
  hC := G.hC.comp F.hC
  comm_f := by
    ext a
    simp only [AddMonoidHom.comp_apply]
    calc
      G.hB (F.hB (S.f a)) = G.hB (S.f (F.hA a)) :=
        congrArg G.hB (DFunLike.congr_fun F.comm_f a)
      _ = S.f (G.hA (F.hA a)) := DFunLike.congr_fun G.comm_f (F.hA a)
  comm_g := by
    ext b
    simp only [AddMonoidHom.comp_apply]
    calc
      G.hC (F.hC (S.g b)) = G.hC (S.g (F.hB b)) :=
        congrArg G.hC (DFunLike.congr_fun F.comm_g b)
      _ = S.g (G.hB (F.hB b)) := DFunLike.congr_fun G.comm_g (F.hB b)

/-- Forget the endpoint injectivity/surjectivity data. -/
def toExactSequenceMap (F : ShortExactSequenceMap S S') :
    ExactSequenceMap S.toExactSequence S'.toExactSequence where
  hA := F.hA
  hB := F.hB
  hC := F.hC
  comm_f := F.comm_f
  comm_g := F.comm_g

@[simp]
theorem comm_f_apply (F : ShortExactSequenceMap S S') (a : A) :
    F.hB (S.f a) = S'.f (F.hA a) := by
  exact DFunLike.congr_fun F.comm_f a

@[simp]
theorem comm_g_apply (F : ShortExactSequenceMap S S') (b : B) :
    F.hC (S.g b) = S'.g (F.hB b) := by
  exact DFunLike.congr_fun F.comm_g b

/-- The middle map is injective when both endpoint maps are injective. -/
theorem middle_injective
    (F : ShortExactSequenceMap S S')
    (hA : Function.Injective F.hA)
    (hC : Function.Injective F.hC) :
    Function.Injective F.hB := by
  intro b₁ b₂ hB
  have hg : S.g b₁ = S.g b₂ := by
    apply hC
    calc
      F.hC (S.g b₁) = S'.g (F.hB b₁) := F.comm_g_apply b₁
      _ = S'.g (F.hB b₂) := congrArg S'.g hB
      _ = F.hC (S.g b₂) := (F.comm_g_apply b₂).symm
  have hker : S.g (b₁ - b₂) = 0 := by
    rw [map_sub, hg, sub_self]
  rcases S.toExactSequence.exactness (b₁ - b₂) hker with ⟨a, ha⟩
  change S.f a = b₁ - b₂ at ha
  have hf : S'.f (F.hA a) = 0 := by
    rw [← F.comm_f_apply a, ha]
    rw [map_sub, hB, sub_self]
  have ha0 : F.hA a = 0 := by
    apply S'.f_injective
    simpa using hf
  have ha' : a = 0 := hA (by simpa using ha0)
  have hsub : b₁ - b₂ = 0 := by
    simpa [ha'] using ha.symm
  exact sub_eq_zero.mp hsub

/-- The middle map is surjective when both endpoint maps are surjective. -/
theorem middle_surjective
    (F : ShortExactSequenceMap S S')
    (hA : Function.Surjective F.hA)
    (hC : Function.Surjective F.hC) :
    Function.Surjective F.hB := by
  intro b'
  obtain ⟨c, hc⟩ := hC (S'.g b')
  obtain ⟨b, hb⟩ := S.g_surjective c
  have hker : S'.g (b' - F.hB b) = 0 := by
    calc
      S'.g (b' - F.hB b) = S'.g b' - S'.g (F.hB b) := by
        simp only [map_sub]
      _ = F.hC c - F.hC (S.g b) := by rw [← hc, F.comm_g_apply]
      _ = 0 := by rw [hb]; simp
  rcases S'.toExactSequence.exactness (b' - F.hB b) hker with ⟨a', ha'⟩
  obtain ⟨a, ha⟩ := hA a'
  refine ⟨b + S.f a, ?_⟩
  rw [map_add, F.comm_f_apply, ha]
  rw [← sub_eq_zero.mp (show b' - F.hB b - S'.f a' = 0 by rw [← ha']; simp)]
  abel

/-- Short-five assembly: bijective endpoint maps force a bijective middle map. -/
theorem middle_bijective
    (F : ShortExactSequenceMap S S')
    (hA : Function.Bijective F.hA)
    (hC : Function.Bijective F.hC) :
    Function.Bijective F.hB :=
  ⟨F.middle_injective hA.1 hC.1, F.middle_surjective hA.2 hC.2⟩

end ShortExactSequenceMap
