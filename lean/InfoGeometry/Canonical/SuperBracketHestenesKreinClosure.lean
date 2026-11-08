import InfoGeometry.Canonical.SymmetryClosureConformalBlocks
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.SuperBracketHestenesKreinClosure

Finite algebraic symmetry closure via Hestenes--Krein involutions.

This is the repo-native replacement for analytic-continuation language:
analyticity is represented by algebraic compatibility with an involutive
Hestenes/Krein axis operator.  Operators may be even or odd relative to that
axis, and the superbracket closes in the corresponding graded sector.

No complex analytic continuation.
No conformal-block function theory.
No loop-group analytic representation.
No physical boundary-state construction.
-/

namespace InfoGeometry.Canonical.SuperBracketHestenesKreinClosure

/-- A linear generator intertwines a Hestenes/Krein axis `K` with scalar sign `σ`. -/
def IntertwinesBy {V : Type*} [AddCommGroup V] [Module ℂ V]
    (K : V →ₗ[ℂ] V) (σ : ℂ) (A : V →ₗ[ℂ] V) : Prop :=
  K.comp A = σ • (A.comp K)

/-- Even generators commute with the Hestenes/Krein axis. -/
def IsEven {V : Type*} [AddCommGroup V] [Module ℂ V]
    (K : V →ₗ[ℂ] V) (A : V →ₗ[ℂ] V) : Prop :=
  IntertwinesBy K 1 A

/-- Odd generators anticommute with the Hestenes/Krein axis. -/
def IsOdd {V : Type*} [AddCommGroup V] [Module ℂ V]
    (K : V →ₗ[ℂ] V) (A : V →ₗ[ℂ] V) : Prop :=
  IntertwinesBy K (-1) A

/-- Superbracket with supplied Koszul sign. -/
def superBracket {V : Type*} [AddCommGroup V] [Module ℂ V]
    (koszul : ℂ) (A B : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  A.comp B - koszul • (B.comp A)

namespace IntertwinesBy

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {K A B : V →ₗ[ℂ] V} {σ τ c : ℂ}

/-- Pointwise form of the intertwining relation. -/
theorem apply (hA : IntertwinesBy K σ A) (v : V) :
    K (A v) = σ • A (K v) := by
  simpa [IntertwinesBy, LinearMap.comp_apply] using congrArg (fun L : V →ₗ[ℂ] V => L v) hA

/-- Scalar multiples preserve the same Hestenes/Krein grade. -/
theorem smul (hA : IntertwinesBy K σ A) :
    IntertwinesBy K σ (c • A) := by
  ext v
  simp [LinearMap.comp_apply, apply hA, smul_smul, mul_comm]

/-- Sums of generators in the same grade remain in that grade. -/
theorem add (hA : IntertwinesBy K σ A) (hB : IntertwinesBy K σ B) :
    IntertwinesBy K σ (A + B) := by
  ext v
  simp [LinearMap.comp_apply, apply hA, apply hB, smul_add]

/-- Negatives preserve the same grade. -/
theorem neg (hA : IntertwinesBy K σ A) :
    IntertwinesBy K σ (-A) := by
  simpa using smul (K := K) (A := A) (σ := σ) (c := (-1 : ℂ)) hA

/-- Differences of generators in the same grade remain in that grade. -/
theorem sub (hA : IntertwinesBy K σ A) (hB : IntertwinesBy K σ B) :
    IntertwinesBy K σ (A - B) := by
  simpa [sub_eq_add_neg] using add hA (neg hB)

/-- Composition multiplies Hestenes/Krein grades. -/
theorem comp (hA : IntertwinesBy K σ A) (hB : IntertwinesBy K τ B) :
    IntertwinesBy K (σ * τ) (A.comp B) := by
  ext v
  simp [LinearMap.comp_apply, apply hA, apply hB, smul_smul]

/-- The superbracket closes in the product grade. -/
theorem superBracket (hA : IntertwinesBy K σ A) (hB : IntertwinesBy K τ B) (koszul : ℂ) :
    IntertwinesBy K (σ * τ) (superBracket koszul A B) := by
  change IntertwinesBy K (σ * τ) (A.comp B - koszul • (B.comp A))
  have hBA : IntertwinesBy K (σ * τ) (koszul • (B.comp A)) := by
    simpa [mul_comm] using (smul (c := koszul) (comp hB hA))
  exact sub (comp hA hB) hBA

end IntertwinesBy

/-- Even-even commutators are even. -/
theorem even_commutator_even {V : Type*} [AddCommGroup V] [Module ℂ V]
    {K A B : V →ₗ[ℂ] V} (hA : IsEven K A) (hB : IsEven K B) :
    IsEven K (superBracket 1 A B) := by
  simpa [IsEven, one_mul] using IntertwinesBy.superBracket hA hB 1

/-- Even-odd commutators are odd. -/
theorem even_odd_commutator_odd {V : Type*} [AddCommGroup V] [Module ℂ V]
    {K A B : V →ₗ[ℂ] V} (hA : IsEven K A) (hB : IsOdd K B) :
    IsOdd K (superBracket 1 A B) := by
  simpa [IsEven, IsOdd, one_mul] using IntertwinesBy.superBracket hA hB 1

/-- Odd-odd anticommutators are even. -/
theorem odd_odd_anticommutator_even {V : Type*} [AddCommGroup V] [Module ℂ V]
    {K A B : V →ₗ[ℂ] V} (hA : IsOdd K A) (hB : IsOdd K B) :
    IsEven K (superBracket (-1) A B) := by
  simpa [IsEven, IsOdd] using IntertwinesBy.superBracket hA hB (-1)

/-- A Hestenes/Krein Cartan packet: an involutive axis and even/odd generator families. -/
structure HestenesKreinCartanPacket (V : Type*) [AddCommGroup V] [Module ℂ V] where
  /-- Cartan/Krein involution axis. -/
  K : V →ₗ[ℂ] V
  /-- Involution law. -/
  K_sq : K.comp K = LinearMap.id
  /-- Even generators. -/
  evenGen : Type*
  /-- Odd generators. -/
  oddGen : Type*
  /-- Realization of even generators as linear maps. -/
  evenOp : evenGen → V →ₗ[ℂ] V
  /-- Realization of odd generators as linear maps. -/
  oddOp : oddGen → V →ₗ[ℂ] V
  /-- Even generators commute with `K`. -/
  even_closed : ∀ g, IsEven K (evenOp g)
  /-- Odd generators anticommute with `K`. -/
  odd_closed : ∀ g, IsOdd K (oddOp g)

namespace HestenesKreinCartanPacket

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (P : HestenesKreinCartanPacket V)

/-- Even-even symmetry closure stays even. -/
theorem even_even_closure (g h : P.evenGen) :
    IsEven P.K (superBracket 1 (P.evenOp g) (P.evenOp h)) :=
  even_commutator_even (P.even_closed g) (P.even_closed h)

/-- Even-odd symmetry closure stays odd. -/
theorem even_odd_closure (g : P.evenGen) (h : P.oddGen) :
    IsOdd P.K (superBracket 1 (P.evenOp g) (P.oddOp h)) :=
  even_odd_commutator_odd (P.even_closed g) (P.odd_closed h)

/-- Odd-odd superclosure returns to the even sector. -/
theorem odd_odd_closure (g h : P.oddGen) :
    IsEven P.K (superBracket (-1) (P.oddOp g) (P.oddOp h)) :=
  odd_odd_anticommutator_even (P.odd_closed g) (P.odd_closed h)

end HestenesKreinCartanPacket

end InfoGeometry.Canonical.SuperBracketHestenesKreinClosure
