import InfoGeometry.Twistor.Incidence
import InfoGeometry.Twistor.NullProjective
import InfoGeometry.Canonical.TomitaKreinNilpotentAtom

/-!
# Five-Graded Twistor Incidence

This module packages the incidence-equation layer for the five-graded
conformal/Tomita-Krein model.

It deliberately keeps three surfaces separate:

* an abstract real doubled twistor atom with `J`, `ε`, and `I = Jε`;
* incidence and mirror-incidence data for the projective/twistor chart;
* the local nilpotent light-cone identities, imported from the proven
  Tomita-Krein `Cl(1,1)` atom.

No current-algebra or Virasoro anomaly is asserted here.
-/

namespace FiveGradedIncidence

open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.TomitaKreinNilpotentAtom
open InfoGeometry.Krein

universe u v

/-! ## 1. Real doubled twistor atom -/

/--
Finite real doubled twistor atom.

The operator `I` is the internal Hestenes-Krein phase axis replacing the
external scalar `i` in the incidence equation.
-/
structure RealDoubledTwistorAtom (V : Type u) [AddCommGroup V] [Module ℝ V] where
  J : V →ₗ[ℝ] V
  eps : V →ₗ[ℝ] V
  I : V →ₗ[ℝ] V
  J_sq : J.comp J = LinearMap.id
  eps_sq : eps.comp eps = LinearMap.id
  anticomm : J.comp eps = -(eps.comp J)
  I_def : I = J.comp eps
  I_sq : I.comp I = -LinearMap.id

namespace RealDoubledTwistorAtom

variable {V : Type u} [AddCommGroup V] [Module ℝ V]
variable (A : RealDoubledTwistorAtom V)

@[simp] theorem J_involutive : A.J.comp A.J = LinearMap.id := A.J_sq

@[simp] theorem eps_involutive : A.eps.comp A.eps = LinearMap.id := A.eps_sq

theorem phase_axis_def : A.I = A.J.comp A.eps := A.I_def

@[simp] theorem phase_axis_sq : A.I.comp A.I = -LinearMap.id := A.I_sq

end RealDoubledTwistorAtom

/-! ## 2. Incidence and Tomita mirror incidence -/

/--
Abstract incidence datum.

`spaceAction x` is the spinor-matrix action of the spacetime chart `x`.  The
incidence equation is

`omega Z = I (spaceAction x (pi Z))`.

The mirror law records the geometric input that Tomita/projective inversion
sends an incident twistor to the incidence relation in the inverted chart.
-/
structure IncidenceDatum (X : Type v) (V : Type u) [AddCommGroup V] [Module ℝ V] where
  atom : RealDoubledTwistorAtom V
  omega : V →ₗ[ℝ] V
  pi : V →ₗ[ℝ] V
  spaceAction : X → V →ₗ[ℝ] V
  conformalInverse : X → X
  mirror_incidence :
    ∀ x Z,
      omega Z = atom.I (spaceAction x (pi Z)) →
      omega (atom.J Z) = atom.I (spaceAction (conformalInverse x) (pi (atom.J Z)))

namespace IncidenceDatum

variable {X : Type v} {V : Type u} [AddCommGroup V] [Module ℝ V]
variable (D : IncidenceDatum X V)

/-- Hestenes-Krein twistor incidence: `ω = I x π`. -/
def Incidence (x : X) (Z : V) : Prop :=
  D.omega Z = D.atom.I (D.spaceAction x (D.pi Z))

/-- Tomita/projective inversion sends incidence to the inverted chart. -/
theorem tomita_mirror_swaps_chiral_incidence
    {x : X} {Z : V} :
    D.Incidence x Z →
      D.Incidence (D.conformalInverse x) (D.atom.J Z) := by
  exact D.mirror_incidence x Z

/-- The internal incidence phase squares to minus the identity. -/
theorem internal_phase_axis_square :
    D.atom.I.comp D.atom.I = -LinearMap.id := by
  exact D.atom.I_sq

end IncidenceDatum

/-! ## 3. Boundary Majorana twistor predicates -/

/--
Boundary Majorana incidence condition.

`P∂` selects the boundary/edge sector, `P0` selects the zero-mode sector, `J`
is the Tomita/PHS mirror, and `D∂` is the boundary zero-mode operator.
-/
def IsMajoranaBoundaryTwistor
    {V : Type u} [AddCommGroup V] [Module ℝ V]
    (Pbdry P0 J Dbdry : V →ₗ[ℝ] V) (Z : V) : Prop :=
  Pbdry Z = Z ∧ P0 Z = Z ∧ J Z = Z ∧ Dbdry Z = 0

variable {V : Type u} [AddCommGroup V] [Module ℝ V]
variable {Pbdry P0 J Dbdry : V →ₗ[ℝ] V} {Z : V}

theorem majorana_boundary_twistor_boundary_supported
    (h : IsMajoranaBoundaryTwistor Pbdry P0 J Dbdry Z) :
    Pbdry Z = Z :=
  h.1

theorem majorana_boundary_twistor_zero_mode_supported
    (h : IsMajoranaBoundaryTwistor Pbdry P0 J Dbdry Z) :
    P0 Z = Z :=
  h.2.1

theorem majorana_boundary_twistor_is_real
    (h : IsMajoranaBoundaryTwistor Pbdry P0 J Dbdry Z) :
    J Z = Z :=
  h.2.2.1

theorem majorana_boundary_twistor_boundary_zero_mode
    (h : IsMajoranaBoundaryTwistor Pbdry P0 J Dbdry Z) :
    Dbdry Z = 0 :=
  h.2.2.2

/-! ## 4. Five-graded incidence algebra interface -/

/--
One-sorted five-graded bracket interface.

This is intentionally leaner than a full dependent graded Lie algebra: it is
the incidence-level contract that brackets add degrees and inversion reverses
degree. A later native `|2|`-graded Lie algebra can refine this surface.
-/
structure FiveGradedTwistorAlgebra (Elem : Type u) where
  grade : Elem → ℤ
  bracket : Elem → Elem → Elem
  inversion : Elem → Elem
  bracket_grade : ∀ X Y, grade (bracket X Y) = grade X + grade Y
  inversion_grade : ∀ X, grade (inversion X) = -grade X
  inversion_involutive : ∀ X, inversion (inversion X) = X

namespace FiveGradedTwistorAlgebra

variable {Elem : Type u} (G : FiveGradedTwistorAlgebra Elem)

theorem bracket_respects_grade (X Y : Elem) :
    G.grade (G.bracket X Y) = G.grade X + G.grade Y :=
  G.bracket_grade X Y

theorem projective_inversion_reverses_grade (X : Elem) :
    G.grade (G.inversion X) = -G.grade X :=
  G.inversion_grade X

theorem projective_inversion_sq (X : Elem) :
    G.inversion (G.inversion X) = X :=
  G.inversion_involutive X

end FiveGradedTwistorAlgebra

/--
The chiral bracket targets of the five-graded model:
`S₊ × S₊ → g₂`, `S₋ × S₋ → g₋₂`, and `S₊ × S₋ → g₀`.
-/
structure ChiralBracketDatum
    (Splus Sminus Gzero GplusTwo GminusTwo : Type u) where
  bracket_plus_plus : Splus → Splus → GplusTwo
  bracket_minus_minus : Sminus → Sminus → GminusTwo
  bracket_plus_minus : Splus → Sminus → Gzero

/-! ## 5. Concrete local nilpotent light-cone theorem -/

section ConcreteAtom

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
The concrete split-null maps in the Tomita-Krein atom give the local light-cone
incidence algebra: the two null maps square to zero and multiply to the two
spectral chiral projectors.
-/
theorem nilpotent_lightcone_incidence :
    (concreteCARCreation (E := E)).comp (concreteCARCreation (E := E)) = 0
      ∧ (concreteCARAnnihilation (E := E)).comp
          (concreteCARAnnihilation (E := E)) = 0
      ∧ (concreteCARCreation (E := E)).comp (concreteCARAnnihilation (E := E))
        = spectralPlusProj (E := E)
      ∧ (concreteCARAnnihilation (E := E)).comp (concreteCARCreation (E := E))
        = spectralMinusProj (E := E) := by
  have h := tomitaKrein_nilpotent_idempotent_atom (E := E)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- Tomita/PHS conjugation swaps the two concrete split-null light-cone maps. -/
theorem tomita_mirror_swaps_concrete_lightcone :
    tomitaConjOp (E := E) (concreteCARCreation (E := E))
      = concreteCARAnnihilation (E := E)
    ∧ tomitaConjOp (E := E) (concreteCARAnnihilation (E := E))
      = concreteCARCreation (E := E) := by
  exact ⟨tomitaConj_creation_eq_annihilation (E := E),
    tomitaConj_annihilation_eq_creation (E := E)⟩

end ConcreteAtom

end FiveGradedIncidence
