import proofs.RealO55CartanDieudonne
import InfoGeometry.Projective.Cl55NullBoundaryBridge

/-!
# Full real Pin action on the `Q55` projective null boundary

This bridge uses the existing full-real `Pin(5,5)` vector representation and
the existing generic projective-null quotient.  It does not identify the full
real Pin carrier with the older star-unitary `Clifford55.Pin55` carrier.
-/

noncomputable section

namespace RealO55ProjectiveBoundaryAction

open Clifford55
open RealPin55Core
open RealPin55TwistedAction
open RealPin55OrthogonalAction
open RealPin55QuadraticRepresentation
open RealPin55ReflectionGenerators
open InfoGeometry.Projective
open InfoGeometry.Projective.Cl55NullBoundaryBridge
open InfoGeometry.Projective.ProjectiveNullBoundaryDatum


/-- The full-real Pin action as an equivariant map of `Q55` carriers. -/
noncomputable def fullPinBoundaryHom (g : FullPin55) :
    BoundaryHom Cl55NullBoundaryBridge.datum Cl55NullBoundaryBridge.datum where
  toFun := fullPinVectorRepresentation g
  map_zero := (fullPinVectorRepresentation g).map_zero
  map_null := by
    intro v hv
    calc
      Q55 (fullPinVectorRepresentation g v) =
          Q55 (twistedVector g v) := by rfl
      _ = Q55 v := fullPin55_preserves_Q g v
      _ = 0 := hv
  map_ne_zero := by
    intro v hv hzero
    apply hv
    apply (fullPinVectorRepresentation g).injective
    have hzero0 : fullPinVectorRepresentation g v = (0 : V55) := by
      simpa [Cl55NullBoundaryBridge.datum] using hzero
    calc
      fullPinVectorRepresentation g v = 0 := hzero0
      _ = fullPinVectorRepresentation g (0 : V55) := by
        rw [(fullPinVectorRepresentation g).map_zero]
      _ = fullPinVectorRepresentation g Cl55NullBoundaryBridge.datum.zero := rfl
  map_scale := by
    intro u v
    exact (fullPinVectorRepresentation g).map_smul (u : ℝ) v

/-- Descent of the full-real Pin action to the projective null quotient. -/
noncomputable def fullPinBoundaryAction (g : FullPin55) : Cl55NullBoundaryBridge.Boundary → Cl55NullBoundaryBridge.Boundary :=
  BoundaryHom.mapBoundary (fullPinBoundaryHom g)

theorem fullPinBoundaryAction_one (Z : Cl55NullBoundaryBridge.NullRep) :
    fullPinBoundaryAction (1 : FullPin55) (Cl55NullBoundaryBridge.mk Z) =
      Cl55NullBoundaryBridge.mk Z := by
  rw [ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary_nullMk]
  apply congrArg (nullMk Cl55NullBoundaryBridge.datum)
  apply ProjectiveNullBoundaryDatum.NullRep.ext_Z
  change fullPinVectorRepresentation (1 : FullPin55) Z.Z = Z.Z
  rw [map_one]
  rfl

theorem fullPinBoundaryAction_mul (g h : FullPin55) (Z : Cl55NullBoundaryBridge.NullRep) :
    fullPinBoundaryAction (g * h) (Cl55NullBoundaryBridge.mk Z) =
      fullPinBoundaryAction g
        (fullPinBoundaryAction h (Cl55NullBoundaryBridge.mk Z)) := by
  rw [ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary_nullMk, ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary_nullMk]
  apply congrArg (nullMk Cl55NullBoundaryBridge.datum)
  apply ProjectiveNullBoundaryDatum.NullRep.ext_Z
  change fullPinVectorRepresentation (g * h) Z.Z =
    fullPinVectorRepresentation g (fullPinVectorRepresentation h Z.Z)
  rw [map_mul]
  rfl

/-! ## The orthogonal action and Pin-to-orthogonal factorization -/

/-- An `OQ55` transformation acts equivariantly on the same null quotient. -/
noncomputable def oqBoundaryHom (f : OQ55) :
    BoundaryHom Cl55NullBoundaryBridge.datum Cl55NullBoundaryBridge.datum where
  toFun := f.1
  map_zero := f.1.map_zero
  map_null := by
    intro v hv
    calc
      Q55 (f.1 v) = Q55 v := f.2 v
      _ = 0 := hv
  map_ne_zero := by
    intro v hv hzero
    apply hv
    apply f.1.injective
    have hzero0 : f.1 v = (0 : V55) := by
      simpa [Cl55NullBoundaryBridge.datum] using hzero
    calc
      f.1 v = 0 := hzero0
      _ = f.1 (0 : V55) := by rw [f.1.map_zero]
      _ = f.1 Cl55NullBoundaryBridge.datum.zero := rfl
  map_scale := by
    intro u v
    exact f.1.map_smul (u : ℝ) v

noncomputable def oqBoundaryAction (f : OQ55) : Cl55NullBoundaryBridge.Boundary → Cl55NullBoundaryBridge.Boundary :=
  BoundaryHom.mapBoundary (oqBoundaryHom f)

theorem oqBoundaryAction_one (Z : Cl55NullBoundaryBridge.NullRep) :
    oqBoundaryAction (1 : OQ55) (Cl55NullBoundaryBridge.mk Z) =
      Cl55NullBoundaryBridge.mk Z := by
  rw [ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary_nullMk]
  apply congrArg (nullMk Cl55NullBoundaryBridge.datum)
  apply ProjectiveNullBoundaryDatum.NullRep.ext_Z
  change (1 : OQ55).1 Z.Z = Z.Z
  simp

theorem oqBoundaryAction_mul (f h : OQ55) (Z : Cl55NullBoundaryBridge.NullRep) :
    oqBoundaryAction (f * h) (Cl55NullBoundaryBridge.mk Z) =
      oqBoundaryAction f (oqBoundaryAction h (Cl55NullBoundaryBridge.mk Z)) := by
  rw [ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary_nullMk, ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary_nullMk]
  apply congrArg (nullMk Cl55NullBoundaryBridge.datum)
  apply ProjectiveNullBoundaryDatum.NullRep.ext_Z
  change (f * h).1 Z.Z = f.1 (h.1 Z.Z)
  rfl

/-- The native orthogonal boundary action is invertible, with inverse induced
by the inverse orthogonal transformation. -/
noncomputable def oqBoundaryPermutation (f : OQ55) : Equiv.Perm Cl55NullBoundaryBridge.Boundary where
  toFun := oqBoundaryAction f
  invFun := oqBoundaryAction f⁻¹
  left_inv := by
    intro X
    refine Quotient.inductionOn X ?_
    intro Z
    change oqBoundaryAction f⁻¹
        (oqBoundaryAction f (Cl55NullBoundaryBridge.mk Z)) =
      Cl55NullBoundaryBridge.mk Z
    rw [← oqBoundaryAction_mul]
    simpa [ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary_nullMk] using oqBoundaryAction_one Z
  right_inv := by
    intro X
    refine Quotient.inductionOn X ?_
    intro Z
    change oqBoundaryAction f
        (oqBoundaryAction f⁻¹ (Cl55NullBoundaryBridge.mk Z)) =
      Cl55NullBoundaryBridge.mk Z
    rw [← oqBoundaryAction_mul]
    simpa [ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary_nullMk] using oqBoundaryAction_one Z

/-- Native permutation-valued representation of `OQ55` on the projective
null boundary. -/
noncomputable def oqBoundaryPermutationRepresentation :
    OQ55 →* Equiv.Perm Cl55NullBoundaryBridge.Boundary where
  toFun := oqBoundaryPermutation
  map_one' := by
    ext X
    refine Quotient.inductionOn X ?_
    intro Z
    change oqBoundaryAction (1 : OQ55)
        (Cl55NullBoundaryBridge.mk Z) =
      Cl55NullBoundaryBridge.mk Z
    exact oqBoundaryAction_one Z
  map_mul' := by
    intro f h
    ext X
    refine Quotient.inductionOn X ?_
    intro Z
    change oqBoundaryAction (f * h)
        (Cl55NullBoundaryBridge.mk Z) =
      oqBoundaryAction f
        (oqBoundaryAction h (Cl55NullBoundaryBridge.mk Z))
    exact oqBoundaryAction_mul f h Z

/-- The native `OQ55` action on the projective null boundary. -/
noncomputable def oqBoundaryRepresentation :
    OQ55 →* Function.End Cl55NullBoundaryBridge.Boundary where
  toFun := oqBoundaryAction
  map_one' := by
    funext x
    refine Quotient.inductionOn
      (s := nullRepSetoid Cl55NullBoundaryBridge.datum) x ?_
    intro Z
    exact oqBoundaryAction_one Z
  map_mul' := by
    intro f h
    funext x
    refine Quotient.inductionOn
      (s := nullRepSetoid Cl55NullBoundaryBridge.datum) x ?_
    intro Z
    change oqBoundaryAction (f * h)
        (Cl55NullBoundaryBridge.mk Z) =
      oqBoundaryAction f
        (oqBoundaryAction h (Cl55NullBoundaryBridge.mk Z))
    exact oqBoundaryAction_mul f h Z

/-- The full-real Pin action on the projective null boundary is a monoid
homomorphism, hence a genuine noncommutative group action. -/
noncomputable def fullPinBoundaryRepresentation :
    FullPin55 →* Function.End Cl55NullBoundaryBridge.Boundary where
  toFun := fullPinBoundaryAction
  map_one' := by
    funext x
    refine Quotient.inductionOn
      (s := nullRepSetoid Cl55NullBoundaryBridge.datum) x ?_
    intro Z
    exact fullPinBoundaryAction_one Z
  map_mul' := by
    intro g h
    funext x
    refine Quotient.inductionOn
      (s := nullRepSetoid Cl55NullBoundaryBridge.datum) x ?_
    intro Z
    change fullPinBoundaryAction (g * h)
        (Cl55NullBoundaryBridge.mk Z) =
      fullPinBoundaryAction g
        (fullPinBoundaryAction h (Cl55NullBoundaryBridge.mk Z))
    exact fullPinBoundaryAction_mul g h Z

theorem fullPinBoundaryRepresentation_factorization :
    fullPinBoundaryRepresentation =
      oqBoundaryRepresentation.comp fullPinToOQ55 := by
  apply MonoidHom.ext
  intro g
  funext x
  refine Quotient.inductionOn
    (s := nullRepSetoid Cl55NullBoundaryBridge.datum) x ?_
  intro Z
  change fullPinBoundaryAction g (Cl55NullBoundaryBridge.mk Z) =
    oqBoundaryAction (fullPinToOQ55 g) (Cl55NullBoundaryBridge.mk Z)
  rw [ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary_nullMk, ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary_nullMk]
  apply congrArg (nullMk Cl55NullBoundaryBridge.datum)
  apply ProjectiveNullBoundaryDatum.NullRep.ext_Z
  rfl

/-- Surjectivity of the real Pin-to-orthogonal map makes the full Pin and
`OQ55` boundary representations have the same range. -/
theorem fullPinBoundaryRepresentation_range_eq :
    Set.range fullPinBoundaryRepresentation =
      Set.range oqBoundaryRepresentation := by
  apply Set.Subset.antisymm
  · intro F hF
    rcases hF with ⟨g, rfl⟩
    exact ⟨fullPinToOQ55 g, rfl⟩
  · intro F hF
    rcases hF with ⟨f, rfl⟩
    rcases RealO55CartanDieudonne.fullPinToOQ55_surjective f with
      ⟨g, hg⟩
    refine ⟨g, ?_⟩
    calc
      fullPinBoundaryRepresentation g =
          (oqBoundaryRepresentation.comp fullPinToOQ55) g := by
            rw [fullPinBoundaryRepresentation_factorization]
      _ = oqBoundaryRepresentation (fullPinToOQ55 g) := rfl
      _ = oqBoundaryRepresentation f := by rw [hg]

/-! ## Reflection-generated closure on the native boundary -/

open RealO55CartanDieudonne

/-- Inclusion of the constructive reflection subgroup into `OQ55`. -/
noncomputable def reflectionGeneratedOQ55_subtypeHom :
    reflectionGeneratedOQ55 →* OQ55 :=
  Subgroup.subtype reflectionGeneratedOQ55

/-- Restriction of the native `OQ55` boundary representation to the
reflection-generated subgroup. -/
noncomputable def reflectionGeneratedBoundaryRepresentation :
    reflectionGeneratedOQ55 →* Function.End Cl55NullBoundaryBridge.Boundary :=
  oqBoundaryRepresentation.comp reflectionGeneratedOQ55_subtypeHom

/-! ## Native permutation-valued restrictions -/

/-- The full real Pin boundary action as a genuine permutation-valued
representation.  This is obtained by composing the native orthogonal
permutation representation with the already-proved Pin-to-orthogonal map. -/
noncomputable def fullPinBoundaryPermutationRepresentation :
    FullPin55 →* Equiv.Perm Cl55NullBoundaryBridge.Boundary :=
  oqBoundaryPermutationRepresentation.comp fullPinToOQ55

/-- The reflection-generated boundary action as a genuine permutation-valued
representation, obtained by restricting the native `OQ55` permutation
representation along the reflection-subgroup inclusion. -/
noncomputable def reflectionGeneratedBoundaryPermutationRepresentation :
    reflectionGeneratedOQ55 →* Equiv.Perm Cl55NullBoundaryBridge.Boundary :=
  oqBoundaryPermutationRepresentation.comp reflectionGeneratedOQ55_subtypeHom

/-- Constructive Cartan--Dieudonné makes the reflection-generated boundary
action have exactly the full native `OQ55` action range. -/
theorem reflectionGeneratedBoundaryRepresentation_range_eq :
    Set.range reflectionGeneratedBoundaryRepresentation =
      Set.range oqBoundaryRepresentation := by
  apply Set.Subset.antisymm
  · intro F hF
    rcases hF with ⟨g, rfl⟩
    exact ⟨g.1, rfl⟩
  · intro F hF
    rcases hF with ⟨f, rfl⟩
    have hf : f ∈ reflectionGeneratedOQ55 := by
      rw [RealO55CartanDieudonne.reflectionGeneratedOQ55_eq_top]
      trivial
    refine ⟨⟨f, hf⟩, ?_⟩
    rfl

/-- The reflection-generated, orthogonal, and full-real-Pin boundary action
ranges coincide. -/
theorem reflectionGeneratedBoundaryRepresentation_range_eq_fullPin :
    Set.range reflectionGeneratedBoundaryRepresentation =
      Set.range fullPinBoundaryRepresentation := by
  rw [reflectionGeneratedBoundaryRepresentation_range_eq,
    fullPinBoundaryRepresentation_range_eq]

/-! ## Native Mathlib actions -/

/-- The native quadratic orthogonal group acts on its projective null boundary. -/
noncomputable instance oqBoundaryMulAction :
    MulAction OQ55 Cl55NullBoundaryBridge.Boundary where
  smul := oqBoundaryAction
  one_smul := by
    intro X
    change oqBoundaryRepresentation (1 : OQ55) X = X
    rw [map_one]
    rfl
  mul_smul := by
    intro f g X
    change oqBoundaryRepresentation (f * g) X =
      oqBoundaryRepresentation f
        (oqBoundaryRepresentation g X)
    rw [map_mul]
    rfl

/-- The full real Pin carrier acts through its native orthogonal boundary
representation. -/
noncomputable instance fullPinBoundaryMulAction :
    MulAction RealPin55Core.FullPin55 Cl55NullBoundaryBridge.Boundary where
  smul := fullPinBoundaryAction
  one_smul := by
    intro X
    change fullPinBoundaryRepresentation
        (1 : RealPin55Core.FullPin55) X = X
    rw [map_one]
    rfl
  mul_smul := by
    intro g h X
    change fullPinBoundaryRepresentation (g * h) X =
      fullPinBoundaryRepresentation g
        (fullPinBoundaryRepresentation h X)
    rw [map_mul]
    rfl

theorem fullPinBoundary_smul_factors_through_oq
    (g : RealPin55Core.FullPin55) (X : Cl55NullBoundaryBridge.Boundary) :
    g • X = (fullPinToOQ55 g) • X := by
  change fullPinBoundaryRepresentation g X =
    oqBoundaryRepresentation (fullPinToOQ55 g) X
  rw [fullPinBoundaryRepresentation_factorization]
  rfl

/-- Every native orthogonal boundary action has a full real Pin lift. -/
theorem exists_fullPin_boundary_smul_eq
    (f : OQ55) (X : Cl55NullBoundaryBridge.Boundary) :
    ∃ p : RealPin55Core.FullPin55, p • X = f • X := by
  rcases RealO55CartanDieudonne.fullPinToOQ55_surjective f with
    ⟨p, hp⟩
  refine ⟨p, ?_⟩
  rw [fullPinBoundary_smul_factors_through_oq, hp]

/-- The canonical Pin lift of an anisotropic vector and its native
orthogonal reflection induce the same boundary action. -/
theorem anisotropicPinLift_boundary_smul_eq
    (a : V55) (ha : Q55 a ≠ 0) (X : Cl55NullBoundaryBridge.Boundary) :
    anisotropicPinLift a ha • X =
      RealO55CartanDieudonne.oqReflection a ha • X := by
  rw [fullPinBoundary_smul_factors_through_oq]
  rfl

/-- The constructive reflection-generated subgroup acts on the native
projective boundary. -/
noncomputable instance reflectionGeneratedBoundaryMulAction :
    MulAction reflectionGeneratedOQ55 Cl55NullBoundaryBridge.Boundary where
  smul := fun g X => oqBoundaryAction g.1 X
  one_smul := by
    intro X
    change oqBoundaryRepresentation
        (1 : OQ55) X = X
    rw [map_one]
    rfl
  mul_smul := by
    intro g h X
    change oqBoundaryRepresentation (g.1 * h.1) X =
      oqBoundaryRepresentation g.1
        (oqBoundaryRepresentation h.1 X)
    rw [map_mul]
    rfl

/-- Every native orthogonal boundary action is realized by a product of
anisotropic reflections. -/
theorem exists_reflectionGenerated_boundary_smul_eq
    (f : OQ55) (X : Cl55NullBoundaryBridge.Boundary) :
    ∃ r : reflectionGeneratedOQ55, r • X = f • X := by
  have hf : f ∈ reflectionGeneratedOQ55 := by
    rw [RealO55CartanDieudonne.reflectionGeneratedOQ55_eq_top]
    trivial
  refine ⟨⟨f, hf⟩, ?_⟩
  rfl

/-- The reflection-generated boundary action has the native inverse law. -/
theorem reflectionGeneratedBoundary_inv_smul_smul
    (r : reflectionGeneratedOQ55) (X : Cl55NullBoundaryBridge.Boundary) :
    r⁻¹ • r • X = X := by
  exact inv_smul_smul r X

end RealO55ProjectiveBoundaryAction

end noncomputable section
