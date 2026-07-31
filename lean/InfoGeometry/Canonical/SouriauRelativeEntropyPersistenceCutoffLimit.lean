import InfoGeometry.Canonical.SouriauRelativeEntropyPersistenceCutoffFunctor

namespace SouriauRelativeEntropyPersistenceCutoffLimit

open CategoryTheory
open CategoryTheory.Limits
open SouriauRelativeEntropyPersistenceColimit
open SouriauRelativeEntropyPersistenceCutoff
open SouriauRelativeEntropyPersistenceCutoffFunctor

/-- The inverse limit over all positive-simplex cutoffs. -/
abbrev RelativeEntropyPersistenceCutoffLimit
    (n : ℕ) : Type :=
  (limit (relativeEntropyPersistenceCutoffFunctor n) : TopCat)

/-- Canonical continuous projection from the cutoff limit to one cutoff colimit. -/
noncomputable def relativeEntropyPersistenceCutoffLimitProjection
    (n : ℕ) (ε : ℝ) :
    C(RelativeEntropyPersistenceCutoffLimit n,
      RelativeEntropyPersistenceColimit (n := n) ε) :=
  (limit.π
    (relativeEntropyPersistenceCutoffFunctor n)
    (Opposite.op ε)).hom

theorem relativeEntropyPersistenceCutoffLimitProjection_compat
    (n : ℕ) {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂)
    (x : RelativeEntropyPersistenceCutoffLimit n) :
    relativeEntropyPersistenceCutoffColimitMap hε
        (relativeEntropyPersistenceCutoffLimitProjection n ε₂ x) =
      relativeEntropyPersistenceCutoffLimitProjection n ε₁ x := by
  let h :
      (Opposite.op ε₂ : ℝᵒᵖ) ⟶ Opposite.op ε₁ :=
    (homOfLE hε).op
  have hw :=
    limit.w (relativeEntropyPersistenceCutoffFunctor n) h
  exact congrArg
    (fun k :
      limit (relativeEntropyPersistenceCutoffFunctor n) ⟶
        (relativeEntropyPersistenceCutoffFunctor n).obj
          (Opposite.op ε₁) =>
      k x) hw

/-- A cutoff-compatible family of continuous maps into all cutoff colimits. -/
structure RelativeEntropyPersistenceCutoffCompatibleFamily
    (n : ℕ) (X : Type) [TopologicalSpace X] where
  map :
    ∀ ε : ℝ,
      C(X, RelativeEntropyPersistenceColimit (n := n) ε)

namespace RelativeEntropyPersistenceCutoffCompatibleFamily

/-- A cutoff-compatible family is a cone over the cutoff functor. -/
noncomputable def toCone
    {n : ℕ} {X : Type} [TopologicalSpace X]
    (family :
      RelativeEntropyPersistenceCutoffCompatibleFamily n X)
    (hcompat :
      ∀ {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) (x : X),
        relativeEntropyPersistenceCutoffColimitMap hε
            (family.map ε₂ x) =
          family.map ε₁ x) :
    Cone (relativeEntropyPersistenceCutoffFunctor n) where
  pt := TopCat.of X
  π :=
    { app := fun ε => TopCat.ofHom (family.map ε.unop)
      naturality := by
        intro ε₂ ε₁ h
        apply TopCat.hom_ext
        ext x
        exact (hcompat (leOfHom h.unop) x).symm }

/-- The continuous map induced into the cutoff inverse limit. -/
noncomputable def lift
    {n : ℕ} {X : Type} [TopologicalSpace X]
    (family :
      RelativeEntropyPersistenceCutoffCompatibleFamily n X)
    (hcompat :
      ∀ {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) (x : X),
        relativeEntropyPersistenceCutoffColimitMap hε
            (family.map ε₂ x) =
          family.map ε₁ x) :
    C(X, RelativeEntropyPersistenceCutoffLimit n) :=
  (limit.lift
    (relativeEntropyPersistenceCutoffFunctor n)
    (family.toCone hcompat)).hom

@[simp] theorem projection_lift
    {n : ℕ} {X : Type} [TopologicalSpace X]
    (family :
      RelativeEntropyPersistenceCutoffCompatibleFamily n X)
    (hcompat :
      ∀ {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) (x : X),
        relativeEntropyPersistenceCutoffColimitMap hε
            (family.map ε₂ x) =
          family.map ε₁ x)
    (ε : ℝ) (x : X) :
    relativeEntropyPersistenceCutoffLimitProjection n ε
        (family.lift hcompat x) =
      family.map ε x := by
  have hfac :=
    limit.lift_π (family.toCone hcompat) (Opposite.op ε)
  exact congrArg
    (fun k :
      TopCat.of X ⟶
        (relativeEntropyPersistenceCutoffFunctor n).obj
          (Opposite.op ε) =>
      k x) hfac

theorem lift_unique
    {n : ℕ} {X : Type} [TopologicalSpace X]
    (family :
      RelativeEntropyPersistenceCutoffCompatibleFamily n X)
    (hcompat :
      ∀ {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) (x : X),
        relativeEntropyPersistenceCutoffColimitMap hε
            (family.map ε₂ x) =
          family.map ε₁ x)
    (g : C(X, RelativeEntropyPersistenceCutoffLimit n))
    (hg :
      ∀ (ε : ℝ) (x : X),
        relativeEntropyPersistenceCutoffLimitProjection n ε (g x) =
          family.map ε x) :
    g = family.lift hcompat := by
  have hhom :
      TopCat.ofHom g =
        limit.lift
          (relativeEntropyPersistenceCutoffFunctor n)
          (family.toCone hcompat) := by
    apply limit.hom_ext
    intro ε
    apply TopCat.hom_ext
    ext x
    exact
      (hg ε.unop x).trans
        (family.projection_lift hcompat ε.unop x).symm
  exact congrArg TopCat.Hom.hom hhom

theorem existsUnique_lift
    {n : ℕ} {X : Type} [TopologicalSpace X]
    (family :
      RelativeEntropyPersistenceCutoffCompatibleFamily n X)
    (hcompat :
      ∀ {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) (x : X),
        relativeEntropyPersistenceCutoffColimitMap hε
            (family.map ε₂ x) =
          family.map ε₁ x) :
    ∃! g : C(X, RelativeEntropyPersistenceCutoffLimit n),
      ∀ (ε : ℝ) (x : X),
        relativeEntropyPersistenceCutoffLimitProjection n ε (g x) =
          family.map ε x := by
  refine ⟨family.lift hcompat, ?_, ?_⟩
  · intro ε x
    exact family.projection_lift hcompat ε x
  · intro g hg
    exact family.lift_unique hcompat g hg

end RelativeEntropyPersistenceCutoffCompatibleFamily

end SouriauRelativeEntropyPersistenceCutoffLimit
