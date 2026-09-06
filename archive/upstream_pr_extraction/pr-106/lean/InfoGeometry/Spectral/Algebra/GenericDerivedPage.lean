import InfoGeometry.Spectral.Algebra.GradedExactCouple

/-!
# Derived pages of arbitrary graded exact couples

This file constructs the differential and homology page of a
`GradedExactCouple` using Mathlib submodules and quotients.  The page is
indexed by the source of its incoming differential.  Consequently both the
incoming boundaries and the cycles at their target live definitionally in the
same graded component.
-/

namespace InfoGeometry.Spectral.Algebra

universe u v

namespace GradedExactCouple

variable {R : Type u} [Ring R]
variable {I : Type v}
variable {D E : I → Type u}
variable [∀ p, AddCommGroup (D p)] [∀ p, AddCommGroup (E p)]
variable [∀ p, Module R (D p)] [∀ p, Module R (E p)]
variable {iDeg jDeg kDeg : I ≃ I}

/-- The degree of the exact-couple differential `d = j ∘ k`. -/
def differentialDegree
    (_C : GradedExactCouple R I D E iDeg jDeg kDeg) : I ≃ I :=
  kDeg.trans jDeg

@[simp]
theorem differentialDegree_apply
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    C.differentialDegree p =
      jDeg (kDeg p) :=
  rfl

/-- The differential induced by the two consecutive exact-couple arrows. -/
def differential
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    E p →ₗ[R] E (C.differentialDegree p) :=
  (C.j (kDeg p)).comp (C.k p)

@[simp]
theorem differential_apply
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (p : I) (x : E p) :
    C.differential p x = C.j (kDeg p) (C.k p x) :=
  rfl

/-- The graded differential commutes with canonical equality transport. -/
theorem differential_cast
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    {p q : I} (h : p = q) (x : E p) :
    LinearEquiv.cast
        (R := R) (M := E)
        (congrArg C.differentialDegree h)
        (C.differential p x) =
      C.differential q
        (LinearEquiv.cast (R := R) (M := E) h x) := by
  subst q
  rfl

/-- Exactness at `E` implies that the induced differential squares to zero. -/
theorem differential_comp_differential
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    (C.differential (C.differentialDegree p)).comp
        (C.differential p) = 0 := by
  ext x
  have hjRange :
      C.j (kDeg p) (C.k p x) ∈
        LinearMap.range (C.j (kDeg p)) :=
    ⟨C.k p x, rfl⟩
  have hk :
      C.k (jDeg (kDeg p))
          (C.j (kDeg p) (C.k p x)) = 0 := by
    change C.j (kDeg p) (C.k p x) ∈
      LinearMap.ker (C.k (jDeg (kDeg p)))
    rw [C.exact_jk (kDeg p)]
    exact hjRange
  change
    C.j (kDeg (jDeg (kDeg p)))
        (C.k (jDeg (kDeg p))
          (C.j (kDeg p) (C.k p x))) = 0
  rw [hk]
  exact map_zero (C.j (kDeg (jDeg (kDeg p))))

/-- Cycles at the target of the differential originating in degree `p`. -/
def targetCycles
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    Submodule R (E (C.differentialDegree p)) :=
  LinearMap.ker (C.differential (C.differentialDegree p))

/-- Boundaries entering the target of the differential originating at `p`. -/
def targetBoundaries
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    Submodule R (E (C.differentialDegree p)) :=
  LinearMap.range (C.differential p)

/-- Every incoming boundary is a cycle at its target. -/
theorem targetBoundaries_le_targetCycles
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    C.targetBoundaries p ≤ C.targetCycles p := by
  change
    LinearMap.range (C.differential p) ≤
      LinearMap.ker (C.differential (C.differentialDegree p))
  rw [LinearMap.range_le_ker_iff]
  exact C.differential_comp_differential p

/-- Incoming boundaries, regarded as a submodule of the target cycles. -/
def targetBoundariesInCycles
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    Submodule R (C.targetCycles p) :=
  (C.targetBoundaries p).comap (C.targetCycles p).subtype

/-- The first homology page: target cycles modulo incoming boundaries. -/
abbrev DerivedE
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :=
  C.targetCycles p ⧸ C.targetBoundariesInCycles p

/-- A cycle at the target of `d_p` determines a class in the derived page. -/
def targetCycleClass
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (p : I) (x : E (C.differentialDegree p))
    (hx : C.differential (C.differentialDegree p) x = 0) :
    C.DerivedE p :=
  Submodule.Quotient.mk ⟨x, hx⟩

/-- Every incoming differential represents zero in the derived page. -/
@[simp]
theorem targetCycleClass_differential_eq_zero
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (p : I) (x : E p) :
    C.targetCycleClass p (C.differential p x)
        (by
          have h :=
            LinearMap.congr_fun
              (C.differential_comp_differential p) x
          simpa [LinearMap.comp_apply] using h) =
      0 := by
  apply (Submodule.Quotient.mk_eq_zero _).2
  change C.differential p x ∈ C.targetBoundaries p
  exact ⟨x, rfl⟩

/--
The naturally indexed derived `E` family.  Its component at `p` is homology in
degree `p`, represented using the unique incoming differential source.
-/
abbrev DirectDerivedE
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :=
  C.DerivedE (C.differentialDegree.symm p)

end GradedExactCouple

end InfoGeometry.Spectral.Algebra
