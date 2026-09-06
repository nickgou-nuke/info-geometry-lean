import InfoGeometry.Spectral.Algebra.DerivedNaturality

/-!
# Algebraic stabilization of a derived page

The first convergence step for an exact couple is purely algebraic.  If the
incoming and outgoing differentials adjacent to one degree are zero, homology
at that degree is the module itself.  The proof below uses Mathlib's kernel,
range, quotient-by-bottom, and top-submodule equivalences directly.
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
variable (C : GradedExactCouple R I D E iDeg jDeg kDeg)

/-- A linear differential with a zero domain is the zero map. -/
theorem differential_eq_zero_of_domain_eq_zero
    (p : I) (h : ∀ x : E p, x = 0) :
    C.differential p = 0 := by
  apply LinearMap.ext
  intro x
  rw [h x]
  exact map_zero (C.differential p)

/-- A linear differential with a zero codomain is the zero map. -/
theorem differential_eq_zero_of_codomain_eq_zero
    (p : I)
    (h : ∀ x : E (C.differentialDegree p), x = 0) :
    C.differential p = 0 := by
  apply LinearMap.ext
  intro x
  exact h (C.differential p x)

include C in
/-- Exactness at `E (jDeg p)` forces that term to vanish whenever both
adjacent `D` terms vanish. -/
theorem E_eq_zero_of_adjacent_D_eq_zero
    (p : I)
    (hSource : ∀ x : D p, x = 0)
    (hTarget : ∀ x : D (kDeg (jDeg p)), x = 0) :
    ∀ x : E (jDeg p), x = 0 := by
  intro x
  have hkx : C.k (jDeg p) x = 0 :=
    hTarget (C.k (jDeg p) x)
  have hxRange : x ∈ LinearMap.range (C.j p) := by
    rw [← C.exact_jk p]
    exact hkx
  rcases hxRange with ⟨y, hy⟩
  rw [← hy, hSource y]
  exact map_zero (C.j p)

/-- A zero outgoing differential makes the cycle submodule the whole module. -/
theorem targetCycles_eq_top_of_differential_eq_zero
    (q : I)
    (h : C.differential (C.differentialDegree q) = 0) :
    C.targetCycles q = ⊤ := by
  apply top_unique
  intro x _
  change C.differential (C.differentialDegree q) x = 0
  rw [h]
  rfl

/-- A zero incoming differential makes the boundary submodule inside cycles
the bottom submodule. -/
theorem targetBoundariesInCycles_eq_bot_of_differential_eq_zero
    (q : I) (h : C.differential q = 0) :
    C.targetBoundariesInCycles q = ⊥ := by
  apply bot_unique
  intro x hx
  change x.1 ∈ LinearMap.range (C.differential q) at hx
  rcases hx with ⟨y, hy⟩
  apply Subtype.ext
  rw [h] at hy
  exact hy.symm

/-- If cycles are all elements and boundaries are zero, the native homology
quotient is linearly equivalent to the underlying module. -/
noncomputable def derivedEEquivOfCyclesEqTopBoundariesEqBot
    (q : I)
    (hCycles : C.targetCycles q = ⊤)
    (hBoundaries : C.targetBoundariesInCycles q = ⊥) :
    C.DerivedE q ≃ₗ[R] E (C.differentialDegree q) :=
  (Submodule.quotEquivOfEqBot
      (C.targetBoundariesInCycles q) hBoundaries).trans
    ((LinearEquiv.ofEq (C.targetCycles q) ⊤ hCycles).trans
      Submodule.topEquiv)

/-- One-step page stabilization at `q`: zero incoming and outgoing
differentials identify homology with the module in the target degree. -/
noncomputable def derivedEEquivOfAdjacentDifferentialsZero
    (q : I)
    (hIncoming : C.differential q = 0)
    (hOutgoing :
      C.differential (C.differentialDegree q) = 0) :
    C.DerivedE q ≃ₗ[R] E (C.differentialDegree q) :=
  C.derivedEEquivOfCyclesEqTopBoundariesEqBot q
    (C.targetCycles_eq_top_of_differential_eq_zero q hOutgoing)
    (C.targetBoundariesInCycles_eq_bot_of_differential_eq_zero q hIncoming)

/-- A directly usable stabilization criterion in terms of vanishing source
and target modules rather than pre-supplied zero-map equalities. -/
noncomputable def derivedEEquivOfAdjacentTermsZero
    (q : I)
    (hIncomingSource : ∀ x : E q, x = 0)
    (hOutgoingTarget :
      ∀ x : E
        (C.differentialDegree
          (C.differentialDegree q)), x = 0) :
    C.DerivedE q ≃ₗ[R] E (C.differentialDegree q) :=
  C.derivedEEquivOfAdjacentDifferentialsZero q
    (C.differential_eq_zero_of_domain_eq_zero q hIncomingSource)
    (C.differential_eq_zero_of_codomain_eq_zero
      (C.differentialDegree q) hOutgoingTarget)

/-- Stabilization in the indexing used by the derived exact couple's `E`
object. -/
noncomputable def directDerivedEEquivOfAdjacentDifferentialsZero
    (p : I)
    (hIncoming :
      C.differential (C.differentialDegree.symm p) = 0)
    (hOutgoing :
      C.differential
        (C.differentialDegree
          (C.differentialDegree.symm p)) = 0) :
    C.DirectDerivedE p ≃ₗ[R] E p :=
  (C.derivedEEquivOfAdjacentDifferentialsZero
      (C.differentialDegree.symm p) hIncoming hOutgoing).trans
    (LinearEquiv.cast
      (R := R) (M := E)
      (C.differentialDegree.apply_symm_apply p))

end GradedExactCouple

end InfoGeometry.Spectral.Algebra
