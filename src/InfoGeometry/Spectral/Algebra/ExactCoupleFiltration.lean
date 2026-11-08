import InfoGeometry.Spectral.Algebra.GenericDerivedCouple
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The image filtration of a graded exact couple

The classical filtration attached to an exact couple is formed by the images
of successive incoming `i` maps.  This file constructs that filtration
directly from linear maps and defines its associated graded quotients using
Mathlib submodules.
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

/-- The source index reached after moving `n` times against the degree of
`i`. -/
def backwardIIndex (iDeg : I ≃ I) : ℕ → I → I
  | 0, p => p
  | n + 1, p => iDeg.symm (backwardIIndex iDeg n p)

@[simp]
theorem backwardIIndex_zero (iDeg : I ≃ I) (p : I) :
    backwardIIndex iDeg 0 p = p :=
  rfl

@[simp]
theorem backwardIIndex_succ (iDeg : I ≃ I) (n : ℕ) (p : I) :
    backwardIIndex iDeg (n + 1) p =
      iDeg.symm (backwardIIndex iDeg n p) :=
  rfl

/-- The composite of `n` incoming `i` maps ending in `D p`. -/
noncomputable def incomingIIterate
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) :
    ∀ n p, D (backwardIIndex iDeg n p) →ₗ[R] D p
  | 0, _ => LinearMap.id
  | n + 1, p =>
      (incomingIIterate C n p).comp
        (C.incomingI (backwardIIndex iDeg n p))

@[simp]
theorem incomingIIterate_zero
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    C.incomingIIterate 0 p = LinearMap.id :=
  rfl

@[simp]
theorem incomingIIterate_succ_apply
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (n : ℕ) (p : I)
    (x : D (backwardIIndex iDeg (n + 1) p)) :
    C.incomingIIterate (n + 1) p x =
      C.incomingIIterate n p
        (C.incomingI (backwardIIndex iDeg n p) x) :=
  rfl

/-- The `n`th image filtration term in `D p`. -/
noncomputable abbrev imageFiltration
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (n : ℕ) (p : I) : Submodule R (D p) :=
  LinearMap.range (C.incomingIIterate n p)

@[simp]
theorem imageFiltration_zero
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    C.imageFiltration 0 p = ⊤ :=
  LinearMap.range_id

/-- At a target of `i`, the first image-filtration term is exactly the kernel
of the outgoing `j` map. -/
theorem ker_j_iDeg_eq_imageFiltration_one
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    LinearMap.ker (C.j (iDeg p)) =
      C.imageFiltration 1 (iDeg p) := by
  rw [C.exact_ij p]
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact C.incomingI_iDeg_mem p x
  · rintro _ ⟨y, rfl⟩
    let h : iDeg.symm (iDeg p) = p := iDeg.symm_apply_apply p
    let x : D p :=
      LinearEquiv.cast (R := R) (M := D) h y
    refine ⟨x, ?_⟩
    change
      C.i p x =
        LinearEquiv.cast
          (R := R) (M := D)
          (iDeg.apply_symm_apply (iDeg p))
          (C.i (iDeg.symm (iDeg p)) y)
    have hi := C.i_cast_apply h y
    simpa [x] using hi.symm

/-- Successive image-filtration terms form a descending chain. -/
theorem imageFiltration_succ_le
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (n : ℕ) (p : I) :
    C.imageFiltration (n + 1) p ≤ C.imageFiltration n p := by
  rintro x ⟨y, rfl⟩
  exact
    ⟨C.incomingI (backwardIIndex iDeg n p) y, rfl⟩

/-- The `(n+1)`st filtration term regarded as a submodule of the `n`th term. -/
noncomputable abbrev imageFiltrationStep
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (n : ℕ) (p : I) :
    Submodule R (C.imageFiltration n p) :=
  (C.imageFiltration (n + 1) p).comap
    (C.imageFiltration n p).subtype

/-- The genuine associated-graded quotient `Fₙ D(p) / Fₙ₊₁ D(p)`. -/
noncomputable abbrev associatedGraded
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (n : ℕ) (p : I) :=
  (C.imageFiltration n p) ⧸ C.imageFiltrationStep n p

/-- The canonical projection from a filtration term to its associated-graded
quotient. -/
noncomputable def toAssociatedGraded
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (n : ℕ) (p : I) :
    C.imageFiltration n p →ₗ[R] C.associatedGraded n p :=
  Submodule.mkQ (C.imageFiltrationStep n p)

/-- The kernel of the canonical associated-graded projection is exactly the
next filtration step. -/
theorem ker_toAssociatedGraded
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (n : ℕ) (p : I) :
    LinearMap.ker (C.toAssociatedGraded n p) =
      C.imageFiltrationStep n p := by
  change
    LinearMap.ker (Submodule.mkQ (C.imageFiltrationStep n p)) =
      C.imageFiltrationStep n p
  exact Submodule.ker_mkQ (C.imageFiltrationStep n p)

/-- The `j` map restricted to the zeroth filtration term. -/
noncomputable def filtrationJ
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    C.imageFiltration 0 (iDeg p) →ₗ[R] E (jDeg (iDeg p)) :=
  (C.j (iDeg p)).comp
    (C.imageFiltration 0 (iDeg p)).subtype

/-- If the following `k` map vanishes, exactness makes the restricted `j` map
surjective. -/
theorem filtrationJ_surjective_of_k_eq_zero
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I)
    (hk : C.k (jDeg (iDeg p)) = 0) :
    Function.Surjective (C.filtrationJ p) := by
  have hjRange :
      LinearMap.range (C.j (iDeg p)) = ⊤ := by
    rw [← C.exact_jk (iDeg p), hk, LinearMap.ker_zero]
  have hjSurjective :
      Function.Surjective (C.j (iDeg p)) :=
    LinearMap.range_eq_top.mp hjRange
  intro y
  obtain ⟨x, hx⟩ := hjSurjective y
  refine ⟨⟨x, ?_⟩, ?_⟩
  · rw [C.imageFiltration_zero]
    exact Submodule.mem_top
  · exact hx

/-- The kernel of the restricted `j` map is the first filtration step. -/
theorem ker_filtrationJ
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I) :
    LinearMap.ker (C.filtrationJ p) =
      C.imageFiltrationStep 0 (iDeg p) := by
  ext x
  change
    C.j (iDeg p) x.1 = 0 ↔
      x.1 ∈ C.imageFiltration 1 (iDeg p)
  rw [← LinearMap.mem_ker, C.ker_j_iDeg_eq_imageFiltration_one p]

/-- At a stage where the following `k` map is zero, the associated graded
quotient is canonically linearly equivalent to the corresponding `E` term. -/
noncomputable def associatedGradedZeroEquivEOfKZero
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I)
    (hk : C.k (jDeg (iDeg p)) = 0) :
    C.associatedGraded 0 (iDeg p) ≃ₗ[R]
      E (jDeg (iDeg p)) :=
  let f := C.filtrationJ p
  let hker :
      LinearMap.ker f =
        C.imageFiltrationStep 0 (iDeg p) :=
    C.ker_filtrationJ p
  let hsurj : Function.Surjective f :=
    C.filtrationJ_surjective_of_k_eq_zero p hk
  ((C.imageFiltrationStep 0 (iDeg p)).quotEquivOfEq
      (LinearMap.ker f) hker.symm).trans
    (f.quotKerEquivRange.trans
      ((LinearEquiv.ofEq
          (LinearMap.range f)
          ⊤
          (LinearMap.range_eq_top.mpr hsurj)).trans
        Submodule.topEquiv))

end GradedExactCouple

end InfoGeometry.Spectral.Algebra
