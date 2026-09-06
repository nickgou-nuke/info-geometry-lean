import InfoGeometry.Spectral.Cohomology.deRham

/-!
# Mayer-Vietoris Bridge for de Rham Cohomology

This module is a compatibility layer over
`InfoGeometry.Spectral.Cohomology.deRham` for the de Rham Mayer-Vietoris
abstractions used in downstream files.
-/

noncomputable section

namespace InfoGeometry.Spectral.Cohomology.MayerVietoris

open InfoGeometry.Spectral.Cohomology.deRham
open InfoGeometry.Spectral.Cohomology.Basic

-- Re-export the existing abstract deRham data.

def criticalStrip : Set ℂ := {s : ℂ | 0 < s.re ∧ s.re < 1}

abbrev MayerVietorisCover (M : Type*) [TopologicalSpace M] [SmoothManifold M] :=
  deRham.MayerVietorisCover M

abbrev MayerVietorisSequence (M : Type*) [TopologicalSpace M]
    (V : Type*) [AddCommGroup V] [Module ℝ V] [SmoothManifold M] (cover : deRham.MayerVietorisCover M) :=
  deRham.MayerVietorisSequence M V cover

namespace MayerVietorisCover

variable {M : Type*} [TopologicalSpace M] [SmoothManifold M]

/-- The inclusion maps for the Mayer-Vietoris sequence on a cover. -/
def inclU_AB (c : deRham.MayerVietorisCover M) : c.intersection → c.Uset := by
  intro x
  exact ⟨x.1, x.2.1⟩

def inclV_AB (c : deRham.MayerVietorisCover M) : c.intersection → c.Vset := by
  intro x
  exact ⟨x.1, x.2.2⟩

def inclU_X (c : deRham.MayerVietorisCover M) : c.Uset → M := fun x => x

def inclV_X (c : deRham.MayerVietorisCover M) : c.Vset → M := fun x => x

-- The Mayer-Vietoris exact sequence for a de Rham owner on a cover.
noncomputable def MV_exact_sequence
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (c : deRham.MayerVietorisCover M)
    (S : deRham.MayerVietorisSequence M V c) :
    letI : SmoothManifold c.intersection := S.smooth_intersection
    letI : SmoothManifold c.Uset := S.smooth_U
    letI : SmoothManifold c.Vset := S.smooth_V
    letI : DifferentialForms c.intersection V := S.forms_intersection
    letI : DifferentialForms c.Uset V := S.forms_U
    letI : DifferentialForms c.Vset V := S.forms_V
    letI : DifferentialForms M V := S.forms_M
    letI : AddCommGroup
      (deRham.deRhamComplex.deRhamCohomology S.CU 0 ⊕
        deRham.deRhamComplex.deRhamCohomology S.CV 0) := S.middleAddCommGroup
    ExactSequence
      (deRham.deRhamComplex.deRhamCohomology S.CUV 0)
      (deRham.deRhamComplex.deRhamCohomology S.CU 0 ⊕
        deRham.deRhamComplex.deRhamCohomology S.CV 0)
      (deRham.deRhamComplex.deRhamCohomology S.CM 0) :=
  by
    exact S.sequence

/-- A reusable constructor for the sequence object above. -/
def MVSequence
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (c : deRham.MayerVietorisCover M)
    (S : deRham.MayerVietorisSequence M V c) :
    letI : SmoothManifold c.intersection := S.smooth_intersection
    letI : SmoothManifold c.Uset := S.smooth_U
    letI : SmoothManifold c.Vset := S.smooth_V
    letI : DifferentialForms c.intersection V := S.forms_intersection
    letI : DifferentialForms c.Uset V := S.forms_U
    letI : DifferentialForms c.Vset V := S.forms_V
    letI : DifferentialForms M V := S.forms_M
    letI : AddCommGroup
      (deRham.deRhamComplex.deRhamCohomology S.CU 0 ⊕
        deRham.deRhamComplex.deRhamCohomology S.CV 0) := S.middleAddCommGroup
    ExactSequence
      (deRham.deRhamComplex.deRhamCohomology S.CUV 0)
      (deRham.deRhamComplex.deRhamCohomology S.CU 0 ⊕
        deRham.deRhamComplex.deRhamCohomology S.CV 0)
      (deRham.deRhamComplex.deRhamCohomology S.CM 0) :=
  by
    exact S.sequence

end MayerVietorisCover

/-- The Locality Principle for de Rham cohomology on the critical strip -/
abbrev LocalityPrinciple (V : Type*) [AddCommGroup V] [Module ℝ V]
    [SmoothManifold ℂ] [DifferentialForms ℂ V] (C : deRhamComplex ℂ V) :=
  deRham.LocalityPrinciple V C

/-- Canonical extraction theorem for locality data. -/
def localToGlobal
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    [SmoothManifold ℂ] [DifferentialForms ℂ V]
    {C : deRhamComplex ℂ V}
    (P : deRham.LocalityPrinciple V C)
    (s : {s : ℂ | 0 < s.re ∧ s.re < 1}) :
    ∃ (U : Set ℂ), IsOpen U ∧ (s : ℂ) ∈ U ∧
      ∃ (_smoothU : SmoothManifold U),
      ∃ (_formsU : DifferentialForms U V),
      ∃ (CU : deRhamComplex U V),
        ∀ k, Nonempty (deRham.deRhamComplex.deRhamCohomology C k ≃+
          deRham.deRhamComplex.deRhamCohomology CU k) := by
  -- Locality is available natively with `s ∈ criticalStrip`; reorder to match.
  simpa [criticalStrip, and_left_comm, and_assoc] using (deRham.localToGlobal (V := V) P s)

end InfoGeometry.Spectral.Cohomology.MayerVietoris
