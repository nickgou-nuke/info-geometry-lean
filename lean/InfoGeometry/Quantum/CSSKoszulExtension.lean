/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Coupled three-generator Koszul complexes

This module formalizes the algebraic complex in Construction 2 of Hao Song,
arXiv:2608.09913v2, equations (160)--(166). The degree-two basis is ordered
cyclically as `(e₂ ∧ e₃, e₃ ∧ e₁, e₁ ∧ e₂)`. The coefficient ring is
commutative, as is the paper's lattice translation group ring.

The off-diagonal coupling is retained in the maps and in the native Mathlib
short complex. Changing it by `B *ᵥ f` gives an explicit unipotent chain
isomorphism. Exactness of the coupled complex is proved from exactness of the
two adjacent Koszul maps; regular-sequence exactness, physical Clifford
circuits, and superselection rigidity are not asserted here.
-/

namespace InfoGeometry.Quantum.CSSKoszulExtension

open CategoryTheory Matrix

universe u

abbrev Vec3 (R : Type u) := Fin 3 → R

variable {R : Type u} [CommRing R]

/-- The length-three Koszul middle differential in the cyclic wedge basis. -/
def koszulMatrix (f : Vec3 R) : Matrix (Fin 3) (Fin 3) R :=
  !![0, f 2, -f 1; -f 2, 0, f 0; f 1, -f 0, 0]

/-- The middle Koszul operator associated with the first coordinate vector. -/
def firstKoszulOperator : Matrix (Fin 3) (Fin 3) R := koszulMatrix ![1, 0, 0]

/-- The middle Koszul operator associated with the second coordinate vector. -/
def secondKoszulOperator : Matrix (Fin 3) (Fin 3) R := koszulMatrix ![0, 1, 0]

/-- Two middle Koszul operators fail to commute, even in characteristic two. -/
theorem firstKoszulOperator_mul_second_ne_reverse [Nontrivial R] :
    (firstKoszulOperator : Matrix (Fin 3) (Fin 3) R) * secondKoszulOperator ≠
      secondKoszulOperator * firstKoszulOperator := by
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 0 1) h
  simp [firstKoszulOperator, secondKoszulOperator, koszulMatrix,
    Matrix.mul_apply, Fin.sum_univ_three] at hentry

/-- The first Koszul differential. -/
def boundary1 (f : Vec3 R) : Vec3 R →ₗ[R] R := dotProductBilin R R f

/-- The second Koszul differential. -/
def boundary2 (f : Vec3 R) : Vec3 R →ₗ[R] Vec3 R :=
  (koszulMatrix f).mulVecLin

/-- The third Koszul differential. -/
def boundary3 (f : Vec3 R) : R →ₗ[R] Vec3 R :=
  LinearMap.toSpanSingleton R (Vec3 R) f

@[simp] theorem boundary1_apply (f x : Vec3 R) : boundary1 f x = f ⬝ᵥ x := rfl

@[simp] theorem boundary2_apply (f x : Vec3 R) :
    boundary2 f x = koszulMatrix f *ᵥ x := rfl

@[simp] theorem boundary3_apply (f : Vec3 R) (t : R) : boundary3 f t = t • f := rfl

@[simp] theorem boundary1_boundary2 (f x : Vec3 R) :
    boundary1 f (boundary2 f x) = 0 := by
  simp [boundary1, boundary2, koszulMatrix, dotProduct,
    Fin.sum_univ_three]
  ring

@[simp] theorem boundary2_boundary3 (f : Vec3 R) (t : R) :
    boundary2 f (boundary3 f t) = 0 := by
  ext i
  fin_cases i <;>
    simp [boundary2, boundary3, koszulMatrix, dotProduct,
      Fin.sum_univ_three] <;> ring

/-- The coupling compatibility which makes the off-diagonal square vanish. -/
theorem boundary1_boundary3_swap (f a : Vec3 R) (t : R) :
    boundary1 f (boundary3 a t) = boundary1 a (boundary3 f t) := by
  simp only [boundary3_apply, map_smul]
  rw [boundary1_apply, boundary1_apply, dotProduct_comm]

/-- The incoming map `K₂ ⊕ K₃ → K₁ ⊕ K₂` retains the coupling vector. -/
def incoming (f a : Vec3 R) : (Vec3 R × R) →ₗ[R] (Vec3 R × Vec3 R) :=
  ((boundary2 f).coprod (boundary3 a)).prod
    ((0 : Vec3 R →ₗ[R] Vec3 R).coprod (boundary3 f))

/-- The outgoing map `K₁ ⊕ K₂ → K₀ ⊕ K₁` of the coupled complex. -/
def outgoing (f a : Vec3 R) : (Vec3 R × Vec3 R) →ₗ[R] (R × Vec3 R) :=
  ((boundary1 f).coprod (-boundary1 a)).prod
    ((0 : Vec3 R →ₗ[R] Vec3 R).coprod (boundary2 f))

@[simp] theorem incoming_apply (f a : Vec3 R) (x : Vec3 R × R) :
    incoming f a x = (boundary2 f x.1 + x.2 • a, x.2 • f) := by
  simp [incoming, boundary3]

@[simp] theorem outgoing_apply (f a : Vec3 R) (x : Vec3 R × Vec3 R) :
    outgoing f a x = (boundary1 f x.1 - boundary1 a x.2, boundary2 f x.2) := by
  simp [outgoing, sub_eq_add_neg]

/-- Equation (163): the coupled maps compose to zero for every coupling. -/
theorem outgoing_comp_incoming (f a : Vec3 R) :
    (outgoing f a).comp (incoming f a) = 0 := by
  apply LinearMap.ext
  intro x
  change outgoing f a (incoming f a x) = 0
  rw [incoming_apply, outgoing_apply]
  apply Prod.ext
  · change boundary1 f (boundary2 f x.1 + x.2 • a) - boundary1 a (x.2 • f) = 0
    rw [map_add, boundary1_boundary2, zero_add]
    exact sub_eq_zero.mpr (boundary1_boundary3_swap f a x.2)
  · exact boundary2_boundary3 f x.2

/-- The actual Mathlib short complex, not just a square-zero assertion. -/
def complex (f a : Vec3 R) : ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk (incoming f a) (outgoing f a) (outgoing_comp_incoming f a)

/-- Native homology is the quotient of cycles by the coupled boundaries. -/
noncomputable def homologyQuotientIso (f a : Vec3 R) :
    (complex f a).homology ≅
      ModuleCat.of R
        ((outgoing f a).ker ⧸ (complex f a).moduleCatToCycles.range) :=
  (complex f a).moduleCatHomologyIso

/-- Exact adjacent Koszul maps imply exactness of the coupled complex.
The hypotheses describe the uncoupled Koszul sequence, not the conclusion. -/
theorem complex_exact_of_koszul_exact (f a : Vec3 R)
    (h12 : Function.Exact (boundary2 f) (boundary1 f))
    (h23 : Function.Exact (boundary3 f) (boundary2 f)) :
    (complex f a).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  rintro ⟨x, y⟩ hxy
  change outgoing f a (x, y) = 0 at hxy
  rw [outgoing_apply] at hxy
  have hy : boundary2 f y = 0 := congrArg Prod.snd hxy
  obtain ⟨t, ht⟩ := (h23 y).mp hy
  have hx : boundary1 f (x - t • a) = 0 := by
    have hfirst : boundary1 f x - boundary1 a y = 0 := congrArg Prod.fst hxy
    rw [← ht] at hfirst
    simpa only [map_sub, ← boundary3_apply,
      boundary1_boundary3_swap f a t] using hfirst
  obtain ⟨u, hu⟩ := (h12 (x - t • a)).mp hx
  refine ⟨(u, t), ?_⟩
  change incoming f a (u, t) = (x, y)
  rw [incoming_apply, hu]
  exact Prod.ext (sub_add_cancel x (t • a)) ht

/-- An upper triangular change of coordinates, assembled from native
`LinearEquiv.skewProd` and the two product swaps. -/
def upperShear {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (b : N →ₗ[R] M) : (M × N) ≃ₗ[R] (M × N) :=
  (LinearEquiv.prodComm R M N).trans
    (((LinearEquiv.refl R N).skewProd (LinearEquiv.refl R M) b).trans
      (LinearEquiv.prodComm R N M))

@[simp] theorem upperShear_apply {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (b : N →ₗ[R] M) (x : M × N) :
    upperShear b x = (x.1 + b x.2, x.2) := rfl

@[simp] theorem upperShear_symm_apply {M N : Type u}
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (b : N →ₗ[R] M) (x : M × N) :
    (upperShear b).symm x = (x.1 - b x.2, x.2) := rfl

/-- The endpoint row needed to compensate for the antisymmetric part of `B`. -/
def endpointVector (B : Matrix (Fin 3) (Fin 3) R) : Vec3 R :=
  ![B 2 1 - B 1 2, B 0 2 - B 2 0, B 1 0 - B 0 1]

/-- The coefficient-valued contraction of the antisymmetric part of `B`.
Matrix-vector multiplication is performed before taking this scalar pairing. -/
private theorem endpoint_dotProduct_identity (f y : Vec3 R)
    (B : Matrix (Fin 3) (Fin 3) R) :
    dotProduct f (B *ᵥ y) - dotProduct (B *ᵥ f) y =
      dotProduct (endpointVector B) (koszulMatrix f *ᵥ y) := by
  simp [endpointVector, koszulMatrix, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three]
  ring

/-- The chain-map compatibility identity behind an ideal-valued change of coupling. -/
theorem endpoint_identity (f y : Vec3 R) (B : Matrix (Fin 3) (Fin 3) R) :
    boundary1 f (B *ᵥ y) - boundary1 (B *ᵥ f) y =
      boundary1 (endpointVector B) (boundary2 f y) := by
  exact endpoint_dotProduct_identity f y B

/-- The six-coordinate unipotent change of physical presentation. -/
def middleEquiv (B : Matrix (Fin 3) (Fin 3) R) :
    (Vec3 R × Vec3 R) ≃ₗ[R] (Vec3 R × Vec3 R) :=
  upperShear B.mulVecLin

/-- The four-coordinate unipotent change at the outgoing endpoint. -/
def endpointEquiv (B : Matrix (Fin 3) (Fin 3) R) :
    (R × Vec3 R) ≃ₗ[R] (R × Vec3 R) :=
  upperShear (boundary1 (endpointVector B))

@[simp] theorem middleEquiv_apply (B : Matrix (Fin 3) (Fin 3) R)
    (x : Vec3 R × Vec3 R) : middleEquiv B x = (x.1 + B *ᵥ x.2, x.2) := rfl

@[simp] theorem endpointEquiv_apply (B : Matrix (Fin 3) (Fin 3) R)
    (x : R × Vec3 R) :
    endpointEquiv B x = (x.1 + boundary1 (endpointVector B) x.2, x.2) := rfl

theorem middle_incoming (f a : Vec3 R) (B : Matrix (Fin 3) (Fin 3) R)
    (x : Vec3 R × R) :
    middleEquiv B (incoming f a x) = incoming f (a + B *ᵥ f) x := by
  simp [smul_add, Matrix.mulVec_smul, add_assoc]

theorem outgoing_middle (f a : Vec3 R) (B : Matrix (Fin 3) (Fin 3) R)
    (x : Vec3 R × Vec3 R) :
    outgoing f (a + B *ᵥ f) (middleEquiv B x) = endpointEquiv B (outgoing f a x) := by
  apply Prod.ext
  · simp only [outgoing_apply, middleEquiv_apply, endpointEquiv_apply, map_add,
      boundary1_apply, add_dotProduct]
    have h := endpoint_identity f x.2 B
    simp only [boundary1_apply] at h
    rw [← h]
    ring
  · rfl

/-- Equation (166), at the level of actual complexes: changing the coupling
by `B f` is an explicit chain isomorphism. No regularity is required. -/
def couplingIso (f a : Vec3 R) (B : Matrix (Fin 3) (Fin 3) R) :
    complex f a ≅ complex f (a + B *ᵥ f) :=
  ShortComplex.isoMk (Iso.refl _)
    (middleEquiv B).toModuleIso (endpointEquiv B).toModuleIso
    (by
      apply ModuleCat.hom_ext
      ext x
      exact (middle_incoming f a B x).symm)
    (by
      apply ModuleCat.hom_ext
      ext x
      exact outgoing_middle f a B x)

/-- The explicit change of presentation induces an isomorphism on native
homology, including the off-diagonal coupling. -/
noncomputable def couplingHomologyIso (f a : Vec3 R) (B : Matrix (Fin 3) (Fin 3) R) :
    (complex f a).homology ≅ (complex f (a + B *ᵥ f)).homology :=
  ShortComplex.homologyMapIso (couplingIso f a B)

/-- Membership of each coupling difference in the Koszul ideal is exactly
the condition needed to express the difference as `B *ᵥ f`. -/
theorem exists_matrix_of_coupling_sub_mem_span (f a a' : Vec3 R)
    (h : ∀ i, a' i - a i ∈ Ideal.span (Set.range f)) :
    ∃ B : Matrix (Fin 3) (Fin 3) R, a' = a + B *ᵥ f := by
  classical
  have hex : ∀ i, ∃ c : Fin 3 → R, ∑ j, c j • f j = a' i - a i :=
    fun i => (Submodule.mem_span_range_iff_exists_fun R).mp (h i)
  choose B hB using hex
  refine ⟨B, ?_⟩
  ext i
  have hi := hB i
  simpa only [Pi.add_apply, Matrix.mulVec, dotProduct, smul_eq_mul] using
    (eq_add_of_sub_eq' hi.symm)

/-- Couplings with the same residue modulo the Koszul ideal give isomorphic
short complexes. This is an algebraic presentation result, not a circuit
classification theorem. -/
theorem nonempty_iso_of_coupling_sub_mem_span (f a a' : Vec3 R)
    (h : ∀ i, a' i - a i ∈ Ideal.span (Set.range f)) :
    Nonempty (complex f a ≅ complex f a') := by
  obtain ⟨B, rfl⟩ := exists_matrix_of_coupling_sub_mem_span f a a' h
  exact ⟨couplingIso f a B⟩

end InfoGeometry.Quantum.CSSKoszulExtension
