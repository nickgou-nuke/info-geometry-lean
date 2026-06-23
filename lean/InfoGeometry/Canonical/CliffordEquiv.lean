import Mathlib
import InfoGeometry.Algebra.PeirceLadderOperators
import InfoGeometry.Canonical.HestenesKreinModularGeometry
import InfoGeometry.Geometry.FiniteHestenesCR
import InfoGeometry.OperatorAlgebra.SplitOctonionSymplecticFoundation

open CliffordAlgebra
open QuadraticMap
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Canonical.HestenesKreinModularGeometry

noncomputable section

namespace InfoGeometry.Canonical.CliffordEquiv

/-! ## 1. Abstract Complex Structure and Induced Module -/

/-- Abstract complex structure: an ℝ-linear endomorphism S on V squaring to -Id. -/
structure AbstractComplexStructure (V : Type*) [AddCommGroup V] [Module ℝ V] where
  S : V →ₗ[ℝ] V
  S_sq : S.comp S = -LinearMap.id

/-- Induce a ℂ-module structure from an abstract complex structure. -/
def inducedComplexModule {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : AbstractComplexStructure V) : Module ℂ V where
  smul z v := (z.re : ℝ) • v + (z.im : ℝ) • C.S v
  one_smul := by
    intro v
    change (1 : ℂ).re • v + (1 : ℂ).im • C.S v = v
    simp
  mul_smul := by
    intro z w v
    change ((z * w).re : ℝ) • v + ((z * w).im : ℝ) • C.S v =
           (z.re : ℝ) • (w.re • v + w.im • C.S v) +
           (z.im : ℝ) • C.S (w.re • v + w.im • C.S v)
    have hS : ∀ x, C.S (C.S x) = -x := by
      intro x
      have hx := congrArg (fun (f : V →ₗ[ℝ] V) => f x) C.S_sq
      simpa using hx
    simp only [Complex.mul_re, Complex.mul_im, map_add, LinearMap.map_smul,
      smul_add, add_smul, sub_smul, hS, smul_neg, ← mul_smul]
    simp only [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  add_smul := by
    intro z w v
    change ((z + w).re : ℝ) • v + ((z + w).im : ℝ) • C.S v =
           ((z.re : ℝ) • v + z.im • C.S v) + ((w.re : ℝ) • v + w.im • C.S v)
    simp only [Complex.add_re, Complex.add_im, add_smul]
    simp only [add_assoc, add_left_comm]
  zero_smul := by
    intro v
    change (0 : ℂ).re • v + (0 : ℂ).im • C.S v = 0
    simp
  smul_add := by
    intro z v w
    change (z.re : ℝ) • (v + w) + (z.im : ℝ) • C.S (v + w) =
           ((z.re : ℝ) • v + z.im • C.S v) + ((z.re : ℝ) • w + z.im • C.S w)
    simp only [map_add, smul_add]
    simp only [add_assoc, add_left_comm]
  smul_zero := by
    intro z
    change (z.re : ℝ) • (0 : V) + (z.im : ℝ) • C.S 0 = 0
    simp

/-! ## 2. Explicit Clifford Complex Structures -/

/-- Quadratic form of signature (1, 1) over ℝ. -/
def q11_R : QuadraticForm ℝ (Fin 2 → ℝ) := proj 0 0 - proj 1 1

/-- Spacelike generator in Cl(1,1). -/
def e₁_R : CliffordAlgebra q11_R := ι q11_R (fun i => if i = 1 then 1 else 0)

theorem e₁_R_sq : e₁_R * e₁_R = -1 := by
  calc
    e₁_R * e₁_R = algebraMap ℝ (CliffordAlgebra q11_R)
                    (q11_R (fun i => if i = 1 then 1 else 0)) := ι_sq_scalar _ _
    _ = -1 := by simp [q11_R, proj_apply]

/-- Quadratic form of signature (2, 0) over ℝ. -/
def q20 : QuadraticForm ℝ (Fin 2 → ℝ) := proj 0 0 + proj 1 1

/-- First generator in Cl(2,0). -/
def cl20_e₁ : CliffordAlgebra q20 := ι q20 (fun i => if i = 0 then 1 else 0)

/-- Second generator in Cl(2,0). -/
def cl20_e₂ : CliffordAlgebra q20 := ι q20 (fun i => if i = 1 then 1 else 0)

theorem cl20_e₁_sq : cl20_e₁ * cl20_e₁ = 1 := by
  calc
    cl20_e₁ * cl20_e₁ = algebraMap ℝ (CliffordAlgebra q20)
                          (q20 (fun i => if i = 0 then 1 else 0)) := ι_sq_scalar _ _
    _ = 1 := by simp [q20, proj_apply]

theorem cl20_e₂_sq : cl20_e₂ * cl20_e₂ = 1 := by
  calc
    cl20_e₂ * cl20_e₂ = algebraMap ℝ (CliffordAlgebra q20)
                          (q20 (fun i => if i = 1 then 1 else 0)) := ι_sq_scalar _ _
    _ = 1 := by simp [q20, proj_apply]

theorem cl20_orth : q20.IsOrtho (fun i => if i = 0 then 1 else 0)
                                 (fun i => if i = 1 then 1 else 0) := by
  dsimp [q20, IsOrtho, proj_apply]
  ring

theorem cl20_anticomm : cl20_e₁ * cl20_e₂ + cl20_e₂ * cl20_e₁ = 0 := by
  have h := ι_mul_ι_add_swap_of_isOrtho cl20_orth
  simpa [cl20_e₁, cl20_e₂] using h

/-- Bivector e₁e₂ in Cl(2,0). -/
def cliffordBivector : CliffordAlgebra q20 := cl20_e₁ * cl20_e₂

theorem cliffordBivector_sq : cliffordBivector * cliffordBivector = -1 := by
  dsimp [cliffordBivector]
  have h_expand : cl20_e₁ * cl20_e₂ * (cl20_e₁ * cl20_e₂) =
                  - (cl20_e₁ * cl20_e₁ * (cl20_e₂ * cl20_e₂)) := by
    calc
      cl20_e₁ * cl20_e₂ * (cl20_e₁ * cl20_e₂)
        = cl20_e₁ * (cl20_e₁ * cl20_e₂ + cl20_e₂ * cl20_e₁) * cl20_e₂ -
          cl20_e₁ * cl20_e₁ * cl20_e₂ * cl20_e₂ := by noncomm_ring
      _ = cl20_e₁ * 0 * cl20_e₂ - cl20_e₁ * cl20_e₁ * cl20_e₂ * cl20_e₂ := by
        rw [cl20_anticomm]
      _ = - (cl20_e₁ * cl20_e₁ * (cl20_e₂ * cl20_e₂)) := by noncomm_ring
  rw [h_expand, cl20_e₁_sq, cl20_e₂_sq]
  simp

/-! ## 3. Functorial Lift from ℂ to Any ℝ-Algebra -/

/-- The linear map r ↦ r • S. -/
def HestenesLiftMap {A : Type*} [Ring A] [Algebra ℝ A] (S : A) : ℝ →ₗ[ℝ] A :=
  LinearMap.toSpanSingleton ℝ A S

theorem HestenesLiftMap_sq {A : Type*} [Ring A] [Algebra ℝ A] (S : A) (hS : S * S = -1) (r : ℝ) :
    HestenesLiftMap S r * HestenesLiftMap S r =
      algebraMap ℝ A (CliffordAlgebraComplex.Q r) := by
  dsimp [HestenesLiftMap, CliffordAlgebraComplex.Q]
  have h1 : (r • S) * (r • S) = (r * r) • (S * S) := by
    rw [smul_mul_smul]
  rw [h1, hS]
  simp [Algebra.algebraMap_eq_smul_one]

/-- Lift S² = -1 to an algebra map from CliffordAlgebra Q. -/
def hestenesLift {A : Type*} [Ring A] [Algebra ℝ A] (S : A) (hS : S * S = -1) :
    CliffordAlgebra CliffordAlgebraComplex.Q →ₐ[ℝ] A :=
  CliffordAlgebra.lift CliffordAlgebraComplex.Q ⟨HestenesLiftMap S, HestenesLiftMap_sq S hS⟩

/-- Lift S² = -1 to an algebra map from ℂ. -/
noncomputable def complexLift {A : Type*} [Ring A] [Algebra ℝ A] (S : A) (hS : S * S = -1) :
    ℂ →ₐ[ℝ] A :=
  (hestenesLift S hS).comp CliffordAlgebraComplex.equiv.symm.toAlgHom

theorem complexLift_I {A : Type*} [Ring A] [Algebra ℝ A] (S : A) (hS : S * S = -1) :
    complexLift S hS Complex.I = S := by
  dsimp [complexLift]
  rw [CliffordAlgebraComplex.ofComplex_I]
  unfold hestenesLift
  have h := lift_ι_apply (HestenesLiftMap S) (HestenesLiftMap_sq S hS) 1
  rw [h]
  dsimp [HestenesLiftMap]
  simp

/-- The range subalgebra generated by S. -/
noncomputable def complexSubalgebra {A : Type*} [Ring A] [Algebra ℝ A] (S : A) (hS : S * S = -1) :
    Subalgebra ℝ A :=
  (complexLift S hS).range

theorem mem_complexSubalgebra_iff {A : Type*} [Ring A] [Algebra ℝ A]
    (S : A) (hS : S * S = -1) (x : A) :
    x ∈ complexSubalgebra S hS ↔ ∃ (r s : ℝ), x = algebraMap ℝ A r + s • S := by
  constructor
  · rintro ⟨z, rfl⟩
    use z.re, z.im
    have h_eq : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    conv_lhs => rw [h_eq]
    simp only [map_add, map_mul]
    have h_re : (complexLift S hS) (z.re : ℂ) = algebraMap ℝ A z.re := by
      exact (complexLift S hS).commutes z.re
    have h_im : (complexLift S hS) (z.im : ℂ) = algebraMap ℝ A z.im := by
      exact (complexLift S hS).commutes (z.im)
    have h_I : (complexLift S hS) Complex.I = S := complexLift_I S hS
    change (complexLift S hS) (z.re : ℂ) +
           (complexLift S hS) (z.im : ℂ) *
           (complexLift S hS) Complex.I = _
    rw [h_re, h_im, h_I]
    rw [← Algebra.smul_def]
  · rintro ⟨r, s, rfl⟩
    use ⟨r, s⟩
    have h_eq : (⟨r, s⟩ : ℂ) = (r : ℂ) + (s : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    conv_lhs => rw [h_eq]
    simp only [map_add, map_mul]
    have h_re : (complexLift S hS) (r : ℂ) = algebraMap ℝ A r := by
      exact (complexLift S hS).commutes r
    have h_im : (complexLift S hS) (s : ℂ) = algebraMap ℝ A s := by
      exact (complexLift S hS).commutes s
    have h_I : (complexLift S hS) Complex.I = S := complexLift_I S hS
    change (complexLift S hS) (r : ℂ) +
           (complexLift S hS) (s : ℂ) *
           (complexLift S hS) Complex.I = _
    rw [h_re, h_im, h_I]
    rw [← Algebra.smul_def]

/-! ## 4. Color-ladder socket and Clifford bivector equivalence -/

/-- Peirce ladder complex J over ℤ. -/
def peirceJ : SplitOctonions.Multiplication.SplitOct := ⟨0, 0, 1, 0, 0, -1, 0, 0⟩

theorem peirceJ_sq :
    SplitOctonions.Multiplication.mulZ peirceJ peirceJ =
      SplitOctonions.Multiplication.negZ
        SplitOctonions.SymplecticFoundation.oneZ := by
  decide



theorem splitOctonion_foundation_packet :
    SplitOctonions.Multiplication.mulZ
        SplitOctonions.SymplecticFoundation.H
        SplitOctonions.SymplecticFoundation.H
      = SplitOctonions.SymplecticFoundation.oneZ ∧
    (∀ i : Fin 3,
      SplitOctonions.SymplecticFoundation.commZ
        (SplitOctonions.Multiplication.up i)
        (SplitOctonions.Multiplication.down i)
        = SplitOctonions.SymplecticFoundation.H) ∧
    (∀ i : Fin 3,
      SplitOctonions.SymplecticFoundation.antiCommZ
        (InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.up i)
        (InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.down i)
        = SplitOctonions.SymplecticFoundation.oneZ) :=
  ⟨SplitOctonions.SymplecticFoundation.H_sq,
   SplitOctonions.SymplecticFoundation.up_down_comm_eq_H,
   SplitOctonions.SymplecticFoundation.up_down_anticomm_eq_oneZ⟩

/-- Double Hestenes commutator theorem. -/
theorem hestenesCommutator_double_comm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : KreinHestenesModularDatum E)
    (h_sq : D.modularGenerator * D.modularGenerator = -1)
    (A : E →L[ℝ] E) :
    KreinHestenesModularDatum.hestenesCommutator D.modularGenerator
      (KreinHestenesModularDatum.hestenesCommutator D.modularGenerator A) =
      -2 • A - 2 • (D.modularGenerator * A * D.modularGenerator) := by
  dsimp [KreinHestenesModularDatum.hestenesCommutator]
  have h_expand :
    D.modularGenerator * (D.modularGenerator * A - A * D.modularGenerator) -
    (D.modularGenerator * A - A * D.modularGenerator) * D.modularGenerator =
    (D.modularGenerator * D.modularGenerator) * A -
    2 • (D.modularGenerator * A * D.modularGenerator) +
    A * (D.modularGenerator * D.modularGenerator) := by
    noncomm_ring
  rw [h_expand]
  rw [h_sq]
  noncomm_ring

/-! ## 5. Main Linear Equivalence and Inductive Independent Proofs -/

theorem S_linear_independent {A : Type*} [Ring A] [Algebra ℝ A] [Nontrivial A]
    (S : A) (hS : S * S = -1) (r s : ℝ) (h : algebraMap ℝ A r + s • S = 0) :
    r = 0 ∧ s = 0 := by
  have h_eq : algebraMap ℝ A r = - (s • S) := by
    exact eq_neg_of_add_eq_zero_left h
  have h_sq : (algebraMap ℝ A r) * (algebraMap ℝ A r) = (- (s • S)) * (- (s • S)) := by
    rw [h_eq]
  simp only [← map_mul] at h_sq
  have h_rhs : (- (s • S)) * (- (s • S)) = algebraMap ℝ A (- (s * s)) := by
    calc
      (- (s • S)) * (- (s • S)) = (s • S) * (s • S) := by rw [neg_mul_neg]
      _ = (s * s) • (S * S) := by rw [smul_mul_smul]
      _ = (s * s) • (-1) := by rw [hS]
      _ = algebraMap ℝ A (- (s * s)) := by
        simp [Algebra.algebraMap_eq_smul_one]
  rw [h_rhs] at h_sq
  have h_inj : r * r = - (s * s) := by
    exact (algebraMap ℝ A).injective h_sq
  have h_sum : r * r + s * s = 0 := by
    linarith
  have h_r_sq : r * r = 0 := by
    have h_r2 : 0 ≤ r * r := mul_self_nonneg r
    have h_s2 : 0 ≤ s * s := mul_self_nonneg s
    linarith
  have h_s_sq : s * s = 0 := by
    have h_r2 : 0 ≤ r * r := mul_self_nonneg r
    have h_s2 : 0 ≤ s * s := mul_self_nonneg s
    linarith
  exact ⟨mul_self_eq_zero.mp h_r_sq, mul_self_eq_zero.mp h_s_sq⟩

noncomputable def complexLiftRange {A : Type*} [Ring A] [Algebra ℝ A] [Nontrivial A]
    (S : A) (hS : S * S = -1) : ℂ →ₗ[ℝ] complexSubalgebra S hS where
  toFun z := ⟨complexLift S hS z, ⟨z, rfl⟩⟩
  map_add' z1 z2 := by ext; simp
  map_smul' r z := by
    ext
    dsimp
    exact (complexLift S hS).toLinearMap.map_smul r z

noncomputable def complexLiftEquiv {A : Type*} [Ring A] [Algebra ℝ A] [Nontrivial A]
    (S : A) (hS : S * S = -1) : ℂ ≃ₗ[ℝ] complexSubalgebra S hS :=
  LinearEquiv.ofBijective (complexLiftRange S hS) ⟨by
    intro z1 z2 h
    simp [complexLiftRange] at h
    have h_eq : complexLift S hS (z1 - z2) = 0 := by
      simp [map_sub, h]
    have h_inj : (z1 - z2).re = 0 ∧ (z1 - z2).im = 0 := by
      have h_eq2 : complexLift S hS (z1 - z2) =
                   algebraMap ℝ A (z1 - z2).re + (z1 - z2).im • S := by
        have h_z : z1 - z2 = ((z1 - z2).re : ℂ) + ((z1 - z2).im : ℂ) * Complex.I := by
          apply Complex.ext <;> simp
        conv_lhs => rw [h_z]
        simp only [map_add, map_mul]
        have h_re : (complexLift S hS) ((z1 - z2).re : ℂ) = algebraMap ℝ A (z1 - z2).re := by
          exact (complexLift S hS).commutes (z1 - z2).re
        have h_im : (complexLift S hS) ((z1 - z2).im : ℂ) = algebraMap ℝ A (z1 - z2).im := by
          exact (complexLift S hS).commutes (z1 - z2).im
        have h_I : (complexLift S hS) Complex.I = S := complexLift_I S hS
        change (complexLift S hS) ((z1 - z2).re : ℂ) +
               (complexLift S hS) ((z1 - z2).im : ℂ) *
               (complexLift S hS) Complex.I = _
        rw [h_re, h_im, h_I]
        rw [← Algebra.smul_def]
      rw [h_eq2] at h_eq
      exact S_linear_independent S hS (z1 - z2).re (z1 - z2).im h_eq
    have h_z1_z2 : z1 - z2 = 0 := by
      apply Complex.ext <;> simp [h_inj]
    exact sub_eq_zero.mp h_z1_z2, by
    intro ⟨x, ⟨z, hz⟩⟩
    use z
    ext
    dsimp [complexLiftRange]
    exact hz⟩

/-- Peirce-Clifford equivalence: both subalgebras are isomorphic to ℂ,
    so they are isomorphic to each other. -/
theorem peirceCliffordEquivalence :
    Nonempty (complexSubalgebra e₁_R e₁_R_sq ≃ₗ[ℝ]
              complexSubalgebra cliffordBivector cliffordBivector_sq) := by
  have h1 : Nonempty (complexSubalgebra e₁_R e₁_R_sq ≃ₗ[ℝ] ℂ) :=
    ⟨(complexLiftEquiv e₁_R e₁_R_sq).symm⟩
  have h2 : Nonempty (ℂ ≃ₗ[ℝ] complexSubalgebra
                      cliffordBivector cliffordBivector_sq) :=
    ⟨complexLiftEquiv cliffordBivector cliffordBivector_sq⟩
  rcases h1 with ⟨e1⟩
  rcases h2 with ⟨e2⟩
  exact ⟨e1.trans e2⟩

/-- The Peirce-ladder complex structure is definitionally the `Cl(1,1)` generator `e₁`. -/
theorem peirceLadder_J_eq_cl11_generator :
    InfoGeometry.Algebra.PeirceLadder.J = InfoGeometry.Algebra.Cl11Fermions.e₁ := by
  rfl

/-- The Peirce-ladder complex structure satisfies the same square-minus-one law. -/
theorem peirceLadder_J_sq_neg_one :
    InfoGeometry.Algebra.PeirceLadder.J * InfoGeometry.Algebra.PeirceLadder.J = -1 := by
  simpa [InfoGeometry.Algebra.PeirceLadder.J] using
    InfoGeometry.Algebra.Cl11Fermions.e₁_sq

/--
Finite bridge packet for the internal complex structures currently realized in-repo.

This is the honest closure surface presently available:
* the Furey/Peirce ladder complex structure is exactly the `Cl(1,1)` generator `e₁`;
* that generator squares to `-1`;
* the Mathlib `Cl(2,0)` bivector squares to `-1`;
* the corresponding `ℂ`-generated real subalgebras are linearly equivalent;
* the finite Hestenes spinor proxy has a bivector `e₁₂` with the same square law.

It does not claim a full global representation identification between all these carriers.
-/
theorem finite_complex_structure_bridge_packet :
    InfoGeometry.Algebra.PeirceLadder.J = InfoGeometry.Algebra.Cl11Fermions.e₁ ∧
    InfoGeometry.Algebra.PeirceLadder.J * InfoGeometry.Algebra.PeirceLadder.J = -1 ∧
    cliffordBivector * cliffordBivector = -1 ∧
    Nonempty (complexSubalgebra e₁_R e₁_R_sq ≃ₗ[ℝ]
      complexSubalgebra cliffordBivector cliffordBivector_sq) ∧
    InfoGeometry.Geometry.FiniteHestenesCR.bivector_i *
        InfoGeometry.Geometry.FiniteHestenesCR.bivector_i = ⟨-1, 0, 0, 0⟩ := by
  exact ⟨peirceLadder_J_eq_cl11_generator, peirceLadder_J_sq_neg_one,
    cliffordBivector_sq, peirceCliffordEquivalence,
    InfoGeometry.Geometry.FiniteHestenesCR.bivector_i_squared⟩

end InfoGeometry.Canonical.CliffordEquiv
