import InfoGeometry.Algebra.FourthRootPeirceProjectors
import InfoGeometry.Canonical.ExteriorSpinorChiralityBridge
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# The actual degree-mod-four operator on a native exterior algebra

The exterior algebra is functorial for v -> i*v. This produces degree phase
`i^k` on its kth exterior power, and its square is the EXISTING grade
involution. A Clifford algebra with a nonzero quadratic relation cannot
support that same generator-scaling as an algebra automorphism.
-/

noncomputable section

namespace InfoGeometry.Clifford.ExteriorDegreePhaseFour

open InfoGeometry.Algebra.FourthRootPeirceProjectors
open InfoGeometry.Canonical.ExteriorSpinorChiralityBridge
open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Extend multiplication by i on generators with the native exterior functor. -/
def degreePhase : ExteriorAlgebra ℂ V →ₐ[ℂ] ExteriorAlgebra ℂ V :=
  ExteriorAlgebra.map (Complex.I • (LinearMap.id : V →ₗ[ℂ] V))

def phaseEnd : Module.End ℂ (ExteriorAlgebra ℂ V) := degreePhase.toLinearMap

@[simp] theorem degreePhase_ι (v : V) :
    degreePhase (ExteriorAlgebra.ι ℂ v) = Complex.I • ExteriorAlgebra.ι ℂ v := by
  simp [degreePhase]

/-- The square agrees with the repository's grade involution on the whole algebra. -/
theorem degreePhase_square :
    degreePhase.comp degreePhase =
      (gradeInvolution : ExteriorAlgebra ℂ V →ₐ[ℂ] ExteriorAlgebra ℂ V) := by
  apply ExteriorAlgebra.hom_ext
  apply LinearMap.ext
  intro v
  simp [AlgHom.comp_apply, smul_smul, Complex.I_mul_I]

theorem phaseEnd_square : phaseEnd^2 =
    (gradeInvolution : ExteriorAlgebra ℂ V →ₐ[ℂ] ExteriorAlgebra ℂ V).toLinearMap := by
  apply LinearMap.ext
  intro x
  change degreePhase (degreePhase x) = gradeInvolution x
  exact DFunLike.congr_fun degreePhase_square x

theorem phaseEnd_fourth : (phaseEnd : Module.End ℂ (ExteriorAlgebra ℂ V))^4 = 1 := by
  calc
    _ = phaseEnd^2 * phaseEnd^2 := by noncomm_ring
    _ = _ := by
      rw [phaseEnd_square]
      apply LinearMap.ext
      intro x
      exact gradeInvolution_involutive x

/-- The degree phase acts by i^n on the native alternating n-fold product. -/
theorem degreePhase_ιMulti (n : ℕ) (v : Fin n → V) :
    degreePhase (ExteriorAlgebra.ιMulti ℂ n v) =
      Complex.I^n • ExteriorAlgebra.ιMulti ℂ n v := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
      rw [ExteriorAlgebra.ιMulti_succ_apply, map_mul, degreePhase_ι, ih]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ']

/-- The eigenvalue statement holds on the whole exterior-power submodule. -/
theorem degreePhase_homogeneous (n : ℕ) (x : ⋀[ℂ]^n V) :
    degreePhase (x : ExteriorAlgebra ℂ V) = Complex.I^n • (x : ExteriorAlgebra ℂ V) := by
  have h : (phaseEnd : Module.End ℂ (ExteriorAlgebra ℂ V)).comp
        (Submodule.subtype (⋀[ℂ]^n V)) =
      (Complex.I^n) • (Submodule.subtype (⋀[ℂ]^n V)) := by
    apply exteriorPower.linearMap_ext
    ext v
    exact degreePhase_ιMulti n v
  exact DFunLike.congr_fun h x

/-- The fourth-root scalar depends precisely on the residue of the degree. -/
theorem I_pow_mod_four (n : ℕ) : Complex.I^n = Complex.I^(n % 4) := by
  have h4 : Complex.I^4 = 1 := by norm_num [pow_succ, Complex.I_mul_I]
  calc
    Complex.I^n = Complex.I^(n % 4 + 4*(n/4)) := by rw [Nat.mod_add_div]
    _ = Complex.I^(n % 4) := by rw [pow_add, pow_mul, h4]; simp

/-- Actual operator projectors onto exterior degrees modulo four. -/
def degreeProjector (k : Fin 4) : Module.End ℂ (ExteriorAlgebra ℂ V) :=
  projector phaseEnd k

/-- Selection of every homogeneous exterior element, including intermediate degrees. -/
theorem degreeProjector_homogeneous (n : ℕ) (x : ⋀[ℂ]^n V) (k : Fin 4) :
    degreeProjector k (x : ExteriorAlgebra ℂ V) =
      if k.val = n % 4 then (x : ExteriorAlgebra ℂ V) else 0 := by
  let r : Fin 4 := ⟨n % 4, Nat.mod_lt n (by norm_num)⟩
  have hx : phaseEnd (x : ExteriorAlgebra ℂ V) = phase r • (x : ExteriorAlgebra ℂ V) := by
    change degreePhase (x : ExteriorAlgebra ℂ V) = _
    rw [degreePhase_homogeneous, I_pow_mod_four]
    rfl
  simpa only [degreeProjector, Fin.ext_iff, r] using
    projector_apply_on_eigenvector phaseEnd (x : ExteriorAlgebra ℂ V) k r hx

/-- The residue projectors are a constructed complete orthogonal family. -/
def degreeProjectorsComplete :
    CompleteOrthogonalIdempotents (degreeProjector (V := V)) :=
  completeProjectors phaseEnd phaseEnd_fourth

/-- Wedge creation raises the phase by one, as a true all-state identity. -/
theorem degreePhase_wedge (v : V) (x : ExteriorAlgebra ℂ V) :
    degreePhase (ExteriorAlgebra.ι ℂ v * x) =
      Complex.I • (ExteriorAlgebra.ι ℂ v * degreePhase x) := by
  rw [map_mul, degreePhase_ι, smul_mul_assoc]

/-- Native contraction lowers the phase by one, with the inverse phase factor. -/
theorem degreePhase_contract (φ : Module.Dual ℂ V) (x : ExteriorAlgebra ℂ V) :
    degreePhase (CliffordAlgebra.contractLeft φ x) =
      (-Complex.I) • CliffordAlgebra.contractLeft φ (degreePhase x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | ι_mul x v hx =>
      simp only [CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul,
        degreePhase_wedge, hx, smul_sub, smul_smul, mul_smul_comm]
      norm_num [Complex.I_mul_I] <;> module

/-- Coarsening the four sectors recovers the existing even-grade projector. -/
theorem degree_even_coarsening :
    degreeProjector (V := V) 0 + degreeProjector 2 =
      (1/2 : ℂ) • (1 +
        (gradeInvolution : ExteriorAlgebra ℂ V →ₐ[ℂ] ExteriorAlgebra ℂ V).toLinearMap) := by
  rw [← phaseEnd_square]
  norm_num [degreeProjector, projector, phase, pow_succ, Complex.I_mul_I] <;> module

theorem degree_odd_coarsening :
    degreeProjector (V := V) 1 + degreeProjector 3 =
      (1/2 : ℂ) • (1 -
        (gradeInvolution : ExteriorAlgebra ℂ V →ₐ[ℂ] ExteriorAlgebra ℂ V).toLinearMap) := by
  rw [← phaseEnd_square]
  norm_num [degreeProjector, projector, phase, pow_succ, Complex.I_mul_I] <;> module

/-- The degree phase fixes the scalar unit and hence cannot square to minus identity. -/
theorem phaseEnd_square_ne_neg_one :
    (phaseEnd : Module.End ℂ (ExteriorAlgebra ℂ V))^2 ≠ -1 := by
  intro h
  have h1 := congrArg (fun T : Module.End ℂ (ExteriorAlgebra ℂ V) =>
    T (1 : ExteriorAlgebra ℂ V)) h
  have hbad : (1 : ExteriorAlgebra ℂ V) = -1 := by
    simpa [phaseEnd, pow_two] using h1
  have hc := congrArg ExteriorAlgebra.algebraMapInv hbad
  norm_num at hc

section NonzeroQuadraticObstruction

variable {A : Type*} [Ring A] [Algebra ℂ A] [Nontrivial A]

/-- Multiplicative scaling by i is incompatible with any nonzero scalar square. -/
theorem no_phase_algHom (a : A) (q : ℂ) (hq : q ≠ 0)
    (ha : a*a = algebraMap ℂ A q) :
    ¬ ∃ F : A →ₐ[ℂ] A, F a = Complex.I • a := by
  rintro ⟨F, hF⟩
  have h : algebraMap ℂ A q = algebraMap ℂ A (-q) := by
    calc
      _ = F (a*a) := by rw [ha, AlgHom.commutes]
      _ = (Complex.I • a) * (Complex.I • a) := by rw [map_mul, hF]
      _ = algebraMap ℂ A (-q) := by
        rw [smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I, neg_one_smul,
          ha, map_neg]
  have hs : q = -q := (algebraMap ℂ A).injective h
  apply hq
  linear_combination (1/2 : ℂ) * hs

end NonzeroQuadraticObstruction

end InfoGeometry.Clifford.ExteriorDegreePhaseFour
