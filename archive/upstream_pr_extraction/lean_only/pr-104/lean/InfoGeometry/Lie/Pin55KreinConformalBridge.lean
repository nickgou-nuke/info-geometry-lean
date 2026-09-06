import InfoGeometry.Lie.SplitOctonionNonmultiplicativity
import InfoGeometry.Physics.SplitCliffordAlgebras
import InfoGeometry.Canonical.WittenMoebiusChiralParityIndex
import InfoGeometry.Clifford.Cl55SpinorChirality
import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Canonical.ZornVectorMatrixExplicit
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Trace
import InfoGeometry.Clifford.SpinorRep
import InfoGeometry.Clifford.CliffordInclusionInjective
import InfoGeometry.Lie.SplitOctonionImaginaryAction
import InfoGeometry.Lie.SplitOctonionCliffordAction
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
import InfoGeometry.Clifford.SplitCl44CausalEnvelope

/-!
# Pin(5,5) Krein Conformal Representation Bridge — Roadmap

This file is a concrete package sketch plus explicit closure debt.

* Verified native kernel-checked proofs in this surface:
  - `anomaly_index_zero_proof`
  - `ρ_spinor_ι_sq`
  - `J_concrete_sq`, `χ_concrete_sq`, `ε_concrete_sq`
  - `P_K_comp_ι_K_eq_id`

* The package is conditional data.  The remaining representation boundary is
  exposed by `Pin55KreinConformalPackage.IsValid`; this file does not construct
  a universal carrier/reindexing theorem connecting every Clifford model to
  the concrete finite operators below.

No analytic or group-level Pin(5,5) claim is promoted from this conditional
package.
-/

noncomputable section
namespace InfoGeometry.Lie.Pin55KreinConformalBridge

open SplitClifford
open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.CliffordTower
open InfoGeometry.Lie.SplitOctonionNonmultiplicativity
open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Clifford.SplitCl44CausalEnvelope
open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Clifford.SpinorRep
open InfoGeometry.Clifford

/--
A representation package formalizing the conformal/Krein bridge
from the 8D split-octonions/Cl(4,4) side to the 10D Pin(5,5) side.
-/
structure Pin55KreinConformalPackage where
  K : Type
  [addCommGroup : AddCommGroup K]
  [moduleReal : Module ℝ K]
  [finiteDimensional : FiniteDimensional ℝ K]
  B : LinearMap.BilinForm ℝ K
  J : K →ₗ[ℝ] K
  χ : K →ₗ[ℝ] K
  ε : K →ₗ[ℝ] K
  ρ : SpinorRep.Cl_split 5 →ₐ[ℝ] Module.End ℝ K

attribute [instance] Pin55KreinConformalPackage.addCommGroup
attribute [instance] Pin55KreinConformalPackage.moduleReal
attribute [instance] Pin55KreinConformalPackage.finiteDimensional

/-! Validity is an explicit predicate, not hidden proof-bearing structure
fields.  A package is data; these laws must be proved by the caller for the
chosen representation and bilinear form. -/
def Pin55KreinConformalPackage.IsValid
    (pkg : Pin55KreinConformalPackage) : Prop :=
  pkg.J ∘ₗ pkg.J = LinearMap.id ∧
  pkg.χ ∘ₗ pkg.χ = LinearMap.id ∧
  pkg.ε ∘ₗ pkg.ε = LinearMap.id ∧
  pkg.B.IsSymm ∧
  pkg.B.Nondegenerate ∧
  (∀ (v : InfoGeometry.CliffordTower.SplitSpace 5),
    ∀ (x y : pkg.K),
      pkg.B (pkg.ρ (CliffordAlgebra.ι (SpinorRep.SplitQuad 5) v) x)
          (pkg.ρ (CliffordAlgebra.ι (SpinorRep.SplitQuad 5) v) y) =
        (SpinorRep.SplitQuad 5 v : ℝ) • pkg.B x y) ∧
  LinearMap.trace ℝ pkg.K (pkg.χ ∘ₗ pkg.ε) = 0

/-- Concrete 10D Krein symmetry J on SplitClifford.SplitSpace 5. -/
def J_concrete : (Fin 32 → ℝ) →ₗ[ℝ] (Fin 32 → ℝ) :=
  { toFun := fun v i => if i.val < 16 then v i else -v i
    map_add' := fun x y => by ext i; dsimp; split_ifs <;> ring
    map_smul' := fun c x => by ext i; dsimp; split_ifs <;> ring }

/-- Concrete 10D chiral grading χ on SplitClifford.SplitSpace 5. -/
def χ_concrete : (Fin 32 → ℝ) →ₗ[ℝ] (Fin 32 → ℝ) :=
  { toFun := fun v i => if i.val < 16 then -v i else v i
    map_add' := fun x y => by ext i; dsimp; split_ifs <;> ring
    map_smul' := fun c x => by ext i; dsimp; split_ifs <;> ring }

/-- Concrete 10D parity ε on SplitClifford.SplitSpace 5. -/
def ε_concrete : (Fin 32 → ℝ) →ₗ[ℝ] (Fin 32 → ℝ) :=
  { toFun := fun v i => if i.val % 2 = 0 then v i else -v i
    map_add' := fun x y => by ext i; dsimp; split_ifs <;> ring
    map_smul' := fun c x => by ext i; dsimp; split_ifs <;> ring }

/-- In this concrete model the chiral grading is the negative of the Krein
symmetry; the two named operators are not independent data. -/
theorem χ_concrete_eq_neg_J_concrete :
    χ_concrete = -J_concrete := by
  apply LinearMap.ext
  intro v
  ext i
  dsimp [χ_concrete, J_concrete]
  split_ifs <;> ring

theorem J_concrete_sq : J_concrete ∘ₗ J_concrete = LinearMap.id := by
  refine LinearMap.ext (fun v => ?_)
  ext i
  dsimp [J_concrete]
  split_ifs <;> ring

theorem χ_concrete_sq : χ_concrete ∘ₗ χ_concrete = LinearMap.id := by
  refine LinearMap.ext (fun v => ?_)
  ext i
  dsimp [χ_concrete]
  split_ifs <;> ring

theorem ε_concrete_sq : ε_concrete ∘ₗ ε_concrete = LinearMap.id := by
  refine LinearMap.ext (fun v => ?_)
  ext i
  dsimp [ε_concrete]
  split_ifs <;> ring

/-- **Genuine Non-Degenerate Signature (16, 16) Krein Bilinear Form on ℝ³²:**
    $$B_{\text{signature}}(x, y) = \sum_{i < 16} x_i y_i - \sum_{i \ge 16} x_i y_i$$
    Satisfies positive definite metric on the first 16 dimensions and negative definite on the last 16. -/
def B_krein_signature : LinearMap.BilinForm ℝ (Fin 32 → ℝ) :=
  LinearMap.mk₂ ℝ
    (fun x y =>
      (∑ i ∈ Finset.univ.filter (fun (i : Fin 32) => i.val < 16), x i * y i) -
      (∑ i ∈ Finset.univ.filter (fun (i : Fin 32) => 16 ≤ i.val), x i * y i))
    (fun x1 x2 y => by
      dsimp
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      ring)
    (fun c x y => by
      dsimp
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      ring)
    (fun x y1 y2 => by
      dsimp
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      ring)
    (fun c x y => by
      dsimp
      simp_rw [mul_comm (x _), mul_assoc]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      ring)

/-- Signature property: evaluating B_krein_signature on basis vector e₀ gives +1. -/
theorem B_krein_signature_pos_diagonal :
    B_krein_signature (Pi.single 0 1) (Pi.single 0 1) = 1 := by
  dsimp [B_krein_signature, LinearMap.mk₂]
  simp [Pi.single_apply]

/-- Signature property: evaluating B_krein_signature on basis vector e₁₆ gives -1. -/
theorem B_krein_signature_neg_diagonal :
    B_krein_signature (Pi.single 16 1) (Pi.single 16 1) = -1 := by
  dsimp [B_krein_signature, LinearMap.mk₂]
  simp [Pi.single_apply]

/-! The concrete diagonal form is symmetric in its two arguments. -/
theorem B_krein_signature_isSymm :
    B_krein_signature.IsSymm := by
  rw [LinearMap.BilinForm.isSymm_def]
  intro x y
  dsimp [B_krein_signature, LinearMap.mk₂]
  rw [Finset.sum_congr rfl (fun i hi => mul_comm (x i) (y i))]
  rw [Finset.sum_congr rfl (fun i hi => mul_comm (x i) (y i))]

/-- Non-degeneracy theorem: B_krein_signature is strictly non-zero. -/
theorem B_krein_signature_nonzero : B_krein_signature ≠ 0 := by
  intro h
  have h_eval := LinearMap.congr_fun (LinearMap.congr_fun h (Pi.single 0 1)) (Pi.single 0 1)
  rw [B_krein_signature_pos_diagonal] at h_eval
  dsimp at h_eval
  exact zero_ne_one h_eval.symm

/-- The concrete signature form separates both arguments.  This establishes
the genuine finite-dimensional Krein form used by the concrete packet; it
does not assert that the spinor representation preserves this form. -/
theorem B_krein_signature_nondegenerate :
    B_krein_signature.Nondegenerate := by
  constructor
  · intro x hx
    funext i
    by_cases hi : i.val < 16
    · have h := hx (Pi.single i 1)
      have hnot : ¬ 16 ≤ i.val := by omega
      dsimp [B_krein_signature, LinearMap.mk₂] at h
      simp [hi, hnot, Pi.single_apply] at h
      change x i = 0
      exact h
    · have hle : 16 ≤ i.val := by omega
      have h := hx (Pi.single i 1)
      dsimp [B_krein_signature, LinearMap.mk₂] at h
      simp [hi, hle, Pi.single_apply] at h
      change x i = 0
      exact h
  · intro y hy
    funext i
    by_cases hi : i.val < 16
    · have h := hy (Pi.single i 1)
      have hnot : ¬ 16 ≤ i.val := by omega
      dsimp [B_krein_signature, LinearMap.mk₂] at h
      simp [hi, hnot, Pi.single_apply] at h
      change y i = 0
      exact h
    · have hle : 16 ≤ i.val := by omega
      have h := hy (Pi.single i 1)
      dsimp [B_krein_signature, LinearMap.mk₂] at h
      simp [hi, hle, Pi.single_apply] at h
      change y i = 0
      exact h

/-- Concrete algebra representation of Cl(5,5) on the 32D spinor module. -/
noncomputable def ρ_spinor : SpinorRep.Cl_split 5 →ₐ[ℝ] Module.End ℝ (Fin 32 → ℝ) :=
  (Matrix.toLinAlgEquiv (Pi.basisFun ℝ (Fin 32))).toAlgHom.comp (SpinorRep.spinorRepresentation 5)

/-- **Theorem: Anomaly Index Zero for Concrete Pin(5,5) Krein Package**
    The trace of the chiral-parity composite involution `χ_concrete ∘ₗ ε_concrete`
    evaluates to `(-8) + 8 + 8 + (-8) = 0`. -/
theorem anomaly_index_zero_proof :
    LinearMap.trace ℝ (Fin 32 → ℝ) (χ_concrete ∘ₗ ε_concrete) = 0 := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin 32))]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Pi.basisFun_apply, LinearMap.comp_apply, Pi.basisFun_repr]
  dsimp [χ_concrete, ε_concrete]
  simp only [Pi.single_eq_same]
  repeat rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_zero]
  dsimp
  ring

/-- The same finite result under a theorem-honest trace terminology. -/
theorem chiral_parity_trace_zero :
    LinearMap.trace ℝ (Fin 32 → ℝ) (χ_concrete ∘ₗ ε_concrete) = 0 :=
  by
    rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin 32))]
    simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
      Pi.basisFun_apply, LinearMap.comp_apply, Pi.basisFun_repr]
    dsimp [χ_concrete, ε_concrete]
    simp only [Pi.single_eq_same]
    repeat rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_zero]
    dsimp
    ring

/-- Clifford algebra generator squaring relation on the spinor representation. -/
theorem ρ_spinor_ι_sq (v : InfoGeometry.CliffordTower.SplitSpace 5) :
    ρ_spinor (CliffordAlgebra.ι (SpinorRep.SplitQuad 5) v) ∘ₗ ρ_spinor (CliffordAlgebra.ι (SpinorRep.SplitQuad 5) v) =
      (SpinorRep.SplitQuad 5 v) • LinearMap.id := by
  have h_hom :
      ρ_spinor (CliffordAlgebra.ι (SpinorRep.SplitQuad 5) v) ∘ₗ ρ_spinor (CliffordAlgebra.ι (SpinorRep.SplitQuad 5) v) =
        ρ_spinor (CliffordAlgebra.ι (SpinorRep.SplitQuad 5) v * CliffordAlgebra.ι (SpinorRep.SplitQuad 5) v) := by
    exact (ρ_spinor.map_mul (CliffordAlgebra.ι (SpinorRep.SplitQuad 5) v) (CliffordAlgebra.ι (SpinorRep.SplitQuad 5) v)).symm
  rw [h_hom]
  rw [CliffordAlgebra.ι_sq_scalar]
  have h_map := ρ_spinor.commutes (SpinorRep.SplitQuad 5 v)
  exact h_map

/-- Linear injection mapping SplitSpace 4 coordinates to Fin 32 -> ℝ. -/
noncomputable def ι_K_concrete : InfoGeometry.CliffordTower.SplitSpace 4 →ₗ[ℝ] (Fin 32 → ℝ) where
  toFun v :=
    let p1 := v.1
    let p2 := v.2.1
    let p3 := v.2.2.1
    let p4 := v.2.2.2.1
    fun i =>
      if h : i.val = 0 then p1.1
      else if h : i.val = 1 then p1.2
      else if h : i.val = 2 then p2.1
      else if h : i.val = 3 then p2.2
      else if h : i.val = 4 then p3.1
      else if h : i.val = 5 then p3.2
      else if h : i.val = 6 then p4.1
      else if h : i.val = 7 then p4.2
      else 0
  map_add' x y := by
    ext i
    dsimp
    split_ifs <;> try rfl
    simp
  map_smul' r x := by
    ext i
    dsimp
    split_ifs <;> try rfl
    simp

/-- Linear projection mapping Fin 32 -> ℝ back to SplitSpace 4. -/
noncomputable def P_K_concrete : (Fin 32 → ℝ) →ₗ[ℝ] InfoGeometry.CliffordTower.SplitSpace 4 where
  toFun f :=
    (
      (f 0, f 1),
      (f 2, f 3),
      (f 4, f 5),
      (f 6, f 7),
      fun _ => (0, 0)
    )
  map_add' f g := by
    dsimp
    refine Prod.ext ?_ ?_
    · rfl
    · refine Prod.ext ?_ ?_
      · rfl
      · refine Prod.ext ?_ ?_
        · rfl
        · refine Prod.ext ?_ ?_
          · rfl
          · funext ⟨val, isLt⟩; cases isLt
  map_smul' r f := by
    dsimp
    refine Prod.ext ?_ ?_
    · rfl
    · refine Prod.ext ?_ ?_
      · rfl
      · refine Prod.ext ?_ ?_
        · rfl
        · refine Prod.ext ?_ ?_
          · rfl
          · funext ⟨val, isLt⟩; cases isLt

/-- Projection-injection retraction lemma. -/
theorem P_K_comp_ι_K_eq_id :
    P_K_concrete ∘ₗ ι_K_concrete = LinearMap.id := by
  refine LinearMap.ext (fun v => ?_)
  dsimp [P_K_concrete, ι_K_concrete]
  refine Prod.ext ?_ ?_
  · rfl
  · refine Prod.ext ?_ ?_
    · rfl
    · refine Prod.ext ?_ ?_
      · rfl
      · refine Prod.ext ?_ ?_
        · rfl
        · funext ⟨val, isLt⟩
          cases isLt

theorem ι_K_concrete_injective : Function.Injective ι_K_concrete := by
  intro x y hxy
  calc
    x = P_K_concrete (ι_K_concrete x) := by
      have h := congrArg (fun f => f x) P_K_comp_ι_K_eq_id
      simpa [LinearMap.comp_apply] using h.symm
    _ = P_K_concrete (ι_K_concrete y) := congrArg P_K_concrete hxy
    _ = y := by
      have h := congrArg (fun f => f y) P_K_comp_ι_K_eq_id
      simpa [LinearMap.comp_apply] using h

theorem P_K_concrete_surjective : Function.Surjective P_K_concrete := by
  intro v
  refine ⟨ι_K_concrete v, ?_⟩
  have h := congrArg (fun f => f v) P_K_comp_ι_K_eq_id
  simpa [LinearMap.comp_apply] using h

/-- The remaining finite-dimensional intertwining obligation for the concrete
stage-4 carrier. An inhabitant must identify the selected eight spinor
coordinates with split-octonion left multiplication under `e`; it is not a
consequence of the Clifford tower inclusion alone. -/
def Pin55FiniteCarrierCompatibility : Prop :=
  ∀ X : Imaginary,
    P_K_concrete ∘ₗ
        (ρ_spinor
          (SpinorRep.incl_Cl_split 4
            (CliffordAlgebra.ι (SpinorRep.SplitQuad 4)
              (InfoGeometry.Lie.SplitOctonionNonmultiplicativity.e X.1)))) ∘ₗ
      ι_K_concrete =
    InfoGeometry.Lie.SplitOctonionNonmultiplicativity.e ∘ₗ
      imaginaryLeftMul X ∘ₗ
      InfoGeometry.Lie.SplitOctonionNonmultiplicativity.e.symm

/-! A package readout is valid only after the package and all finite carrier
compatibility data have been supplied.  In particular, this theorem does not
construct a package from the compatibility law and cannot hide the missing
Krein-form preservation proof. -/
theorem pin55_krein_conformal_package_readout
    (pkg : Pin55KreinConformalPackage)
    (_hvalid : pkg.IsValid)
    (e : CanonicalZorn ≃ₗ[ℝ] InfoGeometry.CliffordTower.SplitSpace 4)
    (ι_K : InfoGeometry.CliffordTower.SplitSpace 4 →ₗ[ℝ] pkg.K)
    (P_K : pkg.K →ₗ[ℝ] InfoGeometry.CliffordTower.SplitSpace 4)
    (hcompat : ∀ (X : Imaginary),
      P_K ∘ₗ (pkg.ρ (SpinorRep.incl_Cl_split 4
        (CliffordAlgebra.ι (SpinorRep.SplitQuad 4) (e X.1)))) ∘ₗ ι_K =
        e ∘ₗ imaginaryLeftMul X ∘ₗ e.symm) :
    ∀ (X : Imaginary),
      P_K ∘ₗ (pkg.ρ (SpinorRep.incl_Cl_split 4
        (CliffordAlgebra.ι (SpinorRep.SplitQuad 4) (e X.1)))) ∘ₗ ι_K =
        e ∘ₗ imaginaryLeftMul X ∘ₗ e.symm :=
  hcompat

end InfoGeometry.Lie.Pin55KreinConformalBridge
