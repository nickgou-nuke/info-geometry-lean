/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.HestenesKreinSplitQuaternionBridge
import InfoGeometry.Canonical.ParaComplexNeutralForm
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Ring.Parity

/-!
# The alternating leaf form of a real hypersymplectic vector space

This owner uses the existing real Hestenes--Krein operator datum. Its field
`D.K` is the elliptic operator `I`, with square `-1`; its field `D.eta` is the
para involution, with square `1`. Anticommutation exchanges the two existing
para eigenspaces. It does not make either eigenspace stable under `I`.

The actual restriction of `I` gives a linear equivalence between the leaves,
with inverse `-I`. For a symmetric nondegenerate form `B` making both operators
skew, the form `B(Iu,v)` restricted to the positive leaf is alternating and
nondegenerate. Its even dimension, proved by a real determinant argument,
therefore makes the dimension of the ambient space divisible by four.

Cross nondegeneracy is derived from whole-space nondegeneracy, isotropy and
the existing Peirce decomposition. It is not a stored extra hypothesis.
The statements include the zero space. They assert finite algebraic geometry,
not closed differential forms, integrable manifold structures, a signature
classification, or a metric identification with the common-symplectic-form
bimetric construction.
-/

noncomputable section

namespace InfoGeometry.Geometry.HypersymplecticDimension

open InfoGeometry.Canonical
open HestenesKreinSplitQuaternionBridge
open ParaComplexConnection
open ParaComplexNeutralForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ## The existing para leaves and the elliptic exchange map -/

/-- View the para operator of the existing split datum through the existing
para-complex interface. No new projector or eigenspace construction is used. -/
def paraStructure (D : HestenesKreinSplitQuaternionBridge.Datum (V := V)) :
    ParaComplexConnection.ParaComplexStructure V where
  tau := D.eta
  tau_sq x := by
    simpa using congrArg (fun T : Module.End ℝ V => T x) D.eta_sq

/-- The native positive para eigenspace of the datum. -/
abbrev plusLeaf (D : HestenesKreinSplitQuaternionBridge.Datum (V := V)) :
    Submodule ℝ V := plusEigenspace (paraStructure D)

/-- The native negative para eigenspace of the datum. -/
abbrev minusLeaf (D : HestenesKreinSplitQuaternionBridge.Datum (V := V)) :
    Submodule ℝ V := minusEigenspace (paraStructure D)

theorem elliptic_sq_apply (D : HestenesKreinSplitQuaternionBridge.Datum (V := V))
    (x : V) : D.K (D.K x) = -x := by
  simpa using congrArg (fun T : Module.End ℝ V => T x) D.K_sq

theorem para_elliptic_apply (D : HestenesKreinSplitQuaternionBridge.Datum (V := V))
    (x : V) : D.eta (D.K x) = -(D.K (D.eta x)) := by
  have h : D.eta * D.K = -(D.K * D.eta) := by
    simpa only [HestenesKreinSplitQuaternionBridge.H] using eta_mul_K_eq_neg_H D
  simpa using congrArg (fun T : Module.End ℝ V => T x) h

theorem elliptic_mem_minus (D : HestenesKreinSplitQuaternionBridge.Datum (V := V))
    {x : V} (hx : x ∈ plusLeaf D) : D.K x ∈ minusLeaf D := by
  apply (mem_minusEigenspace_iff (paraStructure D) (D.K x)).2
  have hx' : D.eta x = x := (mem_plusEigenspace_iff (paraStructure D) x).1 hx
  change D.eta (D.K x) = -(D.K x)
  rw [para_elliptic_apply D, hx']

theorem elliptic_mem_plus (D : HestenesKreinSplitQuaternionBridge.Datum (V := V))
    {x : V} (hx : x ∈ minusLeaf D) : D.K x ∈ plusLeaf D := by
  apply (mem_plusEigenspace_iff (paraStructure D) (D.K x)).2
  have hx' : D.eta x = -x := (mem_minusEigenspace_iff (paraStructure D) x).1 hx
  change D.eta (D.K x) = D.K x
  rw [para_elliptic_apply D, hx', map_neg, neg_neg]

/-- The elliptic operator exchanges the para leaves. Its inverse is the
negative elliptic operator, not the elliptic operator itself. -/
def ellipticLeafEquiv (D : HestenesKreinSplitQuaternionBridge.Datum (V := V)) :
    plusLeaf D ≃ₗ[ℝ] minusLeaf D where
  toFun u := ⟨D.K (u : V), elliptic_mem_minus D u.property⟩
  invFun v := ⟨-(D.K (v : V)), (plusLeaf D).neg_mem (elliptic_mem_plus D v.property)⟩
  left_inv u := by
    apply Subtype.ext
    change -(D.K (D.K (u : V))) = (u : V)
    rw [elliptic_sq_apply D, neg_neg]
  right_inv v := by
    apply Subtype.ext
    change D.K (-(D.K (v : V))) = (v : V)
    rw [map_neg, elliptic_sq_apply D, neg_neg]
  map_add' u v := by
    apply Subtype.ext
    change D.K ((u : V) + (v : V)) = D.K (u : V) + D.K (v : V)
    exact D.K.map_add _ _
  map_smul' c u := by
    apply Subtype.ext
    change D.K (c • (u : V)) = c • D.K (u : V)
    exact D.K.map_smul c _

@[simp] theorem ellipticLeafEquiv_apply
    (D : HestenesKreinSplitQuaternionBridge.Datum (V := V)) (u : plusLeaf D) :
    (ellipticLeafEquiv D u : V) = D.K (u : V) := rfl

@[simp] theorem ellipticLeafEquiv_symm_apply
    (D : HestenesKreinSplitQuaternionBridge.Datum (V := V)) (v : minusLeaf D) :
    ((ellipticLeafEquiv D).symm v : V) = -(D.K (v : V)) := rfl

/-! ## Cross nondegeneracy follows from the existing decomposition -/

/-- An element of the negative leaf annihilating the positive leaf is zero
when the ambient form separates on the left and both leaves are isotropic. -/
theorem minus_cross_separating (PCS : ParaComplexConnection.ParaComplexStructure V)
    (B : LinearMap.BilinForm ℝ V) (hB : B.SeparatingLeft)
    (hcompat : AntiCompatible PCS B) {u : V} (hu : u ∈ minusEigenspace PCS)
    (hcross : ∀ v ∈ plusEigenspace PCS, B u v = 0) : u = 0 := by
  apply hB u
  intro v
  have hp := hcross (peircePlus PCS v) (peircePlus_mem_plusEigenspace PCS v)
  have hm := minus_isotropic PCS B hcompat hu (peirceMinus_mem_minusEigenspace PCS v)
  calc
    B u v = B u (peircePlus PCS v + peirceMinus PCS v) :=
      congrArg (B u) (peirce_sum_id PCS v).symm
    _ = 0 := by rw [map_add, hp, hm, add_zero]

/-- The reverse cross pairing is separating for the same reason. No finite
dimension, symmetry, or separately assumed cross-nondegeneracy is needed. -/
theorem plus_cross_separating (PCS : ParaComplexConnection.ParaComplexStructure V)
    (B : LinearMap.BilinForm ℝ V) (hB : B.SeparatingLeft)
    (hcompat : AntiCompatible PCS B) {u : V} (hu : u ∈ plusEigenspace PCS)
    (hcross : ∀ v ∈ minusEigenspace PCS, B u v = 0) : u = 0 := by
  apply hB u
  intro v
  have hp := plus_isotropic PCS B hcompat hu (peircePlus_mem_plusEigenspace PCS v)
  have hm := hcross (peirceMinus PCS v) (peirceMinus_mem_minusEigenspace PCS v)
  calc
    B u v = B u (peircePlus PCS v + peirceMinus PCS v) :=
      congrArg (B u) (peirce_sum_id PCS v).symm
    _ = 0 := by rw [map_add, hp, hm, add_zero]

theorem para_antiCompatible
    (D : HestenesKreinSplitQuaternionBridge.Datum (V := V))
    (B : LinearMap.BilinForm ℝ V)
    (hpara : ∀ x y, B (D.eta x) y = -B x (D.eta y)) :
    AntiCompatible (paraStructure D) B := by
  intro x y
  change B (D.eta x) y + B x (D.eta y) = 0
  rw [hpara, neg_add_cancel]

/-- Construct the repository's neutral-form package, deriving its cross
nondegeneracy fields instead of adding them as hypotheses. -/
def neutralDatum (D : HestenesKreinSplitQuaternionBridge.Datum (V := V))
    (B : LinearMap.BilinForm ℝ V) (hsymm : B.IsSymm) (hB : B.Nondegenerate)
    (hpara : ∀ x y, B (D.eta x) y = -B x (D.eta y)) :
    ParaComplexNeutralForm.NondegenerateDatum (paraStructure D) where
  form := B
  symmetric := hsymm.eq
  anti_compatible := para_antiCompatible D B hpara
  nondegenerate := hB.1
  plus_cross_nondegenerate := fun _ hu hcross =>
    minus_cross_separating (paraStructure D) B hB.1
      (para_antiCompatible D B hpara) hu hcross
  minus_cross_nondegenerate := fun _ hu hcross =>
    plus_cross_separating (paraStructure D) B hB.1
      (para_antiCompatible D B hpara) hu hcross

/-! ## The native alternating form on one para leaf -/

/-- Restrict the native left contraction `B(I-, -)` to the positive leaf.
The elliptic image lies in the opposite leaf, so this uses the cross pairing. -/
def leafForm (D : HestenesKreinSplitQuaternionBridge.Datum (V := V))
    (B : LinearMap.BilinForm ℝ V) : LinearMap.BilinForm ℝ (plusLeaf D) :=
  (B.compLeft D.K).restrict (plusLeaf D)

@[simp] theorem leafForm_apply
    (D : HestenesKreinSplitQuaternionBridge.Datum (V := V))
    (B : LinearMap.BilinForm ℝ V) (u v : plusLeaf D) :
    leafForm D B u v = B (D.K (u : V)) (v : V) := rfl

theorem leafForm_isAlt (D : HestenesKreinSplitQuaternionBridge.Datum (V := V))
    (B : LinearMap.BilinForm ℝ V) (hsymm : B.IsSymm)
    (helliptic : ∀ x y, B (D.K x) y = -B x (D.K y)) :
    (leafForm D B).IsAlt := by
  intro u
  change B (D.K (u : V)) (u : V) = 0
  have h := helliptic (u : V) (u : V)
  rw [hsymm.eq (u : V) (D.K (u : V))] at h
  have hsum : B (D.K (u : V)) (u : V) + B (D.K (u : V)) (u : V) = 0 :=
    eq_neg_iff_add_eq_zero.mp h
  have htwo : (2 : ℝ) * B (D.K (u : V)) (u : V) = 0 := by
    rw [two_mul, hsum]
  exact (mul_eq_zero.mp htwo).resolve_left two_ne_zero

/-- Cross separation and invertibility of the elliptic operator already
give left separation of the leaf form. -/
theorem leafForm_separatingLeft
    (D : HestenesKreinSplitQuaternionBridge.Datum (V := V))
    (B : LinearMap.BilinForm ℝ V) (hB : B.SeparatingLeft)
    (hpara : ∀ x y, B (D.eta x) y = -B x (D.eta y)) :
    (leafForm D B).SeparatingLeft := by
  intro u hu
  have hIu : D.K (u : V) = 0 :=
    minus_cross_separating (paraStructure D) B hB
      (para_antiCompatible D B hpara) (elliptic_mem_minus D u.property)
      (fun v hv => hu ⟨v, hv⟩)
  apply Subtype.ext
  change (u : V) = 0
  have hneg : -(u : V) = 0 :=
    (elliptic_sq_apply D (u : V)).symm.trans (by rw [hIu, map_zero])
  exact neg_eq_zero.mp hneg

/-- Two-sided nondegeneracy of the actual leaf form. Alternation converts
the already derived left separation into right separation. -/
theorem leafForm_nondegenerate
    (D : HestenesKreinSplitQuaternionBridge.Datum (V := V))
    (B : LinearMap.BilinForm ℝ V) (hsymm : B.IsSymm) (hB : B.Nondegenerate)
    (helliptic : ∀ x y, B (D.K x) y = -B x (D.K y))
    (hpara : ∀ x y, B (D.eta x) y = -B x (D.eta y)) :
    (leafForm D B).Nondegenerate := by
  have hleft := leafForm_separatingLeft D B hB.1 hpara
  have halt := leafForm_isAlt D B hsymm helliptic
  refine ⟨hleft, ?_⟩
  intro u hu
  apply hleft u
  intro v
  have h := halt.neg_eq u v
  rw [hu v] at h
  exact neg_eq_zero.mp h

/-! ## Real determinant parity and the ambient dimension -/

/-- A finite-dimensional real vector space with a nondegenerate alternating
bilinear form has even dimension. The proof uses the determinant of its
matrix in a native finite basis, including the empty basis. -/
theorem even_finrank_of_alternating {W : Type*} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] (C : LinearMap.BilinForm ℝ W)
    (halt : C.IsAlt) (hC : C.Nondegenerate) : Even (Module.finrank ℝ W) := by
  classical
  let b := Module.finBasis ℝ W
  let M : Matrix (Fin (Module.finrank ℝ W)) (Fin (Module.finrank ℝ W)) ℝ :=
    LinearMap.BilinForm.toMatrix b C
  have hdet : Matrix.det M ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hC
  have htranspose : Matrix.transpose M = -M := by
    ext i j
    change (LinearMap.BilinForm.toMatrix b C) j i =
      -(LinearMap.BilinForm.toMatrix b C) i j
    simp only [LinearMap.BilinForm.toMatrix_apply]
    exact (halt.neg_eq (b i) (b j)).symm
  by_contra hnot
  have hodd : Odd (Module.finrank ℝ W) := Nat.not_even_iff_odd.mp hnot
  have hneg : Matrix.det M = -Matrix.det M := by
    calc
      Matrix.det M = Matrix.det (Matrix.transpose M) := (Matrix.det_transpose M).symm
      _ = Matrix.det (-M) := congrArg Matrix.det htranspose
      _ = -Matrix.det M := by
        rw [Matrix.det_neg, Fintype.card_fin, hodd.neg_one_pow, neg_one_mul]
  exact hdet (by linarith)

theorem even_finrank_plusLeaf [FiniteDimensional ℝ V]
    (D : HestenesKreinSplitQuaternionBridge.Datum (V := V))
    (B : LinearMap.BilinForm ℝ V) (hsymm : B.IsSymm) (hB : B.Nondegenerate)
    (helliptic : ∀ x y, B (D.K x) y = -B x (D.K y))
    (hpara : ∀ x y, B (D.eta x) y = -B x (D.eta y)) :
    Even (Module.finrank ℝ (plusLeaf D)) :=
  even_finrank_of_alternating (leafForm D B) (leafForm_isAlt D B hsymm helliptic)
    (leafForm_nondegenerate D B hsymm hB helliptic hpara)

/-- The actual elliptic leaf equivalence supplies the cross equivalence
required by the existing finite-rank decomposition theorem. -/
theorem finrank_eq_two_mul_plusLeaf [FiniteDimensional ℝ V]
    (D : HestenesKreinSplitQuaternionBridge.Datum (V := V)) :
    Module.finrank ℝ V = 2 * Module.finrank ℝ (plusLeaf D) :=
  finrank_v_eq_two_mul_plus_of_cross_equiv (paraStructure D) (ellipticLeafEquiv D)

/-- A single symmetric nondegenerate real form making both members of an
anticommuting elliptic/para pair skew forces four-divisibility of the ambient
dimension. No positivity, nontriviality, or leaf-parity assumption is added. -/
theorem four_dvd_finrank [FiniteDimensional ℝ V]
    (D : HestenesKreinSplitQuaternionBridge.Datum (V := V))
    (B : LinearMap.BilinForm ℝ V) (hsymm : B.IsSymm) (hB : B.Nondegenerate)
    (helliptic : ∀ x y, B (D.K x) y = -B x (D.K y))
    (hpara : ∀ x y, B (D.eta x) y = -B x (D.eta y)) :
    4 ∣ Module.finrank ℝ V := by
  obtain ⟨m, hm⟩ := even_finrank_plusLeaf D B hsymm hB helliptic hpara
  refine ⟨m, ?_⟩
  rw [finrank_eq_two_mul_plusLeaf D, hm]
  exact (Nat.mul_add 2 m m).trans (Nat.add_mul 2 2 m).symm

end InfoGeometry.Geometry.HypersymplecticDimension
