import Mathlib.Algebra.Lie.Killing
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Lie.InvariantForm

open scoped Invertible

universe u v

namespace InfoGeometry.Core.Generic

variable {R : Type u} {L : Type v}

section Symmetric

variable [CommRing R]
variable [LieRing L] [LieAlgebra R L]

/-- A symmetric Lie algebra is a Lie algebra with an involutive automorphism. -/
structure SymmetricLieAlgebra (R : Type u) (L : Type v)
    [CommRing R] [LieRing L] [LieAlgebra R L] where
  θ : L ≃ₗ⁅R⁆ L
  involution : θ.trans θ = (LieEquiv.refl : L ≃ₗ⁅R⁆ L)

namespace SymmetricLieAlgebra

variable (S : SymmetricLieAlgebra R L)

@[simp] lemma involution_apply (x : L) : S.θ (S.θ x) = x := by
  have h := congrArg (fun e : L ≃ₗ⁅R⁆ L => e x) S.involution
  simpa using h

/-!
## Cartan decomposition operators and eigenspaces
-/

def 𝔨 : Submodule R L :=
  LinearMap.ker (S.θ.toLinearMap - (LinearMap.id : L →ₗ[R] L))

def 𝔭 : Submodule R L :=
  LinearMap.ker (S.θ.toLinearMap + (LinearMap.id : L →ₗ[R] L))

lemma mem_𝔨_iff (x : L) : x ∈ S.𝔨 ↔ S.θ x = x := by
  constructor
  · intro hx
    have : S.θ x - x = 0 := by
      simpa [𝔨, LinearMap.mem_ker, LinearMap.sub_apply] using hx
    exact sub_eq_zero.mp this
  · intro hx
    have : S.θ x - x = 0 := by simp [hx]
    simpa [𝔨, LinearMap.mem_ker, LinearMap.sub_apply] using this

lemma mem_𝔭_iff (x : L) : x ∈ S.𝔭 ↔ S.θ x = -x := by
  constructor
  · intro hx
    have : S.θ x + x = 0 := by
      simpa [𝔭, LinearMap.mem_ker, LinearMap.add_apply] using hx
    exact (add_eq_zero_iff_eq_neg).1 this
  · intro hx
    have : S.θ x + x = 0 := by simp [hx]
    simpa [𝔭, LinearMap.mem_ker, LinearMap.add_apply] using this

section Half

variable [Invertible (2 : R)]

def P_plus : L →ₗ[R] L :=
  (⅟ (2 : R)) • ((LinearMap.id : L →ₗ[R] L) + S.θ.toLinearMap)

def P_minus : L →ₗ[R] L :=
  (⅟ (2 : R)) • ((LinearMap.id : L →ₗ[R] L) - S.θ.toLinearMap)

@[simp] lemma P_plus_apply (x : L) :
    S.P_plus x = (⅟ (2 : R)) • (x + S.θ x) := by
  simp [P_plus, LinearMap.add_apply]

@[simp] lemma P_minus_apply (x : L) :
    S.P_minus x = (⅟ (2 : R)) • (x - S.θ x) := by
  simp [P_minus, LinearMap.sub_apply]

lemma P_plus_fixed (x : L) :
    S.θ (S.P_plus x) = S.P_plus x := by
  simp [S.P_plus_apply, map_add, map_smul, S.involution_apply, add_comm]

lemma P_minus_neg_fixed (x : L) :
    S.θ (S.P_minus x) = -S.P_minus x := by
  calc
    S.θ (S.P_minus x) = (⅟ (2 : R)) • (S.θ x - x) := by
      simp [S.P_minus_apply, map_sub, map_smul, S.involution_apply]
    _ = (⅟ (2 : R)) • (-(x - S.θ x)) := by
      simp [sub_eq_add_neg, add_comm]
    _ = -(⅟ (2 : R) • (x - S.θ x)) := by
      rw [smul_neg]
    _ = -S.P_minus x := by
      simp [S.P_minus_apply]

lemma P_plus_mem_𝔨 (x : L) :
    S.P_plus x ∈ S.𝔨 :=
  (S.mem_𝔨_iff _).2 (S.P_plus_fixed x)

lemma P_minus_mem_𝔭 (x : L) :
    S.P_minus x ∈ S.𝔭 :=
  (S.mem_𝔭_iff _).2 (S.P_minus_neg_fixed x)

lemma P_plus_eq_self_of_mem_𝔨 {x : L} (hx : x ∈ S.𝔨) :
    S.P_plus x = x := by
  have hx' : S.θ x = x := (S.mem_𝔨_iff x).1 hx
  calc
    S.P_plus x = (⅟ (2 : R)) • (x + S.θ x) := S.P_plus_apply x
    _ = (⅟ (2 : R)) • (x + x) := by simp [hx']
    _ = (⅟ (2 : R)) • ((2 : R) • x) := by simp [two_smul]
    _ = x := by simp [smul_smul]

lemma P_minus_eq_zero_of_mem_𝔨 {x : L} (hx : x ∈ S.𝔨) :
    S.P_minus x = 0 := by
  have hx' : S.θ x = x := (S.mem_𝔨_iff x).1 hx
  calc
    S.P_minus x = (⅟ (2 : R)) • (x - S.θ x) := S.P_minus_apply x
    _ = (⅟ (2 : R)) • (x - x) := by simp [hx']
    _ = 0 := by simp

lemma P_plus_eq_zero_of_mem_𝔭 {x : L} (hx : x ∈ S.𝔭) :
    S.P_plus x = 0 := by
  have hx' : S.θ x = -x := (S.mem_𝔭_iff x).1 hx
  calc
    S.P_plus x = (⅟ (2 : R)) • (x + S.θ x) := S.P_plus_apply x
    _ = (⅟ (2 : R)) • (x + -x) := by simp [hx']
    _ = 0 := by simp

lemma P_minus_eq_self_of_mem_𝔭 {x : L} (hx : x ∈ S.𝔭) :
    S.P_minus x = x := by
  have hx' : S.θ x = -x := (S.mem_𝔭_iff x).1 hx
  calc
    S.P_minus x = (⅟ (2 : R)) • (x - S.θ x) := S.P_minus_apply x
    _ = (⅟ (2 : R)) • (x + x) := by simp [hx']
    _ = (⅟ (2 : R)) • ((2 : R) • x) := by simp [two_smul]
    _ = x := by simp [smul_smul]

lemma P_plus_idempotent (x : L) :
    S.P_plus (S.P_plus x) = S.P_plus x :=
  S.P_plus_eq_self_of_mem_𝔨 (S.P_plus_mem_𝔨 x)

lemma P_minus_idempotent (x : L) :
    S.P_minus (S.P_minus x) = S.P_minus x :=
  S.P_minus_eq_self_of_mem_𝔭 (S.P_minus_mem_𝔭 x)

lemma P_plus_comp_P_minus (x : L) :
    S.P_plus (S.P_minus x) = 0 :=
  S.P_plus_eq_zero_of_mem_𝔭 (S.P_minus_mem_𝔭 x)

lemma P_minus_comp_P_plus (x : L) :
    S.P_minus (S.P_plus x) = 0 :=
  S.P_minus_eq_zero_of_mem_𝔨 (S.P_plus_mem_𝔨 x)

theorem cartan_decomposition (x : L) :
    x = S.P_plus x + S.P_minus x := by
  symm
  have hx2 : x + x = (2 : R) • x := by
    simpa using (two_smul R x).symm
  have hcombine :
      (⅟ (2 : R)) • (x + S.θ x) + (⅟ (2 : R)) • (x - S.θ x)
        = (⅟ (2 : R)) • ((x + S.θ x) + (x - S.θ x)) := by
    simpa [smul_add] using
      (smul_add (⅟ (2 : R)) (x + S.θ x) (x - S.θ x)).symm
  calc
    S.P_plus x + S.P_minus x
        = (⅟ (2 : R)) • (x + S.θ x) + (⅟ (2 : R)) • (x - S.θ x) := by
            simp [P_plus, P_minus, LinearMap.add_apply, LinearMap.sub_apply]
    _ = (⅟ (2 : R)) • ((x + S.θ x) + (x - S.θ x)) := hcombine
    _ = (⅟ (2 : R)) • (x + x) := by
          simp [sub_eq_add_neg, add_assoc, add_left_comm]
    _ = (⅟ (2 : R)) • ((2 : R) • x) := by simp [hx2]
    _ = x := by
          simp [smul_smul]

theorem P_plus_comp_P_plus_linear :
    S.P_plus.comp S.P_plus = S.P_plus := by
  ext x
  simpa using S.P_plus_idempotent x

theorem P_minus_comp_P_minus_linear :
    S.P_minus.comp S.P_minus = S.P_minus := by
  ext x
  simpa using S.P_minus_idempotent x

theorem P_plus_comp_P_minus_linear :
    S.P_plus.comp S.P_minus = 0 := by
  ext x
  exact S.P_plus_comp_P_minus x

theorem P_minus_comp_P_plus_linear :
    S.P_minus.comp S.P_plus = 0 := by
  ext x
  exact S.P_minus_comp_P_plus x

theorem P_plus_add_P_minus :
    S.P_plus + S.P_minus = (LinearMap.id : L →ₗ[R] L) := by
  ext x
  simpa [LinearMap.add_apply] using (S.cartan_decomposition x).symm

theorem disjoint_𝔨_𝔭 :
    Disjoint S.𝔨 S.𝔭 := by
  refine Submodule.disjoint_def.2 ?_
  intro x hxk hxp
  have hx_plus : S.P_plus x = x := S.P_plus_eq_self_of_mem_𝔨 hxk
  have hx_zero : S.P_plus x = 0 := S.P_plus_eq_zero_of_mem_𝔭 hxp
  calc
    x = S.P_plus x := hx_plus.symm
    _ = 0 := hx_zero

theorem sup_𝔨_𝔭_eq_top :
    S.𝔨 ⊔ S.𝔭 = ⊤ := by
  refine Submodule.eq_top_iff'.2 ?_
  intro x
  refine Submodule.mem_sup.2 ?_
  refine ⟨S.P_plus x, S.P_plus_mem_𝔨 x, S.P_minus x, S.P_minus_mem_𝔭 x, ?_⟩
  simpa using (S.cartan_decomposition x).symm

theorem isCompl_𝔨_𝔭 :
    IsCompl S.𝔨 S.𝔭 :=
  ⟨S.disjoint_𝔨_𝔭, by
    simpa [codisjoint_iff] using S.sup_𝔨_𝔭_eq_top⟩

end Half

/-!
## Symmetric pair bracket relations
-/

theorem bracket_k_k {x y : L} (hx : x ∈ S.𝔨) (hy : y ∈ S.𝔨) :
    ⁅x, y⁆ ∈ S.𝔨 := by
  have hx' : S.θ x = x := (S.mem_𝔨_iff x).1 hx
  have hy' : S.θ y = y := (S.mem_𝔨_iff y).1 hy
  refine (S.mem_𝔨_iff ⁅x, y⁆).2 ?_
  simp [LieEquiv.map_lie, hx', hy']

theorem bracket_k_p {x y : L} (hx : x ∈ S.𝔨) (hy : y ∈ S.𝔭) :
    ⁅x, y⁆ ∈ S.𝔭 := by
  have hx' : S.θ x = x := (S.mem_𝔨_iff x).1 hx
  have hy' : S.θ y = -y := (S.mem_𝔭_iff y).1 hy
  refine (S.mem_𝔭_iff ⁅x, y⁆).2 ?_
  simp [LieEquiv.map_lie, hx', hy']

theorem bracket_p_p {x y : L} (hx : x ∈ S.𝔭) (hy : y ∈ S.𝔭) :
    ⁅x, y⁆ ∈ S.𝔨 := by
  have hx' : S.θ x = -x := (S.mem_𝔭_iff x).1 hx
  have hy' : S.θ y = -y := (S.mem_𝔭_iff y).1 hy
  refine (S.mem_𝔨_iff ⁅x, y⁆).2 ?_
  simp [LieEquiv.map_lie, hx', hy']

/-!
## Lie triple system on 𝔭
-/

def triple (x y z : S.𝔭) : S.𝔭 :=
  ⟨⁅⁅(x : L), (y : L)⁆, (z : L)⁆,
    by
      have h₁ : ⁅(x : L), (y : L)⁆ ∈ S.𝔨 := S.bracket_p_p x.property y.property
      exact S.bracket_k_p h₁ z.property⟩

def curvature (x y z : S.𝔭) : S.𝔭 :=
  -S.triple x y z

/-- The adjoint action of 𝔨 on 𝔭. -/
def ad_k_on_p (x : S.𝔨) : S.𝔭 →ₗ[R] S.𝔭 where
  toFun y := ⟨⁅(x : L), (y : L)⁆, S.bracket_k_p x.property y.property⟩
  map_add' y₁ y₂ := by
    ext
    simp
  map_smul' r y := by
    ext
    simp

/-- A symmetric Lie algebra is isotropy irreducible if the adjoint action of 𝔨 on 𝔭
    admits no nontrivial proper 𝔨-invariant submodules. -/
def IsotropyIrreducible (S : SymmetricLieAlgebra R L) : Prop :=
  ∀ (V : Submodule R S.𝔭), (∀ (x : S.𝔨), ∀ (v : S.𝔭), v ∈ V → S.ad_k_on_p x v ∈ V) →
    V = ⊥ ∨ V = ⊤

/-- A bilinear form on 𝔭 is 𝔨-invariant if it is invariant under the adjoint action of 𝔨. -/
def IsKInvariant (S : SymmetricLieAlgebra R L) (Φ : LinearMap.BilinForm R S.𝔭) : Prop :=
  ∀ (x : S.𝔨) (v w : S.𝔭), Φ (S.ad_k_on_p x v) w + Φ v (S.ad_k_on_p x w) = 0

/-!
Schur-type proportionality on `𝔭` is deferred at this layer.
-/

end SymmetricLieAlgebra

end Symmetric

/-!
# Killing Form Layer
-/

section Killing

variable [CommRing R]
variable [LieRing L] [LieAlgebra R L]
variable [Module.Free R L] [Module.Finite R L]

namespace SymmetricLieAlgebra

variable (S : SymmetricLieAlgebra R L)

noncomputable abbrev B (_S : SymmetricLieAlgebra R L) : LinearMap.BilinForm R L :=
  killingForm R L

omit [Module.Free R L] [Module.Finite R L] in
theorem killing_invariant (x y : L) :
    S.B (S.θ x) (S.θ y) = S.B x y := by
  exact LieAlgebra.killingForm_of_equiv_apply (R := R) (L := L) (L' := L) S.θ x y

section Orthogonal

variable [Invertible (2 : R)]

omit [Module.Free R L] [Module.Finite R L] in
theorem killing_orthogonal {k p : L} (hk : k ∈ S.𝔨) (hp : p ∈ S.𝔭) :
    S.B k p = 0 := by
  have hk' : S.θ k = k := (S.mem_𝔨_iff k).1 hk
  have hp' : S.θ p = -p := (S.mem_𝔭_iff p).1 hp

  have hinv : S.B (S.θ k) (S.θ p) = S.B k p := S.killing_invariant k p
  have h1 : S.B k (-p) = S.B k p := by
    simpa [hk', hp'] using hinv

  have hEq : -(S.B k p) = S.B k p := by
    calc
      -(S.B k p) = S.B k (-p) := by
        simp [map_neg]
      _ = S.B k p := h1

  have hx : S.B k p = -S.B k p := by
    simpa using hEq.symm

  have hsum : S.B k p + S.B k p = 0 :=
    (eq_neg_iff_add_eq_zero).1 hx

  have hmul : (2 : R) * S.B k p = 0 := by
    calc
      (2 : R) * S.B k p = S.B k p + S.B k p := by simp [two_mul]
      _ = 0 := hsum

  have hcancel : (⅟ (2 : R)) * ((2 : R) * S.B k p) = S.B k p := by
    simp

  calc
    S.B k p = (⅟ (2 : R)) * ((2 : R) * S.B k p) := hcancel.symm
    _ = (⅟ (2 : R)) * 0 := by simp [hmul]
    _ = 0 := by simp

end Orthogonal

end SymmetricLieAlgebra

end Killing

/-!
# Extensions: Cartan Involution, Cartan Form, and Ordered Signature Interface
-/

section CartanExtensions

variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [Module.Free R L] [Module.Finite R L]

namespace SymmetricLieAlgebra

/-- A Cartan involutive Lie algebra: symmetric Lie algebra + nondegenerate Killing form. -/
structure CartanLieAlgebra (R : Type u) (L : Type v)
    [CommRing R] [LieRing L] [LieAlgebra R L]
    [Module.Free R L] [Module.Finite R L]
    extends SymmetricLieAlgebra R L where
  killing_nondegenerate : (killingForm R L).Nondegenerate

variable (S : SymmetricLieAlgebra R L)

/-- Cartan form as a bilinear form object: `B_θ(x,y) = -B(x, θ y)`. -/
noncomputable def cartanForm : LinearMap.BilinForm R L :=
  LinearMap.mk₂ R
    (fun x y => -(killingForm R L x (S.θ y)))
    (by
      intro x₁ x₂ y
      simp [map_add, add_comm])
    (by
      intro a x y
      simp [map_smul])
    (by
      intro x y₁ y₂
      simp [map_add, add_comm])
    (by
      intro a x y
      simp [map_smul])

/-- Compatibility scalar-evaluation alias for the Cartan form. -/
noncomputable abbrev cartanFormScalar (x y : L) : R :=
  S.cartanForm x y

omit [Module.Free R L] [Module.Finite R L] in
@[simp] lemma cartanForm_apply (x y : L) :
    S.cartanForm x y = -(killingForm R L x (S.θ y)) :=
  rfl

end SymmetricLieAlgebra

end CartanExtensions

section OrderedSignature

variable [CommRing R] [Preorder R] [LieRing L] [LieAlgebra R L]
variable [Module.Free R L] [Module.Finite R L]

namespace SymmetricLieAlgebra

variable (S : SymmetricLieAlgebra R L)

/-- Noncompact sign convention interface:
`B_θ` is nonnegative on `𝔭` and nonpositive on `𝔨`. -/
structure CartanSignature where
  pos_on_p : ∀ x : L, x ∈ S.𝔭 → 0 ≤ S.cartanForm x x
  neg_on_k : ∀ x : L, x ∈ S.𝔨 → S.cartanForm x x ≤ 0

end SymmetricLieAlgebra

end OrderedSignature

end InfoGeometry.Core.Generic
