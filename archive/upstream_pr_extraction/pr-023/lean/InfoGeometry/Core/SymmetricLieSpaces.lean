import InfoGeometry.Core.SymmetricLieGeneric

/-!
# Core Symmetric Lie Spaces

Lie-level core façade over the generic symmetric Lie algebra layer.

This file is intentionally Lie-level:
- involutive Lie algebra automorphisms;
- `𝔨/𝔭` Cartan decomposition;
- half-projectors when `2` is invertible;
- symmetric-pair bracket relations;
- Lie triple system on `𝔭`;
- Killing / Cartan-form / signature interfaces.

A future Lie-group bridge should sit above this layer.
-/

open scoped Invertible

universe u v

namespace InfoGeometry.Core
namespace SymmetricLieSpaces

variable {R : Type u} {L : Type v}

/-- Core alias for symmetric Lie algebras. -/
abbrev SymmetricLieAlgebra (R : Type u) (L : Type v)
    [CommRing R] [LieRing L] [LieAlgebra R L] :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra R L

/-! ## Symmetric Layer -/

section Symmetric

variable [CommRing R]
variable [LieRing L] [LieAlgebra R L]

namespace SymmetricLieAlgebra

variable (S : SymmetricLieAlgebra R L)

/-- Core alias for the involutive Lie automorphism. -/
abbrev theta : L ≃ₗ⁅R⁆ L := S.θ

@[simp] lemma involution_apply (x : L) :
    S.theta (S.theta x) = x :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.involution_apply S x

/-- Core alias for the `+1` Cartan submodule. -/
abbrev k : Submodule R L :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.𝔨 S

/-- Core alias for the `-1` Cartan submodule. -/
abbrev p : Submodule R L :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.𝔭 S

@[simp] lemma mem_k_iff (x : L) :
    x ∈ S.k ↔ S.theta x = x :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.mem_𝔨_iff S x

@[simp] lemma mem_p_iff (x : L) :
    x ∈ S.p ↔ S.theta x = -x :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.mem_𝔭_iff S x

section Half

variable [Invertible (2 : R)]

/-- Core alias for the `+1` eigenspace projector. -/
abbrev Pplus : L →ₗ[R] L :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.P_plus S

/-- Core alias for the `-1` eigenspace projector. -/
abbrev Pminus : L →ₗ[R] L :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.P_minus S

@[simp] lemma Pplus_apply (x : L) :
    S.Pplus x = (⅟ (2 : R)) • (x + S.theta x) :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.P_plus_apply S x

@[simp] lemma Pminus_apply (x : L) :
    S.Pminus x = (⅟ (2 : R)) • (x - S.theta x) :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.P_minus_apply S x

lemma Pplus_mem_k (x : L) :
    S.Pplus x ∈ S.k :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.P_plus_mem_𝔨 S x

lemma Pminus_mem_p (x : L) :
    S.Pminus x ∈ S.p :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.P_minus_mem_𝔭 S x

lemma Pplus_eq_self_of_mem_k {x : L} (hx : x ∈ S.k) :
    S.Pplus x = x :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.P_plus_eq_self_of_mem_𝔨 S hx

lemma Pminus_eq_zero_of_mem_k {x : L} (hx : x ∈ S.k) :
    S.Pminus x = 0 :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.P_minus_eq_zero_of_mem_𝔨 S hx

lemma Pplus_eq_zero_of_mem_p {x : L} (hx : x ∈ S.p) :
    S.Pplus x = 0 :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.P_plus_eq_zero_of_mem_𝔭 S hx

lemma Pminus_eq_self_of_mem_p {x : L} (hx : x ∈ S.p) :
    S.Pminus x = x :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.P_minus_eq_self_of_mem_𝔭 S hx

lemma Pplus_idempotent (x : L) :
    S.Pplus (S.Pplus x) = S.Pplus x :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.P_plus_idempotent S x

lemma Pminus_idempotent (x : L) :
    S.Pminus (S.Pminus x) = S.Pminus x :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.P_minus_idempotent S x

lemma Pplus_comp_Pminus (x : L) :
    S.Pplus (S.Pminus x) = 0 :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.P_plus_comp_P_minus S x

lemma Pminus_comp_Pplus (x : L) :
    S.Pminus (S.Pplus x) = 0 :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.P_minus_comp_P_plus S x

theorem cartan_decomposition (x : L) :
    x = S.Pplus x + S.Pminus x :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.cartan_decomposition S x

theorem Pplus_comp_Pplus_linear :
    S.Pplus.comp S.Pplus = S.Pplus :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.P_plus_comp_P_plus_linear S

theorem Pminus_comp_Pminus_linear :
    S.Pminus.comp S.Pminus = S.Pminus :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.P_minus_comp_P_minus_linear S

theorem Pplus_comp_Pminus_linear :
    S.Pplus.comp S.Pminus = 0 :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.P_plus_comp_P_minus_linear S

theorem Pminus_comp_Pplus_linear :
    S.Pminus.comp S.Pplus = 0 :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.P_minus_comp_P_plus_linear S

theorem Pplus_add_Pminus :
    S.Pplus + S.Pminus = (LinearMap.id : L →ₗ[R] L) :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.P_plus_add_P_minus S

theorem isCompl_k_p :
    IsCompl S.k S.p :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.isCompl_𝔨_𝔭 S

end Half

theorem bracket_k_k {x y : L} (hx : x ∈ S.k) (hy : y ∈ S.k) :
    ⁅x, y⁆ ∈ S.k :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.bracket_k_k S hx hy

theorem bracket_k_p {x y : L} (hx : x ∈ S.k) (hy : y ∈ S.p) :
    ⁅x, y⁆ ∈ S.p :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.bracket_k_p S hx hy

theorem bracket_p_p {x y : L} (hx : x ∈ S.p) (hy : y ∈ S.p) :
    ⁅x, y⁆ ∈ S.k :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.bracket_p_p S hx hy

/-- Core alias for the Lie triple product on `𝔭`. -/
abbrev triple (x y z : S.p) : S.p :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.triple S x y z

/-- Core alias for the curvature operator on `𝔭`. -/
abbrev curvature (x y z : S.p) : S.p :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.curvature S x y z

/-- Core alias for the isotropy representation of `𝔨` on `𝔭`. -/
abbrev ad_k_on_p (x : S.k) : S.p →ₗ[R] S.p :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.ad_k_on_p S x

/-- Core alias for isotropy irreducibility. -/
abbrev IsotropyIrreducible : Prop :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.IsotropyIrreducible S

/-- Core alias for `𝔨`-invariant bilinear forms on `𝔭`. -/
abbrev IsKInvariant (Φ : LinearMap.BilinForm R S.p) : Prop :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.IsKInvariant S Φ

end SymmetricLieAlgebra

end Symmetric

/-! ## Killing Layer -/

section Killing

variable [CommRing R]
variable [LieRing L] [LieAlgebra R L]
variable [Module.Free R L] [Module.Finite R L]

/-- Core alias for Cartan Lie algebras. -/
abbrev CartanLieAlgebra :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.CartanLieAlgebra R L

namespace SymmetricLieAlgebra

variable (S : SymmetricLieAlgebra R L)

/-- Core alias for the Killing form. -/
noncomputable abbrev B : LinearMap.BilinForm R L :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.B S

omit [Module.Free R L] [Module.Finite R L] in
theorem killing_invariant (x y : L) :
    S.B (S.θ x) (S.θ y) = S.B x y :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.killing_invariant S x y

section Orthogonal

variable [Invertible (2 : R)]

omit [Module.Free R L] [Module.Finite R L] in
theorem killing_orthogonal {k p : L} (hk : k ∈ S.k) (hp : p ∈ S.p) :
    S.B k p = 0 :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.killing_orthogonal S hk hp

end Orthogonal

/-- Core alias for the Cartan form object. -/
noncomputable abbrev cartanForm : LinearMap.BilinForm R L :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.cartanForm S

/-- Compatibility scalar readout of the Cartan bilinear form. -/
noncomputable abbrev cartanFormScalar (x y : L) : R :=
  S.cartanForm x y

omit [Module.Free R L] [Module.Finite R L] in
@[simp] lemma cartanForm_apply (x y : L) :
    S.cartanForm x y = -(killingForm R L x (S.θ y)) :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.cartanForm_apply S x y

end SymmetricLieAlgebra

end Killing

/-! ## Ordered Signature -/

section OrderedSignature

variable [CommRing R] [Preorder R]
variable [LieRing L] [LieAlgebra R L]
variable [Module.Free R L] [Module.Finite R L]

namespace SymmetricLieAlgebra

/-- Core alias for Cartan signature assumptions. -/
abbrev CartanSignature (S : SymmetricLieAlgebra R L) :=
  InfoGeometry.Core.Generic.SymmetricLieAlgebra.CartanSignature S

end SymmetricLieAlgebra

end OrderedSignature

end SymmetricLieSpaces
end InfoGeometry.Core
