import Mathlib

/-!
# Glide-symmetric `ℤ₂` invariant anchors

Finite linear-algebra anchor for the Klein-bottle / `pg` glide picture.  If a
Hamiltonian commutes with an involutive glide operator `Θ`, then the `+1` and
`-1` glide eigensectors are invariant under the Hamiltonian.
-/

noncomputable section

namespace GlideSymmetricInvariant

variable {K V : Type*} [Ring K] [AddCommGroup V] [Module K V]

/-- A glide-reflection operator represented as a linear involution. -/
structure GlideOperator where
  theta : V →ₗ[K] V
  involution : theta.comp theta = LinearMap.id

/-- Hamiltonian/glide commutation at a high-symmetry line. -/
def IsGlideSymmetric (H : V →ₗ[K] V) (g : GlideOperator (K := K) (V := V)) : Prop :=
  H.comp g.theta = g.theta.comp H

/-- Positive `+1` eigenspace of the glide. -/
def eigenspacePlus (g : GlideOperator (K := K) (V := V)) : Submodule K V :=
  LinearMap.ker (g.theta - LinearMap.id)

/-- Negative `-1` eigenspace of the glide. -/
def eigenspaceMinus (g : GlideOperator (K := K) (V := V)) : Submodule K V :=
  LinearMap.ker (g.theta + LinearMap.id)

/-- A glide-symmetric Hamiltonian preserves the `+1` glide eigenspace. -/
theorem hamiltonian_preserves_plus_eigenspace
    (H : V →ₗ[K] V) (g : GlideOperator (K := K) (V := V))
    (h_symm : IsGlideSymmetric H g) :
    ∀ x ∈ eigenspacePlus g, H x ∈ eigenspacePlus g := by
  intro x hx
  simp [eigenspacePlus, LinearMap.mem_ker] at hx ⊢
  have htheta : g.theta x = x := sub_eq_zero.mp hx
  have h_comm := congrArg (fun T : V →ₗ[K] V => T x) h_symm
  simp [LinearMap.comp_apply] at h_comm
  rw [htheta] at h_comm
  exact sub_eq_zero.mpr h_comm.symm

/-- A glide-symmetric Hamiltonian preserves the `-1` glide eigenspace. -/
theorem hamiltonian_preserves_minus_eigenspace
    (H : V →ₗ[K] V) (g : GlideOperator (K := K) (V := V))
    (h_symm : IsGlideSymmetric H g) :
    ∀ x ∈ eigenspaceMinus g, H x ∈ eigenspaceMinus g := by
  intro x hx
  simp [eigenspaceMinus, LinearMap.mem_ker] at hx ⊢
  have htheta : g.theta x = -x := by
    exact eq_neg_of_add_eq_zero_left hx
  have h_comm := congrArg (fun T : V →ₗ[K] V => T x) h_symm
  simp [LinearMap.comp_apply] at h_comm
  rw [← h_comm, htheta, map_neg]
  simp


end GlideSymmetricInvariant
