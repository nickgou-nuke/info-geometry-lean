import InfoGeometry.Canonical.Spin55NativeOrthogonalActionBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Clifford.Clifford55

/-!
# Kernel reduction for the native `Spin(5,5)` orthogonal action

This owner reduces membership in the kernel of the native action to the
pointwise fixed-vector condition.  It deliberately does not identify the
kernel with a sign subgroup, prove surjectivity, or assert a double-cover
theorem.
-/

theorem spinNativeOrthogonalAction_mem_kernel_iff
    (g : Spin55) :
    g ∈ (spinNativeOrthogonalAction).ker ↔
      ∀ v : V55, spinAction g v = v := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg v
    have hv := congrArg (fun e : Q55.IsometryEquiv Q55 => e v) hg
    change spinAction g v = v at hv
    exact hv
  · intro h
    apply DFunLike.ext
    intro v
    change spinAction g v = v
    exact h v

theorem spinNativeOrthogonalAction_mem_kernel_iff_pin_preimage
    (g : Spin55) :
    g ∈ (spinNativeOrthogonalAction).ker ↔
      spinToPin g ∈ (pinNativeOrthogonalAction).ker := by
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro hg
    rw [← spinNativeOrthogonalAction_eq_pinNativeOrthogonalAction g]
    exact hg
  · intro hg
    rw [spinNativeOrthogonalAction_eq_pinNativeOrthogonalAction g]
    exact hg

theorem spinToPinHom_injective :
    Function.Injective spinToPinHom := by
  intro g h hgh
  apply Subtype.ext
  exact congrArg (fun x : Pin55 => (x : Cl55)) hgh

theorem spinNativeOrthogonalAction_kernel_eq_pin_comap :
    (spinNativeOrthogonalAction).ker =
      Subgroup.comap spinToPinHom (pinNativeOrthogonalAction).ker := by
  apply Subgroup.ext
  intro g
  exact spinNativeOrthogonalAction_mem_kernel_iff_pin_preimage g

end InfoGeometry.Clifford.Clifford55
