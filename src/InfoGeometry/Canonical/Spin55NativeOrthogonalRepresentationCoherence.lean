import InfoGeometry.Canonical.Spin55NativeOrthogonalGroupKernelExact
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Clifford.Clifford55

/-!
# Coherence of the two native Spin orthogonal readouts

The Clifford layer exposes the Spin action both as an element of the native
orthogonal subgroup and directly as a quadratic isometry.  This owner records
that these are the same multiplicative representation after transport through
`orthogonalGroup55MulEquiv`.  It does not assert surjectivity, a determinant
statement, or a double-cover theorem.
-/

theorem orthogonalGroup55MulEquiv_comp_spinActionOrthogonalHom_eq
    : orthogonalGroup55MulEquiv.toMonoidHom.comp spinActionOrthogonalHom =
        spinNativeOrthogonalAction := by
  apply MonoidHom.ext
  intro g
  rw [MonoidHom.comp_apply, spinActionOrthogonalHom_apply,
    spinNativeOrthogonalAction_apply]
  rfl

@[simp] theorem orthogonalGroup55MulEquiv_spinActionOrthogonalHom_apply
    (g : Spin55) :
    orthogonalGroup55MulEquiv (spinActionOrthogonalHom g) =
      spinNativeOrthogonalAction g := by
  change
    (orthogonalGroup55MulEquiv.toMonoidHom.comp spinActionOrthogonalHom) g =
      spinNativeOrthogonalAction g
  rw [orthogonalGroup55MulEquiv_comp_spinActionOrthogonalHom_eq]

end InfoGeometry.Clifford.Clifford55
