import InfoGeometry.Lie.CanonicalZornDerivation

/-!
# The central scalar line is killed by canonical Zorn derivations

This owner records only the universal kernel statement forced by Leibniz.  It
does not claim that the kernel of a particular derivation is exactly the
scalar line.
-/

namespace InfoGeometry.Lie.CanonicalZornDerivation

open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

noncomputable instance : NonUnitalNonAssocSemiring CZ where
  left_distrib := fun X Y Z =>
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_add X Y Z
  right_distrib := fun X Y Z =>
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.add_mul X Y Z
  zero_mul := fun X =>
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul X
  mul_zero := fun X =>
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero X

theorem derivation_apply_one (D : canonicalZornDerivations) :
    D.1 (1 : CZ) = 0 := by
  apply canonicalVectorEquiv.injective
  change canonicalVectorEquiv (D.1 (1 : CZ)) = canonicalVectorEquiv (0 : CZ)
  have h := (canonicalToVectorDerivation D).map_one
  simpa only [canonicalToVectorDerivation_apply,
    canonicalVectorEquiv_symm_one, canonicalVectorEquiv_zero] using h

theorem derivation_apply_scalar (D : canonicalZornDerivations) (c : ℝ) :
    D.1 (c • (1 : CZ)) = 0 := by
  rw [D.1.map_smul, derivation_apply_one]
  simp

/-- The fixed-point set of a canonical derivation, as a carrier set. -/
def derivationFixedSet (D : canonicalZornDerivations) : Set CZ :=
  {X | D.1 X = 0}

theorem derivationFixedSet_one (D : canonicalZornDerivations) :
    (1 : CZ) ∈ derivationFixedSet D := by
  exact derivation_apply_one D

theorem derivationFixedSet_mul (D : canonicalZornDerivations)
    {X Y : CZ} (hX : X ∈ derivationFixedSet D)
    (hY : Y ∈ derivationFixedSet D) :
    X * Y ∈ derivationFixedSet D := by
  change D.1 (X * Y) = 0
  rw [D.property X Y, hX, hY, zero_mul, mul_zero, add_zero]

noncomputable def derivationKernelSubalgebra
    (D : canonicalZornDerivations) : NonUnitalSubalgebra ℝ CZ where
  carrier := derivationFixedSet D
  add_mem' := by
    intro X Y hX hY
    change D.1 (X + Y) = 0
    rw [D.1.map_add, hX, hY, add_zero]
  zero_mem' := by simp [derivationFixedSet]
  mul_mem' := by
    intro X Y hX hY
    exact derivationFixedSet_mul D hX hY
  smul_mem' := by
    intro c X hX
    change D.1 (c • X) = 0
    rw [D.1.map_smul, hX, smul_zero]

@[simp]
theorem mem_derivationKernelSubalgebra
    (D : canonicalZornDerivations) (X : CZ) :
    X ∈ derivationKernelSubalgebra D ↔ D.1 X = 0 := Iff.rfl

@[simp]
theorem one_mem_derivationKernelSubalgebra
    (D : canonicalZornDerivations) :
    (1 : CZ) ∈ derivationKernelSubalgebra D :=
  derivation_apply_one D

theorem scalar_mem_derivationKernelSubalgebra
    (D : canonicalZornDerivations) (c : ℝ) :
    c • (1 : CZ) ∈ derivationKernelSubalgebra D :=
  derivation_apply_scalar D c

end InfoGeometry.Lie.CanonicalZornDerivation
