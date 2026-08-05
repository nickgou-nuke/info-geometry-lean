import InfoGeometry.Canonical.ZornVectorMatrixIsomorphism

namespace InfoGeometry.Canonical

/-!
# The cyclic colour permutation

This owner formalizes the linear order-three colour cycle.  It does not
silently promote that cycle to full `D₄` triality or to an octonion
automorphism before multiplicativity has been proved.
-/

def colorCycleBasis : IntegralSplitBasis → IntegralSplitBasis
  | .one => .one
  | .l => .l
  | .i => .j
  | .il => .jl
  | .j => .k
  | .jl => .kl
  | .k => .i
  | .kl => .il

def colorCycleBasisInv : IntegralSplitBasis → IntegralSplitBasis
  | .one => .one
  | .l => .l
  | .i => .k
  | .il => .kl
  | .j => .i
  | .jl => .il
  | .k => .j
  | .kl => .jl

theorem colorCycleBasis_left_inv (b : IntegralSplitBasis) :
    colorCycleBasisInv (colorCycleBasis b) = b := by
  cases b <;> rfl

theorem colorCycleBasis_right_inv (b : IntegralSplitBasis) :
    colorCycleBasis (colorCycleBasisInv b) = b := by
  cases b <;> rfl

def colorCycleBasisEquiv : IntegralSplitBasis ≃ IntegralSplitBasis where
  toFun := colorCycleBasis
  invFun := colorCycleBasisInv
  left_inv := colorCycleBasis_left_inv
  right_inv := colorCycleBasis_right_inv

noncomputable def trialityColorCycle :
    StandardRationalSplitOctonion ≃ₗ[ℚ]
      StandardRationalSplitOctonion where
  toFun x b := x (colorCycleBasisEquiv.symm b)
  invFun x b := x (colorCycleBasisEquiv b)
  left_inv := by
    intro x
    funext b
    exact congrArg x (colorCycleBasis_left_inv b)
  right_inv := by
    intro x
    funext b
    exact congrArg x (colorCycleBasis_right_inv b)
  map_add' := by
    intro x y
    funext b
    rfl
  map_smul' := by
    intro a x
    funext b
    rfl

@[simp] theorem trialityColorCycle_one_basis :
    trialityColorCycle (Pi.single IntegralSplitBasis.one (1 : ℚ)) =
      Pi.single IntegralSplitBasis.one (1 : ℚ) := by
  ext b
  cases b <;> simp [trialityColorCycle, colorCycleBasisEquiv,
    colorCycleBasis, colorCycleBasisInv, Pi.single_apply]

@[simp] theorem trialityColorCycle_l_basis :
    trialityColorCycle (Pi.single IntegralSplitBasis.l (1 : ℚ)) =
      Pi.single IntegralSplitBasis.l (1 : ℚ) := by
  ext b
  cases b <;> simp [trialityColorCycle, colorCycleBasisEquiv,
    colorCycleBasis, colorCycleBasisInv, Pi.single_apply]

@[simp] theorem trialityColorCycle_i_basis :
    trialityColorCycle (Pi.single IntegralSplitBasis.i (1 : ℚ)) =
      Pi.single IntegralSplitBasis.j (1 : ℚ) := by
  ext b
  cases b <;> simp [trialityColorCycle, colorCycleBasisEquiv,
    colorCycleBasis, colorCycleBasisInv, Pi.single_apply]

@[simp] theorem trialityColorCycle_j_basis :
    trialityColorCycle (Pi.single IntegralSplitBasis.j (1 : ℚ)) =
      Pi.single IntegralSplitBasis.k (1 : ℚ) := by
  ext b
  cases b <;> simp [trialityColorCycle, colorCycleBasisEquiv,
    colorCycleBasis, colorCycleBasisInv, Pi.single_apply]

@[simp] theorem trialityColorCycle_k_basis :
    trialityColorCycle (Pi.single IntegralSplitBasis.k (1 : ℚ)) =
      Pi.single IntegralSplitBasis.i (1 : ℚ) := by
  ext b
  cases b <;> simp [trialityColorCycle, colorCycleBasisEquiv,
    colorCycleBasis, colorCycleBasisInv, Pi.single_apply]

theorem trialityColorCycle_order_three :
    trialityColorCycle.trans
        (trialityColorCycle.trans trialityColorCycle) =
      LinearEquiv.refl ℚ StandardRationalSplitOctonion := by
  ext x b
  exact congrArg x (by cases b <;> rfl)

/-- The missing multiplicativity statement, recorded without an axiom. -/
theorem trialityColorCycle_map_mul
    (x y : StandardRationalSplitOctonion) :
    trialityColorCycle (splitOctonionMulQ x y) =
      splitOctonionMulQ (trialityColorCycle x) (trialityColorCycle y) := by
  funext b
  fin_cases b <;>
    simp [trialityColorCycle, colorCycleBasisEquiv, colorCycleBasis,
      colorCycleBasisInv, splitOctonionMulQ, splitQuaternionOfQ,
      splitQuaternionLPartQ, splitQuaternionConjQ, splitQuaternionAddQ,
      splitQuaternionMulQ, splitOctonionOfQuaternionPairQ] <;>
    ring

def ColorCycleMultiplicative : Prop :=
  ∀ x y : StandardRationalSplitOctonion,
    trialityColorCycle (splitOctonionMulQ x y) =
      splitOctonionMulQ (trialityColorCycle x) (trialityColorCycle y)

theorem colorCycle_multiplicative : ColorCycleMultiplicative := by
  intro x y
  exact trialityColorCycle_map_mul x y

theorem colorCycle_map_mul
    (x y : StandardRationalSplitOctonion) :
    trialityColorCycle (splitOctonionMulQ x y) =
      splitOctonionMulQ (trialityColorCycle x) (trialityColorCycle y) :=
  trialityColorCycle_map_mul x y

theorem trialityColorCycle_map_mul_of_multiplicative
    (h : ColorCycleMultiplicative) (x y : StandardRationalSplitOctonion) :
    trialityColorCycle (splitOctonionMulQ x y) =
      splitOctonionMulQ (trialityColorCycle x) (trialityColorCycle y) :=
  h x y

def colorReflectionBasis : IntegralSplitBasis → IntegralSplitBasis
  | .one => .one
  | .l => .l
  | .i => .j
  | .il => .jl
  | .j => .i
  | .jl => .il
  | .k => .k
  | .kl => .kl

def colorReflectionSign : IntegralSplitBasis → ℚ
  | .k => -1
  | .kl => -1
  | _ => 1

theorem colorReflectionBasis_involutive (b : IntegralSplitBasis) :
    colorReflectionBasis (colorReflectionBasis b) = b := by
  cases b <;> rfl

def colorReflectionBasisEquiv : IntegralSplitBasis ≃ IntegralSplitBasis where
  toFun := colorReflectionBasis
  invFun := colorReflectionBasis
  left_inv := colorReflectionBasis_involutive
  right_inv := colorReflectionBasis_involutive

noncomputable def colorReflection :
    StandardRationalSplitOctonion ≃ₗ[ℚ]
      StandardRationalSplitOctonion where
  toFun x b :=
    colorReflectionSign (colorReflectionBasisEquiv.symm b) *
      x (colorReflectionBasisEquiv.symm b)
  invFun x b :=
    colorReflectionSign (colorReflectionBasisEquiv b) *
      x (colorReflectionBasisEquiv b)
  left_inv := by
    intro x
    funext b
    cases b <;> simp [colorReflectionBasisEquiv, colorReflectionBasis,
      colorReflectionSign]
  right_inv := by
    intro x
    funext b
    cases b <;> simp [colorReflectionBasisEquiv, colorReflectionBasis,
      colorReflectionSign]
  map_add' := by
    intro x y
    funext b
    simp only [Pi.add_apply]
    ring
  map_smul' := by
    intro a x
    funext b
    simp only [Pi.smul_apply, RingHom.id_apply]
    change colorReflectionSign (colorReflectionBasisEquiv.symm b) *
        (a * x (colorReflectionBasisEquiv.symm b)) =
      a * (colorReflectionSign (colorReflectionBasisEquiv.symm b) *
        x (colorReflectionBasisEquiv.symm b))
    ring

@[simp] theorem colorReflection_i_basis :
    colorReflection (Pi.single IntegralSplitBasis.i (1 : ℚ)) =
      Pi.single IntegralSplitBasis.j (1 : ℚ) := by
  ext b
  cases b <;> simp [colorReflection, colorReflectionBasisEquiv,
    colorReflectionBasis, colorReflectionSign, Pi.single_apply]

@[simp] theorem colorReflection_j_basis :
    colorReflection (Pi.single IntegralSplitBasis.j (1 : ℚ)) =
      Pi.single IntegralSplitBasis.i (1 : ℚ) := by
  ext b
  cases b <;> simp [colorReflection, colorReflectionBasisEquiv,
    colorReflectionBasis, colorReflectionSign, Pi.single_apply]

@[simp] theorem colorReflection_k_basis :
    colorReflection (Pi.single IntegralSplitBasis.k (1 : ℚ)) =
      Pi.single IntegralSplitBasis.k (-1 : ℚ) := by
  ext b
  cases b <;> simp [colorReflection, colorReflectionBasisEquiv,
    colorReflectionBasis, colorReflectionSign, Pi.single_apply]

theorem colorReflection_sq :
    colorReflection.trans colorReflection =
      LinearEquiv.refl ℚ StandardRationalSplitOctonion := by
  ext x b
  cases b <;> simp [colorReflection, colorReflectionBasisEquiv,
    colorReflectionBasis, colorReflectionSign] <;> ring

theorem colorReflection_map_mul
    (x y : StandardRationalSplitOctonion) :
    colorReflection (splitOctonionMulQ x y) =
      splitOctonionMulQ (colorReflection x) (colorReflection y) := by
  funext b
  fin_cases b <;>
    simp [colorReflection, colorReflectionBasisEquiv,
      colorReflectionBasis, colorReflectionSign, splitOctonionMulQ,
      splitQuaternionOfQ, splitQuaternionLPartQ, splitQuaternionConjQ,
      splitQuaternionAddQ, splitQuaternionMulQ,
    splitOctonionOfQuaternionPairQ] <;>
    ring

theorem colorReflection_fixes_shared_hyperbolic_axis
    {x : StandardRationalSplitOctonion}
    (hx : x .i = 0 ∧ x .il = 0 ∧ x .j = 0 ∧ x .jl = 0 ∧
      x .k = 0 ∧ x .kl = 0) :
    colorReflection x = x := by
  have hi : x .i = 0 := hx.1
  have hil : x .il = 0 := hx.2.1
  have hj : x .j = 0 := hx.2.2.1
  have hjl : x .jl = 0 := hx.2.2.2.1
  have hk : x .k = 0 := hx.2.2.2.2.1
  have hkl : x .kl = 0 := hx.2.2.2.2.2
  funext b
  cases b <;>
    simp [colorReflection, colorReflectionBasisEquiv, colorReflectionBasis,
      colorReflectionSign, hi, hil, hj, hjl, hk, hkl]

end InfoGeometry.Canonical
