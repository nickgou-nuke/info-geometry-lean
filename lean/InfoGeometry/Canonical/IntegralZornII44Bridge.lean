import InfoGeometry.Physics.SplitOctonionBraidSU3
import InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge

/-!
# Integral Zorn coordinates and the split even lattice of signature `(4,4)`

This owner file gives the integral carrier needed before making lattice or
charge-lattice claims about the canonical Zorn algebra. It uses four hyperbolic
pairs. The quadratic refinement is

`q(x,y) = ∑ i, x i * y i`,

while the associated symmetric integral pairing is

`B((x,y),(x',y')) = ∑ i, (x i * y' i + y i * x' i)`.

Consequently `B(z,z) = 2 * q(z)`, so the integral pairing is even. The
coordinate swap is the inverse Gram operator in the standard basis. We do not
identify this carrier with the positive-definite `D₄` root lattice.
-/

noncomputable section

namespace IntegralZornII44Bridge

open InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge

/-- Integral Zorn coordinates `(a,u,v,b)` with `u,v : Fin 3 → ℤ`. -/
abbrev IntegralZorn := ℤ × (Fin 3 → ℤ) × ((Fin 3 → ℤ) × ℤ)

def IntegralZorn.a (X : IntegralZorn) : ℤ := X.1
def IntegralZorn.u (X : IntegralZorn) : Fin 3 → ℤ := X.2.1
def IntegralZorn.v (X : IntegralZorn) : Fin 3 → ℤ := X.2.2.1
def IntegralZorn.b (X : IntegralZorn) : ℤ := X.2.2.2

/-- Four integral hyperbolic coordinate pairs. -/
abbrev II44Coordinates := (Fin 4 → ℤ) × (Fin 4 → ℤ)

/-- The quadratic refinement of the four-hyperbolic-plane pairing. -/
def ii44Quadratic (z : II44Coordinates) : ℤ :=
  ∑ i, z.1 i * z.2 i

/-- The symmetric integral pairing of four hyperbolic planes. -/
def ii44Pair (z w : II44Coordinates) : ℤ :=
  ∑ i, (z.1 i * w.2 i + z.2 i * w.1 i)

theorem ii44Pair_self (z : II44Coordinates) :
    ii44Pair z z = 2 * ii44Quadratic z := by
  simp [ii44Pair, ii44Quadratic, Fin.sum_univ_four]
  ring

theorem ii44Pair_even (z : II44Coordinates) : Even (ii44Pair z z) := by
  rw [ii44Pair_self]
  exact ⟨ii44Quadratic z, by ring⟩

/-- Coordinate swap, representing the hyperbolic Gram operator. -/
def ii44Dual : II44Coordinates →ₗ[ℤ] II44Coordinates where
  toFun z := (z.2, z.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ii44Dual_involutive (z : II44Coordinates) :
    ii44Dual (ii44Dual z) = z := rfl

theorem ii44Dual_bijective : Function.Bijective ii44Dual := by
  constructor
  · intro z w h
    simpa only [ii44Dual_involutive] using congrArg ii44Dual h
  · intro z
    exact ⟨ii44Dual z, ii44Dual_involutive z⟩

/-- Integral Zorn determinant. -/
def integralZornNorm (X : IntegralZorn) : ℤ :=
  X.a * X.b - ∑ i, X.u i * X.v i

/-- Place the four Zorn hyperbolic pairs into the standard split coordinates. -/
def integralZornToII44 : IntegralZorn ≃ₗ[ℤ] II44Coordinates where
  toFun X :=
    (![X.a, X.u 0, X.u 1, X.u 2],
     ![X.b, -X.v 0, -X.v 1, -X.v 2])
  invFun z :=
    (z.1 0, (fun i => z.1 i.succ), ((fun i => -z.2 i.succ), z.2 0))
  left_inv X := by
    rcases X with ⟨a, u, v, b⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext i
        fin_cases i <;> rfl
      · apply Prod.ext
        · funext i
          fin_cases i <;> simp [IntegralZorn.v]
        · rfl
  right_inv z := by
    rcases z with ⟨x, y⟩
    apply Prod.ext <;> funext i <;> fin_cases i <;>
      simp [IntegralZorn.a, IntegralZorn.u, IntegralZorn.v, IntegralZorn.b]
  map_add' X Y := by
    apply Prod.ext <;> funext i <;> fin_cases i <;>
      simp [IntegralZorn.a, IntegralZorn.u, IntegralZorn.v, IntegralZorn.b] <;>
      ring
  map_smul' n X := by
    apply Prod.ext <;> funext i <;> fin_cases i <;>
      simp [IntegralZorn.a, IntegralZorn.u, IntegralZorn.v, IntegralZorn.b]

/-- The integral Zorn determinant is the `II₄,₄` quadratic refinement. -/
theorem ii44Quadratic_integralZornToII44 (X : IntegralZorn) :
    ii44Quadratic (integralZornToII44 X) = integralZornNorm X := by
  simp [ii44Quadratic, integralZornToII44, integralZornNorm,
    IntegralZorn.a, IntegralZorn.u, IntegralZorn.v, IntegralZorn.b,
    Fin.sum_univ_four, Fin.sum_univ_three]
  ring

/-- Coordinatewise embedding of the integral lattice into the real Zorn carrier. -/
def integralToCoreZorn (X : IntegralZorn) : ZornCore.Zorn where
  a := X.a
  u := fun i => X.u i
  v := fun i => X.v i
  b := X.b

theorem integralToCoreZorn_injective : Function.Injective integralToCoreZorn := by
  intro X Y h
  apply Prod.ext
  · have hc : (X.a : ℝ) = (Y.a : ℝ) := by
      simpa [integralToCoreZorn] using congrArg ZornCore.Zorn.a h
    exact_mod_cast hc
  · apply Prod.ext
    · funext i
      have hc : (X.u i : ℝ) = (Y.u i : ℝ) := by
        simpa [integralToCoreZorn] using congrArg (fun Z => Z.u i) h
      exact_mod_cast hc
    · apply Prod.ext
      · funext i
        have hc : (X.v i : ℝ) = (Y.v i : ℝ) := by
          simpa [integralToCoreZorn] using congrArg (fun Z => Z.v i) h
        exact_mod_cast hc
      · have hc : (X.b : ℝ) = (Y.b : ℝ) := by
          simpa [integralToCoreZorn] using congrArg ZornCore.Zorn.b h
        exact_mod_cast hc

/-- The real Zorn determinant restricts to the integral lattice norm. -/
theorem integralToCoreZorn_det (X : IntegralZorn) :
    ZornCore.det (integralToCoreZorn X) = (integralZornNorm X : ℝ) := by
  simp [ZornCore.det, ZornCore.dot, integralToCoreZorn, integralZornNorm,
    IntegralZorn.a, IntegralZorn.u, IntegralZorn.v, IntegralZorn.b,
    Fin.sum_univ_three]

/-- The complete typed norm diagram from integral hyperbolic coordinates to
real and canonical complex Zorn coordinates. -/
theorem integral_ii44_real_complex_norm_bridge (X : IntegralZorn) :
    ii44Quadratic (integralZornToII44 X) = integralZornNorm X ∧
    ZornCore.det (integralToCoreZorn X) = (integralZornNorm X : ℝ) ∧
    InfoGeometry.Physics.SplitOctonionBraidSU3.zornNorm
        (coreToCanonical (integralToCoreZorn X)) =
      (integralZornNorm X : ℂ) := by
  refine ⟨ii44Quadratic_integralZornToII44 X,
    integralToCoreZorn_det X, ?_⟩
  rw [coreToCanonical_norm, integralToCoreZorn_det]
  norm_num

end IntegralZornII44Bridge

end noncomputable section
