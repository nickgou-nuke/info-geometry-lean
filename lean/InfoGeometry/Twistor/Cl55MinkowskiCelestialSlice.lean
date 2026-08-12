import InfoGeometry.Clifford.Clifford55
import InfoGeometry.Twistor.NullProjective

/-!
# A Lorentzian celestial slice of the projective `Q55` null boundary

This owner embeds the concrete Minkowski carrier `ℝ × ℝ³` into the native
`(5,5)` quadratic carrier.  On this slice, `Q55` restricts to
`t² - ∑ i, x i²`.  Normalizing `t = 1` identifies the null equation with
the ordinary unit two-sphere equation and supplies an injective map into the
native projective-null subtype `TwistorSpace Q55`.

No homeomorphism with `ℂP¹`, spherical-braid identification, or monodromy
claim is made here.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

namespace InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice

open BigOperators
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor

/-- The concrete `(1,3)` coordinate carrier. -/
abbrev Minkowski13 := ℝ × (Fin 3 → ℝ)

/-- Embed one positive time coordinate and three negative spatial coordinates
into the native `(5,5)` carrier. -/
def minkowskiSlice : Minkowski13 →ₗ[ℝ] V55 where
  toFun z :=
    (![z.1, 0, 0, 0, 0], ![z.2 0, z.2 1, z.2 2, 0, 0])
  map_add' z w := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp
  map_smul' c z := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp

theorem minkowskiSlice_injective : Function.Injective minkowskiSlice := by
  intro z w h
  apply Prod.ext
  · exact congrFun (congrArg Prod.fst h) 0
  · funext i
    fin_cases i
    · exact congrFun (congrArg Prod.snd h) 0
    · exact congrFun (congrArg Prod.snd h) 1
    · exact congrFun (congrArg Prod.snd h) 2

/-- The native split quadratic form restricts to the Minkowski interval on
the slice. -/
@[simp] theorem Q55_minkowskiSlice (z : Minkowski13) :
    Q55 (minkowskiSlice z) = z.1 ^ 2 - ∑ i : Fin 3, z.2 i ^ 2 := by
  simp [minkowskiSlice, Q55_apply, Fin.sum_univ_succ]

/-- The normalized celestial two-sphere, written with its Euclidean equation
rather than an ambient projective alias. -/
abbrev CelestialSphere := {x : Fin 3 → ℝ // ∑ i : Fin 3, x i ^ 2 = 1}

/-- The normalized null representative `(1,x)` in the native `Q55` carrier. -/
def celestialVector (x : CelestialSphere) : V55 :=
  minkowskiSlice (1, x.1)

theorem celestialVector_ne_zero (x : CelestialSphere) :
    celestialVector x ≠ 0 := by
  intro h
  have ht := congrFun (congrArg Prod.fst h) 0
  norm_num [celestialVector, minkowskiSlice] at ht

@[simp] theorem Q55_celestialVector (x : CelestialSphere) :
    Q55 (celestialVector x) = 0 := by
  rw [celestialVector, Q55_minkowskiSlice]
  simp [x.2]

/-- A normalized celestial direction defines an actual point of the native
projective `Q55` null boundary. -/
def celestialNullPoint (x : CelestialSphere) : TwistorSpace Q55 :=
  twistorMk Q55 (celestialVector x) (celestialVector_ne_zero x)
    (Q55_celestialVector x)

/-- Time normalization removes the remaining projective scaling ambiguity,
so distinct celestial directions give distinct projective-null points. -/
theorem celestialNullPoint_injective :
    Function.Injective celestialNullPoint := by
  intro x y hxy
  have hproj :
      Projectivization.mk ℝ (celestialVector x) (celestialVector_ne_zero x) =
        Projectivization.mk ℝ (celestialVector y) (celestialVector_ne_zero y) :=
    congrArg Subtype.val hxy
  rcases (Projectivization.mk_eq_mk_iff ℝ
      (celestialVector x) (celestialVector y)
      (celestialVector_ne_zero x) (celestialVector_ne_zero y)).1 hproj with
    ⟨c, hc⟩
  rw [Units.smul_def] at hc
  have ht := congrFun (congrArg Prod.fst hc) 0
  have hc_one : (c : ℝ) = 1 := by
    simpa [celestialVector, minkowskiSlice] using ht
  have hv : celestialVector x = celestialVector y := by
    have : celestialVector y = celestialVector x := by
      simpa [hc_one] using hc
    exact this.symm
  have hpair : ((1 : ℝ), x.1) = ((1 : ℝ), y.1) :=
    minkowskiSlice_injective hv
  exact Subtype.ext (congrArg Prod.snd hpair)

end InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice
