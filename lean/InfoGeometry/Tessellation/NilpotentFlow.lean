import InfoGeometry.Tessellation.Corner
import Mathlib.Tactic

/-!
# Square-zero lightray flows

A square-zero lightray generates a concrete unipotent transport `1 + N` with
inverse `1 - N`.  This is the nilpotent-flow side of the tessellation picture;
it is separate from the diagonal determinant/exponential H¹ theorem.
-/

namespace InfoGeometry.Tessellation

/-- A square-zero element generates the unit `1 + N` with inverse `1 - N`. -/
def oneAddSquareZeroUnit {A : Type*} [Ring A] (N : A) (hN : N * N = 0) : Aˣ where
  val := 1 + N
  inv := 1 - N
  val_inv := by
    noncomm_ring [hN]
  inv_val := by
    noncomm_ring [hN]

@[simp]
theorem oneAddSquareZeroUnit_val
    {A : Type*} [Ring A] (N : A) (hN : N * N = 0) :
    (oneAddSquareZeroUnit N hN : A) = 1 + N :=
  rfl

/-- The inverse of the square-zero unipotent is `1 - N`. -/
theorem oneAddSquareZeroUnit_inv_val
    {A : Type*} [Ring A] (N : A) (hN : N * N = 0) :
    (((oneAddSquareZeroUnit N hN)⁻¹ : Aˣ) : A) = 1 - N :=
  rfl

/--
If two square-zero boundary modes anticommute, then their ordered bivector is
square-zero.
-/
theorem majoranaBivector_nilpotent
    {A : Type*} [Ring A] (N₁ N₂ : A)
    (h₁ : N₁ * N₁ = 0) (h₂ : N₂ * N₂ = 0)
    (h₁₂ : N₁ * N₂ + N₂ * N₁ = 0) :
    (N₁ * N₂) * (N₁ * N₂) = 0 := by
  have hAnti : N₂ * N₁ = -(N₁ * N₂) :=
    eq_neg_of_add_eq_zero_right h₁₂
  have hProd : N₁ * N₁ * N₂ * N₂ = 0 := by
    calc
      N₁ * N₁ * N₂ * N₂ = (N₁ * N₁) * (N₂ * N₂) := by
        simp only [mul_assoc]
      _ = 0 * 0 := by rw [h₁, h₂]
      _ = 0 := by rw [zero_mul]
  calc
    (N₁ * N₂) * (N₁ * N₂) = N₁ * (N₂ * N₁) * N₂ := by
      simp only [mul_assoc]
    _ = N₁ * (-(N₁ * N₂)) * N₂ := by rw [hAnti]
    _ = -(N₁ * N₁ * N₂ * N₂) := by
      rw [mul_neg, neg_mul]
      simp only [mul_assoc]
    _ = -0 := by rw [hProd]
    _ = 0 := by simp

/-- Real-scaled square-zero elements remain square-zero in a real algebra. -/
theorem realScaled_square_zero
    {A : Type*} [Ring A] [Algebra ℝ A]
    (P : A) (t : ℝ) (hP : P * P = 0) :
    ((algebraMap ℝ A t) * P) * ((algebraMap ℝ A t) * P) = 0 := by
  calc
    ((algebraMap ℝ A t) * P) * ((algebraMap ℝ A t) * P)
        = (algebraMap ℝ A t) * (P * (algebraMap ℝ A t)) * P := by
          simp only [mul_assoc]
    _ = (algebraMap ℝ A t) * ((algebraMap ℝ A t) * P) * P := by
          rw [(Algebra.commutes t P).symm]
    _ = ((algebraMap ℝ A t) * (algebraMap ℝ A t)) * (P * P) := by
          simp only [mul_assoc]
    _ = 0 := by rw [hP, mul_zero]

/-- Nilpotent Majorana braid coordinate `1 + t N₁N₂`. -/
def majoranaBraid {A : Type*} [Ring A] [Algebra ℝ A]
    (t : ℝ) (N₁ N₂ : A) : A :=
  1 + (algebraMap ℝ A t) * (N₁ * N₂)

/-- Inverse nilpotent Majorana braid coordinate `1 - t N₁N₂`. -/
def majoranaBraidInv {A : Type*} [Ring A] [Algebra ℝ A]
    (t : ℝ) (N₁ N₂ : A) : A :=
  1 - (algebraMap ℝ A t) * (N₁ * N₂)

/-- Right-inverse law for the finite nilpotent Majorana braid coordinate. -/
theorem majoranaBraid_mul_inv
    {A : Type*} [Ring A] [Algebra ℝ A]
    (N₁ N₂ : A)
    (h₁ : N₁ * N₁ = 0) (h₂ : N₂ * N₂ = 0)
    (h₁₂ : N₁ * N₂ + N₂ * N₁ = 0) (t : ℝ) :
    majoranaBraid t N₁ N₂ * majoranaBraidInv t N₁ N₂ = 1 := by
  unfold majoranaBraid majoranaBraidInv
  let P : A := N₁ * N₂
  have hP : P * P = 0 := by
    dsimp [P]
    exact majoranaBivector_nilpotent N₁ N₂ h₁ h₂ h₁₂
  let a : A := (algebraMap ℝ A t) * P
  have ha : a * a = 0 := by
    dsimp [a]
    exact realScaled_square_zero P t hP
  calc
    (1 + a) * (1 - a) = 1 - a * a := by noncomm_ring
    _ = 1 := by rw [ha, sub_zero]

/-- Left-inverse law for the finite nilpotent Majorana braid coordinate. -/
theorem majoranaBraid_inv_mul
    {A : Type*} [Ring A] [Algebra ℝ A]
    (N₁ N₂ : A)
    (h₁ : N₁ * N₁ = 0) (h₂ : N₂ * N₂ = 0)
    (h₁₂ : N₁ * N₂ + N₂ * N₁ = 0) (t : ℝ) :
    majoranaBraidInv t N₁ N₂ * majoranaBraid t N₁ N₂ = 1 := by
  unfold majoranaBraid majoranaBraidInv
  let P : A := N₁ * N₂
  have hP : P * P = 0 := by
    dsimp [P]
    exact majoranaBivector_nilpotent N₁ N₂ h₁ h₂ h₁₂
  let a : A := (algebraMap ℝ A t) * P
  have ha : a * a = 0 := by
    dsimp [a]
    exact realScaled_square_zero P t hP
  calc
    (1 - a) * (1 + a) = 1 - a * a := by noncomm_ring
    _ = 1 := by rw [ha, sub_zero]

/--
An incident lightray between orthogonal sectors generates a unipotent
transport unit.
-/
def IncidentLightray.flowUnit
    {A : Type*} [Ring A] {src tgt : Diamond A}
    (L : IncidentLightray A src tgt) (h_orthogonal : src.P * tgt.P = 0) : Aˣ :=
  oneAddSquareZeroUnit L.N (L.square_zero_of_orthogonal h_orthogonal)

@[simp]
theorem IncidentLightray.flowUnit_val
    {A : Type*} [Ring A] {src tgt : Diamond A}
    (L : IncidentLightray A src tgt) (h_orthogonal : src.P * tgt.P = 0) :
    (L.flowUnit h_orthogonal : A) = 1 + L.N :=
  rfl

/-- Incident lightray flow transports causal diamonds by unit conjugation. -/
def IncidentLightray.transportDiamond
    {A : Type*} [Ring A] {src tgt : Diamond A}
    (L : IncidentLightray A src tgt) (h_orthogonal : src.P * tgt.P = 0)
    (D : Diamond A) : Diamond A :=
  unitConjDiamond (L.flowUnit h_orthogonal) D

/-- Incident lightray flow transports corner membership. -/
theorem IncidentLightray.transport_mem_corner
    {A : Type*} [Ring A] {src tgt D : Diamond A}
    (L : IncidentLightray A src tgt) (h_orthogonal : src.P * tgt.P = 0)
    {x : A} (hx : IsInCorner D x) :
    IsInCorner (L.transportDiamond h_orthogonal D)
      (unitConjRing (L.flowUnit h_orthogonal) x) := by
  exact unitConjRing_mem_corner (L.flowUnit h_orthogonal) hx

end InfoGeometry.Tessellation
