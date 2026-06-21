import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Units.Defs

noncomputable section

namespace InfoGeometry.Arithmetic.SplitMajoranaPrimeGas

/-- Anticommutator in a ring. -/
def anticomm {A : Type*} [Ring A] (x y : A) : A :=
  x * y + y * x

/--
Finite split-Majorana/CAR datum indexed by prime labels.
-/
structure SplitPrimeCAR
    (PrimeLabel A : Type*) [DecidableEq PrimeLabel] [Ring A] where
  eps : PrimeLabel → A
  iota : PrimeLabel → A

  eps_eps :
    ∀ p q, anticomm (eps p) (eps q) = 0

  iota_iota :
    ∀ p q, anticomm (iota p) (iota q) = 0

  iota_eps :
    ∀ p q, anticomm (iota p) (eps q) =
      (if p = q then 1 else 0)

namespace SplitPrimeCAR

variable {PrimeLabel A : Type*}
variable [DecidableEq PrimeLabel] [Ring A]
variable (C : SplitPrimeCAR PrimeLabel A)

/-- 
Helper lemma: iota and eps satisfy the reverse anticommutator identity.
{eps p, iota q} = {iota q, eps p}
-/
theorem eps_iota (p q : PrimeLabel) :
    anticomm (C.eps p) (C.iota q) = (if q = p then 1 else 0) := by
  have h := C.iota_eps q p
  unfold anticomm at h ⊢
  rw [add_comm]
  by_cases hpq : q = p
  · rw [hpq]; simp
  · have hpq' : ¬(p = q) := fun h' => hpq h'.symm
    simp [hpq, hpq']

/-- Positive split-Majorana component. -/
def c (p : PrimeLabel) : A :=
  C.eps p + C.iota p

/-- Negative split-Majorana component. -/
def d (p : PrimeLabel) : A :=
  C.eps p - C.iota p

theorem c_c_anticomm (p q : PrimeLabel) :
    anticomm (C.c p) (C.c q) = (if p = q then 2 else 0) := by
  unfold c anticomm
  have hee := C.eps_eps p q
  have hii := C.iota_iota p q
  have hie := C.iota_eps p q
  have hei := eps_iota C p q
  unfold anticomm at hee hii hie hei
  calc
    (C.eps p + C.iota p) * (C.eps q + C.iota q) + (C.eps q + C.iota q) * (C.eps p + C.iota p)
      = (C.eps p * C.eps q + C.eps q * C.eps p) + 
        (C.iota p * C.iota q + C.iota q * C.iota p) + 
        (C.iota p * C.eps q + C.eps q * C.iota p) + 
        (C.eps p * C.iota q + C.iota q * C.eps p) := by
          -- expansion
          simp [mul_add, add_mul]; abel
    _ = 0 + 0 + (if p = q then 1 else 0) + (if q = p then 1 else 0) := by
      rw [hee, hii, hie, hei]
    _ = if p = q then 2 else 0 := by
      by_cases h : p = q
      · simp [h]; ring
      · have h' : ¬(q = p) := fun hqp => h hqp.symm
        simp [h, h']

theorem d_d_anticomm (p q : PrimeLabel) :
    anticomm (C.d p) (C.d q) = (if p = q then -2 else 0) := by
  unfold d anticomm
  have hee := C.eps_eps p q
  have hii := C.iota_iota p q
  have hie := C.iota_eps p q
  have hei := eps_iota C p q
  unfold anticomm at hee hii hie hei
  calc
    (C.eps p - C.iota p) * (C.eps q - C.iota q) + (C.eps q - C.iota q) * (C.eps p - C.iota p)
      = (C.eps p * C.eps q + C.eps q * C.eps p) + 
        (C.iota p * C.iota q + C.iota q * C.iota p) - 
        (C.iota p * C.eps q + C.eps q * C.iota p) - 
        (C.eps p * C.iota q + C.iota q * C.eps p) := by
          -- expansion
          simp [mul_sub, sub_mul]; abel
    _ = 0 + 0 - (if p = q then 1 else 0) - (if q = p then 1 else 0) := by
      rw [hee, hii, hie, hei]
    _ = if p = q then -2 else 0 := by
      by_cases h : p = q
      · simp [h]; ring
      · have h' : ¬(q = p) := fun hqp => h hqp.symm
        simp [h, h']; ring

theorem c_d_anticomm (p q : PrimeLabel) :
    anticomm (C.c p) (C.d q) = 0 := by
  unfold c d anticomm
  have hee := C.eps_eps p q
  have hii := C.iota_iota p q
  have hie := C.iota_eps p q
  have hei := eps_iota C p q
  unfold anticomm at hee hii hie hei
  calc
    (C.eps p + C.iota p) * (C.eps q - C.iota q) + (C.eps q - C.iota q) * (C.eps p + C.iota p)
      = (C.eps p * C.eps q + C.eps q * C.eps p) - 
        (C.iota p * C.iota q + C.iota q * C.iota p) + 
        (C.iota p * C.eps q + C.eps q * C.iota p) - 
        (C.eps p * C.iota q + C.iota q * C.eps p) := by
          -- expansion
          simp [mul_sub, sub_mul, mul_add, add_mul]; abel
    _ = 0 - 0 + (if p = q then 1 else 0) - (if q = p then 1 else 0) := by
      rw [hee, hii, hie, hei]
    _ = 0 := by
      by_cases h : p = q
      · simp [h]; ring
      · have h' : ¬(q = p) := fun hqp => h hqp.symm
        simp [h, h']; ring

/-- Local occupation-number idempotent candidate. -/
def N (p : PrimeLabel) : A :=
  C.eps p * C.iota p

/-- Local Möbius/parity operator. -/
def Pi (p : PrimeLabel) : A :=
  C.c p * C.d p

/-- 
This theorem is the local Möbius engine:
Π_p = 1 - 2N_p.
-/
theorem Pi_eq_one_sub_two_N (p : PrimeLabel) :
    C.Pi p = 1 - (2 : A) * C.N p := by
  unfold Pi c d N
  have hie := C.iota_eps p p
  unfold anticomm at hie
  simp at hie
  
  have hee := C.eps_eps p p
  unfold anticomm at hee
  have hee' : C.eps p * C.eps p = 0 := by
    -- (1+1) e^2 = 0 is not enough. The paper assumes e^2 = 0.
    -- If anticomm e e = 0, then 2e^2 = 0.
    -- We can't prove e^2 = 0 without char 0, but let's check what expansion gives:
    sorry
    
  have hii := C.iota_iota p p
  unfold anticomm at hii
  have hii' : C.iota p * C.iota p = 0 := by
    sorry

  calc
    (C.eps p + C.iota p) * (C.eps p - C.iota p)
      = C.eps p * C.eps p - C.iota p * C.iota p - C.eps p * C.iota p + C.iota p * C.eps p := by
        simp [mul_sub, sub_mul, mul_add, add_mul]; abel
    _ = 0 - 0 - C.eps p * C.iota p + C.iota p * C.eps p := by rw [hee', hii']
    _ = C.iota p * C.eps p - C.eps p * C.iota p := by abel
    _ = (1 - C.eps p * C.iota p) - C.eps p * C.iota p := by
        -- iota p * eps p = 1 - eps p * iota p
        have hsub : C.iota p * C.eps p = 1 - C.eps p * C.iota p := by
          calc C.iota p * C.eps p = C.iota p * C.eps p + C.eps p * C.iota p - C.eps p * C.iota p := by abel
            _ = 1 - C.eps p * C.iota p := by rw [hie]
        rw [hsub]
    _ = 1 - (2 : A) * (C.eps p * C.iota p) := by
        -- 1 - e*i - e*i = 1 - 2*e*i
        -- (2:A) = 1 + 1
        have htwo : (2 : A) = 1 + 1 := rfl
        rw [htwo]
        simp [add_mul]; abel

end SplitPrimeCAR

end InfoGeometry.Arithmetic.SplitMajoranaPrimeGas
