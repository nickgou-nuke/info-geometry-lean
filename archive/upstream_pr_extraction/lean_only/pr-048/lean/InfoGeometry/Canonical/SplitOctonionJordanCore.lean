import InfoGeometry.Canonical.SplitOctonionJordanForm

/-!
# Explicit spin-factor Jordan core over the verified `(4,4)` form

This owner supplies the algebraic spin-factor model on `ℝ × MiddleCarrier`.
It does not identify that model with the full split-octonion carrier or with a
structure algebra; those are separate equivalence theorems.
-/

namespace InfoGeometry.Canonical.SplitOctonionJordanCore

open SplitOctonionJordanForm

abbrev SpinCarrier := ℝ × MiddleCarrier

def jordanMul (x y : SpinCarrier) : SpinCarrier :=
  (x.1 * y.1 + beta44 x.2 y.2,
    fun i => x.1 * y.2 i + y.1 * x.2 i)

instance : Mul SpinCarrier := ⟨jordanMul⟩

def spinUnit : SpinCarrier := (1, 0)

def scalarPart (x : SpinCarrier) : ℝ := x.1

def imaginaryPart (x : SpinCarrier) : MiddleCarrier := x.2

@[simp] theorem jordanMul_apply (x y : SpinCarrier) :
    x * y = jordanMul x y := rfl

theorem jordanMul_comm (x y : SpinCarrier) : x * y = y * x := by
  ext <;> simp [jordanMul, mul_comm, add_comm]

@[simp] theorem jordanMul_unit_left (x : SpinCarrier) :
    spinUnit * x = x := by
  ext <;> simp [spinUnit, jordanMul]

@[simp] theorem jordanMul_unit_right (x : SpinCarrier) :
    x * spinUnit = x := by
  rw [jordanMul_comm, jordanMul_unit_left]

theorem jordanMul_formula (a b : ℝ) (u v : MiddleCarrier) :
    (a, u) * (b, v) =
      (a * b + beta44 u v, fun i => a * v i + b * u i) := rfl

theorem jordan_spin_factor_formula (a b : ℝ) (u v : MiddleCarrier) :
    (a, u) * (b, v) =
      (a * b + beta44 u v, fun i => a * v i + b * u i) :=
  jordanMul_formula a b u v

theorem jordan_trace_decomposition (x : SpinCarrier) :
    x = (scalarPart x, 0) + (0, imaginaryPart x) := by
  rcases x with ⟨a, u⟩
  ext i <;> simp [scalarPart, imaginaryPart]

def normPolar (u v : MiddleCarrier) : ℝ := beta44 u v

theorem normPolar_symmetric (u v : MiddleCarrier) :
    normPolar u v = normPolar v u := beta44_symmetric u v

theorem normPolar_nondegenerate_left (u : MiddleCarrier)
    (hu : ∀ v, normPolar u v = 0) : u = 0 := by
  exact beta44_nondegenerate_left u hu

theorem normPolar_nondegenerate_right (v : MiddleCarrier)
    (hv : ∀ u, normPolar u v = 0) : v = 0 := by
  exact beta44_nondegenerate_right v hv

theorem jordanMul_jordan_identity (x y : SpinCarrier) :
    (x * y) * (x * x) = x * (y * (x * x)) := by
  rcases x with ⟨a, u⟩
  rcases y with ⟨b, v⟩
  ext i <;>
    simp [jordanMul, beta44_apply] <;>
    ring

theorem trace_free_square_zero (u v : MiddleCarrier) :
    (0, u) * (0, v) = (beta44 u v, 0) := by
  ext i <;> simp [jordanMul]

end InfoGeometry.Canonical.SplitOctonionJordanCore
