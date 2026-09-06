import proofs.SplitOctonionCircularChiralClosure

/-!
# Spin-coordinate core of the full split-octonion Jordan algebra

The symmetrized Zorn product is expressed as a scalar plus a seven-dimensional
trace-free coordinate.  Cross products cancel once, in the coordinate theorem;
all subsequent Jordan identities use only the bilinear spin pairing.
-/

noncomputable section

namespace SplitOctonionJordanCore

open SplitOctonionChiralClosure

abbrev Zorn := SplitOctonionChiralClosure.Zorn
abbrev Vec3 := SplitOctonionChiralClosure.Vec3

structure SpinVector7 where
  t : ℂ
  u : Vec3
  v : Vec3

@[ext] theorem SpinVector7.ext {x y : SpinVector7}
    (ht : x.t = y.t) (hu : x.u = y.u) (hv : x.v = y.v) : x = y := by
  cases x
  cases y
  simp_all

def jordanMul (X Y : Zorn) : Zorn := smul (1 / 2) (antiComm X Y)

def scalarCoord (X : Zorn) : ℂ := (X.a + X.b) / 2

def vectorCoord (X : Zorn) : SpinVector7 :=
  ⟨(X.a - X.b) / 2, X.u, X.v⟩

def spinPairing (x y : SpinVector7) : ℂ :=
  x.t * y.t + (dot x.u y.v + dot y.u x.v) / 2

def spinLinear (a : ℂ) (x : SpinVector7)
    (b : ℂ) (y : SpinVector7) : SpinVector7 :=
  ⟨a * y.t + b * x.t,
    fun i => a * y.u i + b * x.u i,
    fun i => a * y.v i + b * x.v i⟩

theorem spinPairing_symmetric (x y : SpinVector7) :
    spinPairing x y = spinPairing y x := by
  simp [spinPairing]
  ring

theorem jordanMul_spin_coordinates (X Y : Zorn) :
    scalarCoord (jordanMul X Y) =
        scalarCoord X * scalarCoord Y +
          spinPairing (vectorCoord X) (vectorCoord Y) ∧
    vectorCoord (jordanMul X Y) =
        spinLinear (scalarCoord X) (vectorCoord X)
          (scalarCoord Y) (vectorCoord Y) := by
  constructor
  · simp [scalarCoord, vectorCoord, jordanMul, spinPairing,
      antiComm, mul, add, smul, dot,
      SplitOctonionBraidSU3.zornMul, SplitOctonionBraidSU3.zornAdd,
      SplitOctonionBraidSU3.zornSmul, SplitOctonionBraidSU3.dot3]
    ring
  · apply SpinVector7.ext
    · simp [scalarCoord, vectorCoord, jordanMul, spinLinear,
        antiComm, mul, add, smul,
        SplitOctonionBraidSU3.zornMul, SplitOctonionBraidSU3.zornAdd,
        SplitOctonionBraidSU3.zornSmul, SplitOctonionBraidSU3.dot3]
      ring
    · funext i
      simp [scalarCoord, vectorCoord, jordanMul, spinLinear,
        antiComm, mul, add, smul,
        SplitOctonionBraidSU3.zornMul, SplitOctonionBraidSU3.zornAdd,
        SplitOctonionBraidSU3.zornSmul, SplitOctonionBraidSU3.cross3]
      fin_cases i <;> simp [SplitOctonionBraidSU3.cross3] <;> ring
    · funext i
      simp [scalarCoord, vectorCoord, jordanMul, spinLinear,
        antiComm, mul, add, smul,
        SplitOctonionBraidSU3.zornMul, SplitOctonionBraidSU3.zornAdd,
        SplitOctonionBraidSU3.zornSmul, SplitOctonionBraidSU3.cross3]
      fin_cases i <;> simp [SplitOctonionBraidSU3.cross3] <;> ring

theorem zorn_eq_of_spin_coordinates {X Y : Zorn}
    (hs : scalarCoord X = scalarCoord Y)
    (hv : vectorCoord X = vectorCoord Y) : X = Y := by
  apply SplitOctonionBraidSU3.zorn_ext
  · have ht := congrArg SpinVector7.t hv
    simp [scalarCoord, vectorCoord] at hs ht
    calc
      X.a = ((X.a + X.b) + (X.a - X.b)) / 2 := by ring
      _ = ((Y.a + Y.b) + (Y.a - Y.b)) / 2 := by rw [hs, ht]
      _ = Y.a := by ring
  · exact congrArg SpinVector7.u hv
  · exact congrArg SpinVector7.v hv
  · have ht := congrArg SpinVector7.t hv
    simp [scalarCoord, vectorCoord] at hs ht
    calc
      X.b = ((X.a + X.b) - (X.a - X.b)) / 2 := by ring
      _ = ((Y.a + Y.b) - (Y.a - Y.b)) / 2 := by rw [hs, ht]
      _ = Y.b := by ring

@[simp] theorem scalarCoord_jordanMul (X Y : Zorn) :
    scalarCoord (jordanMul X Y) =
      scalarCoord X * scalarCoord Y +
        spinPairing (vectorCoord X) (vectorCoord Y) :=
  (jordanMul_spin_coordinates X Y).1

@[simp] theorem vectorCoord_jordanMul (X Y : Zorn) :
    vectorCoord (jordanMul X Y) =
      spinLinear (scalarCoord X) (vectorCoord X)
        (scalarCoord Y) (vectorCoord Y) :=
  (jordanMul_spin_coordinates X Y).2

private theorem spinPairing_spinLinear_left
    (a b : ℂ) (x y z : SpinVector7) :
    spinPairing (spinLinear a x b y) z =
      a * spinPairing y z + b * spinPairing x z := by
  simp [spinPairing, spinLinear, dot, SplitOctonionBraidSU3.dot3]
  ring

private theorem spinPairing_spinLinear_right
    (a b : ℂ) (x y z : SpinVector7) :
    spinPairing z (spinLinear a x b y) =
      a * spinPairing z y + b * spinPairing z x := by
  rw [spinPairing_symmetric, spinPairing_spinLinear_left]
  rw [spinPairing_symmetric y z, spinPairing_symmetric x z]

private theorem spinLinear_extensional (a b c d : ℂ)
    (x y : SpinVector7)
    (ht : a * y.t + b * x.t = c * y.t + d * x.t)
    (hu : ∀ i, a * y.u i + b * x.u i = c * y.u i + d * x.u i)
    (hv : ∀ i, a * y.v i + b * x.v i = c * y.v i + d * x.v i) :
    spinLinear a x b y = spinLinear c x d y := by
  apply SpinVector7.ext
  · exact ht
  · funext i; exact hu i
  · funext i; exact hv i

/-- Lightweight Jordan identity derived from the spin-coordinate formula. -/
theorem jordan_identity_from_spin_coordinates (X Y : Zorn) :
    jordanMul (jordanMul X X) (jordanMul X Y) =
      jordanMul X (jordanMul (jordanMul X X) Y) := by
  apply zorn_eq_of_spin_coordinates
  · simp only [scalarCoord_jordanMul, vectorCoord_jordanMul,
      spinPairing_spinLinear_left, spinPairing_spinLinear_right]
    ring
  · simp only [scalarCoord_jordanMul, vectorCoord_jordanMul,
      spinPairing_spinLinear_left, spinPairing_spinLinear_right]
    apply SpinVector7.ext <;>
      simp only [spinLinear]
    · ring
    · funext i
      ring
    · funext i
      ring

theorem jordan_square_coordinates (X : Zorn) :
    scalarCoord (jordanMul X X) =
        scalarCoord X ^ 2 + spinPairing (vectorCoord X) (vectorCoord X) ∧
    vectorCoord (jordanMul X X) =
      spinLinear (scalarCoord X) (vectorCoord X)
        (scalarCoord X) (vectorCoord X) := by
  simpa [pow_two] using jordanMul_spin_coordinates X X

end SplitOctonionJordanCore

end noncomputable section
