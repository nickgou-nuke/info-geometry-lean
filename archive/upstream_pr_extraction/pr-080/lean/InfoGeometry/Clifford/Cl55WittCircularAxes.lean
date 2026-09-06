import InfoGeometry.Clifford.Cl55CAROperatorLift

/-!
# The noncommutative Witt/circular axes in `Cl(5,5)`

For every verified CAR pair, the sum and difference of creation and
annihilation operators give the split and elliptic directions of the local
Clifford packet.  All statements are proved in the full Clifford algebra.
-/

noncomputable section

namespace InfoGeometry.Clifford.Clifford55

def hyperbolicAxis55 (i : Fin 5) : Cl55 :=
  creation55 i + annihilation55 i

def ellipticAxis55 (i : Fin 5) : Cl55 :=
  creation55 i - annihilation55 i

/-- The elliptic CAR axis acting by genuine left multiplication. -/
def hyperbolicAction55 (i : Fin 5) : Cl55Operator :=
  leftAction55 (hyperbolicAxis55 i)

def ellipticAction55 (i : Fin 5) : Cl55Operator :=
  leftAction55 (ellipticAxis55 i)

theorem hyperbolicAxis55_sq (i : Fin 5) :
    hyperbolicAxis55 i * hyperbolicAxis55 i = 1 := by
  dsimp [hyperbolicAxis55]
  have hcar : creation55 i * annihilation55 i +
      annihilation55 i * creation55 i = 1 := by
    simpa [add_comm] using annihilation55_creation55_anticommutator i
  calc
    (creation55 i + annihilation55 i) *
        (creation55 i + annihilation55 i) =
        creation55 i * creation55 i +
          (creation55 i * annihilation55 i +
            annihilation55 i * creation55 i) +
          annihilation55 i * annihilation55 i := by noncomm_ring
    _ = 1 := by rw [creation55_sq i, annihilation55_sq i, hcar]; simp

theorem ellipticAxis55_sq (i : Fin 5) :
    ellipticAxis55 i * ellipticAxis55 i = -(1 : Cl55) := by
  dsimp [ellipticAxis55]
  have hcar : creation55 i * annihilation55 i +
      annihilation55 i * creation55 i = 1 := by
    simpa [add_comm] using annihilation55_creation55_anticommutator i
  calc
    (creation55 i - annihilation55 i) *
        (creation55 i - annihilation55 i) =
        creation55 i * creation55 i -
          (creation55 i * annihilation55 i +
            annihilation55 i * creation55 i) +
          annihilation55 i * annihilation55 i := by noncomm_ring
    _ = -(1 : Cl55) := by rw [creation55_sq i, annihilation55_sq i, hcar]; simp

theorem hyperbolicAxis55_ellipticAxis55_anticommute (i : Fin 5) :
    hyperbolicAxis55 i * ellipticAxis55 i +
        ellipticAxis55 i * hyperbolicAxis55 i = 0 := by
  dsimp [hyperbolicAxis55, ellipticAxis55]
  calc
    (creation55 i + annihilation55 i) * (creation55 i - annihilation55 i) +
        (creation55 i - annihilation55 i) *
          (creation55 i + annihilation55 i) =
        (creation55 i * creation55 i -
          annihilation55 i * annihilation55 i) +
          (annihilation55 i * annihilation55 i -
            creation55 i * creation55 i) := by
              noncomm_ring
              simp [creation55_sq, annihilation55_sq]
    _ = 0 := by
      simp [creation55_sq, annihilation55_sq]

theorem ellipticAction55_sq (i : Fin 5) :
    ellipticAction55 i * ellipticAction55 i = -(1 : Cl55Operator) := by
  rw [ellipticAction55, ← leftAction55_mul, ellipticAxis55_sq,
    leftAction55_neg, leftAction55_one]

theorem hyperbolicAction55_sq (i : Fin 5) :
    hyperbolicAction55 i * hyperbolicAction55 i = (1 : Cl55Operator) := by
  rw [hyperbolicAction55, ← leftAction55_mul, hyperbolicAxis55_sq,
    leftAction55_one]

theorem hyperbolicAction55_ellipticAction55_anticommute (i : Fin 5) :
    hyperbolicAction55 i * ellipticAction55 i +
        ellipticAction55 i * hyperbolicAction55 i = 0 := by
  rw [hyperbolicAction55, ellipticAction55, ← leftAction55_mul,
    ← leftAction55_mul, ← leftAction55_add,
    hyperbolicAxis55_ellipticAxis55_anticommute, leftAction55_zero]

theorem ellipticAction55_apply_sq (i : Fin 5) (x : Cl55) :
    ellipticAction55 i (ellipticAction55 i x) = -x := by
  have h := congrArg (fun T : Cl55Operator => T x) (ellipticAction55_sq i)
  simpa [Module.End.mul_apply] using h

theorem hyperbolicAction55_apply_sq (i : Fin 5) (x : Cl55) :
    hyperbolicAction55 i (hyperbolicAction55 i x) = x := by
  have h := congrArg (fun T : Cl55Operator => T x) (hyperbolicAction55_sq i)
  simpa [Module.End.mul_apply] using h

theorem hyperbolicAction55_ellipticAction55_apply_anticommute
    (i : Fin 5) (x : Cl55) :
    hyperbolicAction55 i (ellipticAction55 i x) +
        ellipticAction55 i (hyperbolicAction55 i x) = 0 := by
  have h := congrArg (fun T : Cl55Operator => T x)
    (hyperbolicAction55_ellipticAction55_anticommute i)
  simpa [Module.End.mul_apply] using h

def spinTransportedHyperbolicAction55
    (g : Spin55) (i : Fin 5) : Cl55Operator :=
  leftAction55 (spinCliffordRingEquiv g (hyperbolicAxis55 i))

def spinTransportedEllipticAction55
    (g : Spin55) (i : Fin 5) : Cl55Operator :=
  leftAction55 (spinCliffordRingEquiv g (ellipticAxis55 i))

theorem spinTransportedHyperbolicAction55_sq
    (g : Spin55) (i : Fin 5) :
    spinTransportedHyperbolicAction55 g i *
        spinTransportedHyperbolicAction55 g i = (1 : Cl55Operator) := by
  rw [spinTransportedHyperbolicAction55, ← leftAction55_mul,
    ← map_mul, hyperbolicAxis55_sq, map_one, leftAction55_one]

theorem spinTransportedEllipticAction55_sq
    (g : Spin55) (i : Fin 5) :
    spinTransportedEllipticAction55 g i *
        spinTransportedEllipticAction55 g i = -(1 : Cl55Operator) := by
  rw [spinTransportedEllipticAction55, ← leftAction55_mul,
    ← map_mul, ellipticAxis55_sq, map_neg, map_one, leftAction55_neg,
    leftAction55_one]

theorem spinTransportedAxis55_intertwines
    (g : Spin55) (i : Fin 5) (x : Cl55) :
    spinCliffordRingEquiv g (hyperbolicAction55 i x) =
      spinTransportedHyperbolicAction55 g i
        (spinCliffordRingEquiv g x) := by
  exact spinTransport_leftAction55_mul g (hyperbolicAxis55 i) x

theorem spinTransportedEllipticAction55_intertwines
    (g : Spin55) (i : Fin 5) (x : Cl55) :
    spinCliffordRingEquiv g (ellipticAction55 i x) =
      spinTransportedEllipticAction55 g i
        (spinCliffordRingEquiv g x) := by
  exact spinTransport_leftAction55_mul g (ellipticAxis55 i) x

theorem spinTransportedAxis55_anticommute
    (g : Spin55) (i : Fin 5) :
    spinTransportedHyperbolicAction55 g i *
          spinTransportedEllipticAction55 g i +
    spinTransportedEllipticAction55 g i *
          spinTransportedHyperbolicAction55 g i = 0 := by
  rw [spinTransportedHyperbolicAction55,
    spinTransportedEllipticAction55, ← leftAction55_mul,
    ← leftAction55_mul, ← leftAction55_add]
  have h := congrArg (spinCliffordRingEquiv g)
    (hyperbolicAxis55_ellipticAxis55_anticommute i)
  rw [map_add, map_mul, map_mul, map_zero] at h
  rw [h]
  exact leftAction55_zero

theorem spinTransported_hyperbolicAxis55_sq (g : Spin55) (i : Fin 5) :
    spinCliffordRingEquiv g (hyperbolicAxis55 i) *
        spinCliffordRingEquiv g (hyperbolicAxis55 i) = 1 := by
  simpa only [map_mul, map_one] using
    congrArg (spinCliffordRingEquiv g) (hyperbolicAxis55_sq i)

theorem spinTransported_ellipticAxis55_sq (g : Spin55) (i : Fin 5) :
    spinCliffordRingEquiv g (ellipticAxis55 i) *
        spinCliffordRingEquiv g (ellipticAxis55 i) = -(1 : Cl55) := by
  simpa only [map_mul, map_neg, map_one] using
    congrArg (spinCliffordRingEquiv g) (ellipticAxis55_sq i)

end InfoGeometry.Clifford.Clifford55
