import InfoGeometry.Clifford.Cl55CAROperatorLift
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55CARAutomorphism

/-!
# Spin covariance of the operator-valued doubled carrier

The matrix entries are left-multiplication operators in the full
noncommutative `Cl(5,5)` algebra.  Spin covariance is proved pointwise on the
doubled carrier by the ring-equivalence multiplication and finite-sum laws.
-/

noncomputable section

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.Optics.OperatorLiftCarrier

abbrev Cl55ElementMatrix := Matrix (Fin 2) (Fin 2) Cl55

def leftActionMatrix55 (M : Cl55ElementMatrix) : Cl55OperatorMatrix :=
  fun i j => leftAction55 (M i j)

def spinTransportCarrier55 (g : Spin55) (v : Fin 2 → Cl55) : Fin 2 → Cl55 :=
  fun i => spinCARAutomorphism g (v i)

def spinTransportMatrix55 (g : Spin55) (M : Cl55ElementMatrix) :
    Cl55OperatorMatrix :=
  leftActionMatrix55 (fun i j => spinCARAutomorphism g (M i j))

noncomputable def spinTransportElementMatrix55 (g : Spin55) :
    Cl55ElementMatrix ≃+* Cl55ElementMatrix :=
  (spinCARAutomorphism g).mapMatrix

@[simp] theorem spinTransportElementMatrix55_apply
    (g : Spin55) (M : Cl55ElementMatrix) (i j : Fin 2) :
    spinTransportElementMatrix55 g M i j = spinCARAutomorphism g (M i j) :=
  rfl

theorem spinTransportElementMatrix55_mul
    (g h : Spin55) (M : Cl55ElementMatrix) :
    spinTransportElementMatrix55 (g * h) M =
      spinTransportElementMatrix55 g
        (spinTransportElementMatrix55 h M) := by
  ext i j
  exact spinCliffordRingEquiv_mul g h (M i j)

theorem spinTransportElementMatrix55_injective
    (g : Spin55) :
    Function.Injective (spinTransportElementMatrix55 g) := by
  exact (spinTransportElementMatrix55 g).injective

theorem spinTransportElementMatrix55_surjective
    (g : Spin55) :
    Function.Surjective (spinTransportElementMatrix55 g) := by
  exact (spinTransportElementMatrix55 g).surjective

noncomputable def spinTransportElementMatrix55Hom :
    Spin55 →* (Cl55ElementMatrix ≃+* Cl55ElementMatrix) where
  toFun := spinTransportElementMatrix55
  map_one' := by
    ext M i j
    simp [spinTransportElementMatrix55, spinCARAutomorphism,
      spinCliffordRingEquiv]
  map_mul' := by
    intro g h
    ext M i j
    exact spinCliffordRingEquiv_mul g h (M i j)

@[simp] theorem spinTransportCarrier55_apply
    (g : Spin55) (v : Fin 2 → Cl55) (i : Fin 2) :
    spinTransportCarrier55 g v i = spinCARAutomorphism g (v i) :=
  rfl

theorem spinTransportCarrier55_mul
    (g h : Spin55) (v : Fin 2 → Cl55) :
    spinTransportCarrier55 (g * h) v =
      spinTransportCarrier55 g (spinTransportCarrier55 h v) := by
  funext i
  change spinCARAutomorphism (g * h) (v i) =
    spinCARAutomorphism g (spinCARAutomorphism h (v i))
  exact spinCliffordRingEquiv_mul g h (v i)

theorem spinTransportMatrix55_action
    (g : Spin55) (M : Cl55ElementMatrix) (v : Fin 2 → Cl55) (i : Fin 2) :
    spinCARAutomorphism g
        (matrixAction (leftActionMatrix55 M) v i) =
      matrixAction (spinTransportMatrix55 g M)
        (spinTransportCarrier55 g v) i := by
  simp only [matrixAction_apply, leftActionMatrix55, spinTransportMatrix55,
    spinTransportCarrier55, leftAction55_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact map_mul (spinCARAutomorphism g) (M i j) (v j)

theorem spinTransportMatrix55_action_fun
    (g : Spin55) (M : Cl55ElementMatrix) (v : Fin 2 → Cl55) :
    spinTransportCarrier55 g (matrixAction (leftActionMatrix55 M) v) =
      matrixAction (spinTransportMatrix55 g M)
        (spinTransportCarrier55 g v) := by
  funext i
  exact spinTransportMatrix55_action g M v i

end InfoGeometry.Clifford.Clifford55
