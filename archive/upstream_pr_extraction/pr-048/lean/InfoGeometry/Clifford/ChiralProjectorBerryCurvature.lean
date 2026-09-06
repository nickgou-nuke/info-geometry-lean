import Mathlib.Tactic

/-!
# Algebraic projector curvature and relative chiral transport

The parameter derivatives are supplied as operator-valued data.  This is the
finite algebraic core of the projector formula; smoothness and differential
forms belong to a later specialization.
-/

namespace InfoGeometry.Clifford.ChiralProjectorBerryCurvature

variable {I A : Type*} [Ring A]

def commutator (x y : A) : A := x * y - y * x

def projectorCurvature (P dPi dPj : A) : A :=
  P * commutator dPi dPj * P

theorem projectorCurvature_swap (P dPi dPj : A) :
    projectorCurvature P dPj dPi = -projectorCurvature P dPi dPj := by
  dsimp [projectorCurvature, commutator]
  noncomm_ring

def relativeCurvature (Fplus Fminus : A) (transport : A → A) : A :=
  Fminus - transport Fplus

theorem relativeCurvature_eq_zero_of_transport
    (Fplus Fminus : A) (transport : A → A)
    (htransport : transport Fplus = Fminus) :
    relativeCurvature Fplus Fminus transport = 0 := by
  dsimp [relativeCurvature]
  rw [htransport, sub_self]

theorem relativeCurvature_eq_zero_iff
    (Fplus Fminus : A) (transport : A → A) :
    relativeCurvature Fplus Fminus transport = 0 ↔
      transport Fplus = Fminus := by
  constructor
  · intro h
    dsimp [relativeCurvature] at h
    exact (sub_eq_zero.mp h).symm
  · exact relativeCurvature_eq_zero_of_transport Fplus Fminus transport

def covariantTwistDefect
    (Dplus Dminus : A → A) (tau : A → A) : A → A :=
  fun x => Dminus (tau x) - tau (Dplus x)

def twistCurvatureDefect
    (Fplus Fminus : A → A) (tau : A → A) : A → A :=
  fun x => Fminus (tau x) - tau (Fplus x)

theorem twistCurvatureDefect_apply
    (Fplus Fminus : A → A) (tau : A → A) (x : A) :
    twistCurvatureDefect Fplus Fminus tau x =
      Fminus (tau x) - tau (Fplus x) := rfl

theorem covariantTwistDefect_eq_zero_iff
    (Dplus Dminus : A → A) (tau : A → A) :
    covariantTwistDefect Dplus Dminus tau = 0 ↔
      ∀ x, Dminus (tau x) = tau (Dplus x) := by
  constructor
  · intro h x
    have hx := congrFun h x
    dsimp [covariantTwistDefect] at hx
    exact sub_eq_zero.mp hx
  · intro h
    funext x
    dsimp [covariantTwistDefect]
    simpa [covariantTwistDefect] using sub_eq_zero.mpr (h x)

theorem twistCurvatureDefect_eq_zero_iff
    (Fplus Fminus : A → A) (tau : A → A) :
    twistCurvatureDefect Fplus Fminus tau = 0 ↔
      ∀ x, Fminus (tau x) = tau (Fplus x) := by
  constructor
  · intro h x
    have hx := congrFun h x
    dsimp [twistCurvatureDefect] at hx
    exact sub_eq_zero.mp hx
  · intro h
    funext x
    simpa [twistCurvatureDefect] using sub_eq_zero.mpr (h x)

end InfoGeometry.Clifford.ChiralProjectorBerryCurvature
