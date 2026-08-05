import InfoGeometry.Canonical.Cl11FiniteTraceGNSReadout
import InfoGeometry.Prequantum.GNSAction

/-!
# Quotient action for the finite real trace GNS states

The finite matrix trace is faithful on quadratic squares.  Consequently its
algebraic GNS null set is zero, which supplies the null-left-ideal witness
required by the existing quotient-action owner.
-/

namespace InfoGeometry.Canonical.Cl11FiniteTraceGNSAction

open InfoGeometry.Canonical.Cl11FiniteTraceGNSReadout
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Prequantum.AlgebraicGNSState
open InfoGeometry.Prequantum.GNSAction
open InfoGeometry.Prequantum.GNSBridge
open InfoGeometry.Prequantum.GNSBridge.AbstractGNSState

noncomputable section

theorem normalizedTrace_star_mul_self_eq_zero_iff
    (n : ℕ) (X : MatStage n) :
    normalizedTrace n (star X * X) = 0 ↔ X = 0 := by
  constructor
  · intro h
    have hden : (2 : ℝ) ^ n ≠ 0 := by positivity
    have htrace : Matrix.trace (star X * X) = 0 := by
      unfold normalizedTrace at h
      field_simp [hden] at h
      simpa using h
    unfold Matrix.trace at htrace
    change (∑ i : InfoGeometry.Clifford.TowerMatrix.Idx n,
      ∑ j : InfoGeometry.Clifford.TowerMatrix.Idx n, X j i * X j i) = 0 at htrace
    ext i j
    have houter : ∀ i : InfoGeometry.Clifford.TowerMatrix.Idx n,
        (∑ j : InfoGeometry.Clifford.TowerMatrix.Idx n, X j i * X j i) = 0 :=
      fun i => (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (f := fun i : InfoGeometry.Clifford.TowerMatrix.Idx n =>
          ∑ j : InfoGeometry.Clifford.TowerMatrix.Idx n, X j i * X j i)
        (fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg (X j i))).mp htrace i
          (Finset.mem_univ i)
    have hrow :
        (∑ i : InfoGeometry.Clifford.TowerMatrix.Idx n, X i j * X i j) = 0 :=
      houter j
    have hentry : X i j * X i j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (f := fun k : InfoGeometry.Clifford.TowerMatrix.Idx n => X k j * X k j)
        (fun k _ => mul_self_nonneg (X k j))).mp hrow i (Finset.mem_univ i)
    exact mul_self_eq_zero.mp hentry
  · intro h
    subst X
    simp [normalizedTrace]

noncomputable def cl11RepresentationState (n : ℕ) :
    RepresentationState (MatStage n) where
  state := cl11AbstractGNSState n
  null_left_ideal := by
    intro a x hx
    rw [AbstractGNSState.mem_gnsNullSet_iff] at hx ⊢
    change normalizedTrace n (star x * x) = 0 at hx
    have hx0 : x = 0 :=
      (normalizedTrace_star_mul_self_eq_zero_iff n x).mp hx
    subst x
    simpa [cl11AbstractGNSState] using
      (normalizedTrace_star_mul_self_eq_zero_iff n (0 : MatStage n)).mpr rfl

abbrev cl11RepresentationQuotient (n : ℕ) : Type _ :=
  AbstractGNSState.gnsQuotient (cl11RepresentationState n).state

def cl11Action (n : ℕ) (a : MatStage n) :
    cl11RepresentationQuotient n → cl11RepresentationQuotient n :=
  (cl11RepresentationState n).act a

@[simp] theorem cl11Action_mk
    (n : ℕ) (a x : MatStage n) :
    cl11Action n a
        (Quotient.mk (AbstractGNSState.gnsSetoid
          (cl11RepresentationState n).state) x) =
      Quotient.mk (AbstractGNSState.gnsSetoid
        (cl11RepresentationState n).state) (a * x) := rfl

theorem cl11Action_mul
    (n : ℕ) (a b : MatStage n) (q : cl11RepresentationQuotient n) :
    cl11Action n (a * b) q = cl11Action n a (cl11Action n b q) := by
  exact (cl11RepresentationState n).act_mul a b q

end

end InfoGeometry.Canonical.Cl11FiniteTraceGNSAction
