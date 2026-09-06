import InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis

/-!
# The circular Peirce basis on the canonical Zorn carrier

The Cartesian circular frame is transported through the native linear
equivalence `cartesianZornLinearEquiv`.  This packages the eight polarized
vectors as an actual Mathlib basis and records the determinant/null-cone
readout in those coordinates.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Canonical.ZornMatrix

abbrev CZ := CanonicalZorn

noncomputable def circularPeirceBasis : Module.Basis (Fin 8) ℝ CZ :=
  circularBasis.map cartesianZornLinearEquiv

@[simp] theorem circularPeirceBasis_apply (i : Fin 8) :
    circularPeirceBasis i = cartesianZornLinearEquiv (circularFrame i) := by
  rw [circularPeirceBasis, Module.Basis.map_apply, circularBasis_apply]

theorem circularPeirceBasis_reconstruct (X : CZ) :
    ∑ i : Fin 8,
      circularCoordinate (cartesianZornLinearEquiv.symm X) i •
        circularPeirceBasis i = X := by
  rw [← cartesianZornLinearEquiv.apply_symm_apply X]
  have h := circularFrame_reconstruct (cartesianZornLinearEquiv.symm X)
  have h' := congrArg cartesianZornLinearEquiv h
  simpa only [circularPeirceBasis, Module.Basis.map_apply,
    circularBasis_apply, map_sum, map_smul,
    cartesianZornLinearEquiv.symm_apply_apply] using h'

theorem zornPlus_mul_circularPeirceBasis (i : Fin 8) :
    zornPlus * circularPeirceBasis i =
      match i with
      | 0 => circularPeirceBasis 0
      | 1 => circularPeirceBasis 1
      | 2 => circularPeirceBasis 2
      | 3 => circularPeirceBasis 3
      | 4 => 0
      | 5 => 0
      | 6 => 0
      | 7 => 0
      | _ => 0 := by
  fin_cases i <;> simp only [Fin.isValue]
  · rw [circularPeirceBasis_apply, circularPeirceBasis_apply]
    change zornPlus * cartesianZornLinearEquiv scalarPlus =
      cartesianZornLinearEquiv scalarPlus
    rw [cartesianZorn_scalarPlus, zornPlus_idempotent]
  · rw [circularPeirceBasis_apply, circularPeirceBasis_apply]
    change zornPlus * cartesianZornLinearEquiv (rootPlus 0) =
      cartesianZornLinearEquiv (rootPlus 0)
    exact zornPlus_mul_cartesianZorn_rootPlus 0
  · rw [circularPeirceBasis_apply, circularPeirceBasis_apply]
    change zornPlus * cartesianZornLinearEquiv (rootPlus 1) =
      cartesianZornLinearEquiv (rootPlus 1)
    exact zornPlus_mul_cartesianZorn_rootPlus 1
  · rw [circularPeirceBasis_apply, circularPeirceBasis_apply]
    change zornPlus * cartesianZornLinearEquiv (rootPlus 2) =
      cartesianZornLinearEquiv (rootPlus 2)
    exact zornPlus_mul_cartesianZorn_rootPlus 2
  · rw [circularPeirceBasis_apply]
    change zornPlus * cartesianZornLinearEquiv scalarMinus = 0
    rw [cartesianZorn_scalarMinus, zornPlus_mul_zornMinus]
  · rw [circularPeirceBasis_apply]
    change zornPlus * cartesianZornLinearEquiv (rootMinus 0) = 0
    exact zornPlus_mul_cartesianZorn_rootMinus 0
  · rw [circularPeirceBasis_apply]
    change zornPlus * cartesianZornLinearEquiv (rootMinus 1) = 0
    exact zornPlus_mul_cartesianZorn_rootMinus 1
  · rw [circularPeirceBasis_apply]
    change zornPlus * cartesianZornLinearEquiv (rootMinus 2) = 0
    exact zornPlus_mul_cartesianZorn_rootMinus 2

theorem zornMinus_mul_circularPeirceBasis (i : Fin 8) :
    zornMinus * circularPeirceBasis i =
      match i with
      | 0 => 0
      | 1 => 0
      | 2 => 0
      | 3 => 0
      | 4 => circularPeirceBasis 4
      | 5 => circularPeirceBasis 5
      | 6 => circularPeirceBasis 6
      | 7 => circularPeirceBasis 7
      | _ => 0 := by
  fin_cases i <;> simp only [Fin.isValue]
  · rw [circularPeirceBasis_apply]
    change zornMinus * cartesianZornLinearEquiv scalarPlus = 0
    rw [cartesianZorn_scalarPlus, zornMinus_mul_zornPlus]
  · rw [circularPeirceBasis_apply]
    change zornMinus * cartesianZornLinearEquiv (rootPlus 0) = 0
    exact zornMinus_mul_cartesianZorn_rootPlus 0
  · rw [circularPeirceBasis_apply]
    change zornMinus * cartesianZornLinearEquiv (rootPlus 1) = 0
    exact zornMinus_mul_cartesianZorn_rootPlus 1
  · rw [circularPeirceBasis_apply]
    change zornMinus * cartesianZornLinearEquiv (rootPlus 2) = 0
    exact zornMinus_mul_cartesianZorn_rootPlus 2
  · rw [circularPeirceBasis_apply, circularPeirceBasis_apply]
    change zornMinus * cartesianZornLinearEquiv scalarMinus =
      cartesianZornLinearEquiv scalarMinus
    rw [cartesianZorn_scalarMinus, zornMinus_idempotent]
  · rw [circularPeirceBasis_apply, circularPeirceBasis_apply]
    change zornMinus * cartesianZornLinearEquiv (rootMinus 0) =
      cartesianZornLinearEquiv (rootMinus 0)
    exact zornMinus_mul_cartesianZorn_rootMinus 0
  · rw [circularPeirceBasis_apply, circularPeirceBasis_apply]
    change zornMinus * cartesianZornLinearEquiv (rootMinus 1) =
      cartesianZornLinearEquiv (rootMinus 1)
    exact zornMinus_mul_cartesianZorn_rootMinus 1
  · rw [circularPeirceBasis_apply, circularPeirceBasis_apply]
    change zornMinus * cartesianZornLinearEquiv (rootMinus 2) =
      cartesianZornLinearEquiv (rootMinus 2)
    exact zornMinus_mul_cartesianZorn_rootMinus 2

theorem circularPeirceBasis_mul_zornPlus (i : Fin 8) :
    circularPeirceBasis i * zornPlus =
      match i with
      | 0 => circularPeirceBasis 0
      | 1 => 0
      | 2 => 0
      | 3 => 0
      | 4 => 0
      | 5 => circularPeirceBasis 5
      | 6 => circularPeirceBasis 6
      | 7 => circularPeirceBasis 7
      | _ => 0 := by
  fin_cases i <;> simp only [Fin.isValue]
  · rw [circularPeirceBasis_apply, circularPeirceBasis_apply]
    change cartesianZornLinearEquiv scalarPlus * zornPlus =
      cartesianZornLinearEquiv scalarPlus
    rw [cartesianZorn_scalarPlus, zornPlus_idempotent]
  · rw [circularPeirceBasis_apply]
    change cartesianZornLinearEquiv (rootPlus 0) * zornPlus = 0
    exact cartesianZorn_rootPlus_mul_zornPlus 0
  · rw [circularPeirceBasis_apply]
    change cartesianZornLinearEquiv (rootPlus 1) * zornPlus = 0
    exact cartesianZorn_rootPlus_mul_zornPlus 1
  · rw [circularPeirceBasis_apply]
    change cartesianZornLinearEquiv (rootPlus 2) * zornPlus = 0
    exact cartesianZorn_rootPlus_mul_zornPlus 2
  · rw [circularPeirceBasis_apply]
    change cartesianZornLinearEquiv scalarMinus * zornPlus = 0
    rw [cartesianZorn_scalarMinus, zornMinus_mul_zornPlus]
  · rw [circularPeirceBasis_apply, circularPeirceBasis_apply]
    change cartesianZornLinearEquiv (rootMinus 0) * zornPlus =
      cartesianZornLinearEquiv (rootMinus 0)
    exact cartesianZorn_rootMinus_mul_zornPlus 0
  · rw [circularPeirceBasis_apply, circularPeirceBasis_apply]
    change cartesianZornLinearEquiv (rootMinus 1) * zornPlus =
      cartesianZornLinearEquiv (rootMinus 1)
    exact cartesianZorn_rootMinus_mul_zornPlus 1
  · rw [circularPeirceBasis_apply, circularPeirceBasis_apply]
    change cartesianZornLinearEquiv (rootMinus 2) * zornPlus =
      cartesianZornLinearEquiv (rootMinus 2)
    exact cartesianZorn_rootMinus_mul_zornPlus 2

theorem circularPeirceBasis_mul_zornMinus (i : Fin 8) :
    circularPeirceBasis i * zornMinus =
      match i with
      | 0 => 0
      | 1 => circularPeirceBasis 1
      | 2 => circularPeirceBasis 2
      | 3 => circularPeirceBasis 3
      | 4 => circularPeirceBasis 4
      | 5 => 0
      | 6 => 0
      | 7 => 0
      | _ => 0 := by
  fin_cases i <;> simp only [Fin.isValue]
  · rw [circularPeirceBasis_apply]
    change cartesianZornLinearEquiv scalarPlus * zornMinus = 0
    rw [cartesianZorn_scalarPlus, zornPlus_mul_zornMinus]
  · rw [circularPeirceBasis_apply, circularPeirceBasis_apply]
    change cartesianZornLinearEquiv (rootPlus 0) * zornMinus =
      cartesianZornLinearEquiv (rootPlus 0)
    exact cartesianZorn_rootPlus_mul_zornMinus 0
  · rw [circularPeirceBasis_apply, circularPeirceBasis_apply]
    change cartesianZornLinearEquiv (rootPlus 1) * zornMinus =
      cartesianZornLinearEquiv (rootPlus 1)
    exact cartesianZorn_rootPlus_mul_zornMinus 1
  · rw [circularPeirceBasis_apply, circularPeirceBasis_apply]
    change cartesianZornLinearEquiv (rootPlus 2) * zornMinus =
      cartesianZornLinearEquiv (rootPlus 2)
    exact cartesianZorn_rootPlus_mul_zornMinus 2
  · rw [circularPeirceBasis_apply, circularPeirceBasis_apply]
    change cartesianZornLinearEquiv scalarMinus * zornMinus =
      cartesianZornLinearEquiv scalarMinus
    rw [cartesianZorn_scalarMinus, zornMinus_idempotent]
  · rw [circularPeirceBasis_apply]
    change cartesianZornLinearEquiv (rootMinus 0) * zornMinus = 0
    exact cartesianZorn_rootMinus_mul_zornMinus 0
  · rw [circularPeirceBasis_apply]
    change cartesianZornLinearEquiv (rootMinus 1) * zornMinus = 0
    exact cartesianZorn_rootMinus_mul_zornMinus 1
  · rw [circularPeirceBasis_apply]
    change cartesianZornLinearEquiv (rootMinus 2) * zornMinus = 0
    exact cartesianZorn_rootMinus_mul_zornMinus 2

theorem circularPeirceBasis_equivFun_symm_coordinate (X : CZ) :
    circularPeirceBasis.equivFun.symm
        (circularCoordinate (cartesianZornLinearEquiv.symm X)) = X := by
  rw [circularPeirceBasis.equivFun_symm_apply]
  exact circularPeirceBasis_reconstruct X

theorem circularPeirceBasis_coordinate_eq_equivFun (X : CZ) :
    circularCoordinate (cartesianZornLinearEquiv.symm X) =
      circularPeirceBasis.equivFun X := by
  have h := congrArg circularPeirceBasis.equivFun
    (circularPeirceBasis_equivFun_symm_coordinate X)
  simpa only [LinearEquiv.apply_symm_apply] using h

theorem circularPeirceBasis_linearIndependent :
    LinearIndependent ℝ (circularPeirceBasis : Fin 8 → CZ) :=
  circularPeirceBasis.linearIndependent

theorem circularPeirceBasis_span_top :
    Submodule.span ℝ (Set.range (circularPeirceBasis : Fin 8 → CZ)) = ⊤ := by
  exact circularPeirceBasis.span_eq

theorem circularPeirceBasis_norm_formula (X : CZ) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X =
      circularCoordinate (cartesianZornLinearEquiv.symm X) 0 *
          circularCoordinate (cartesianZornLinearEquiv.symm X) 4 -
        (circularCoordinate (cartesianZornLinearEquiv.symm X) 1 *
            circularCoordinate (cartesianZornLinearEquiv.symm X) 5 +
          circularCoordinate (cartesianZornLinearEquiv.symm X) 2 *
            circularCoordinate (cartesianZornLinearEquiv.symm X) 6 +
          circularCoordinate (cartesianZornLinearEquiv.symm X) 3 *
            circularCoordinate (cartesianZornLinearEquiv.symm X) 7) := by
  rcases X with ⟨a, x, y, b⟩
  simp [cartesianZornLinearEquiv_symm_apply, circularCoordinate,
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ,
    InfoGeometry.Canonical.ZornMatrix.dot]
  ring

theorem circularPeirceBasis_null_iff (X : CZ) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X = 0 ↔
      circularCoordinate (cartesianZornLinearEquiv.symm X) 0 *
          circularCoordinate (cartesianZornLinearEquiv.symm X) 4 =
        circularCoordinate (cartesianZornLinearEquiv.symm X) 1 *
            circularCoordinate (cartesianZornLinearEquiv.symm X) 5 +
          circularCoordinate (cartesianZornLinearEquiv.symm X) 2 *
            circularCoordinate (cartesianZornLinearEquiv.symm X) 6 +
          circularCoordinate (cartesianZornLinearEquiv.symm X) 3 *
            circularCoordinate (cartesianZornLinearEquiv.symm X) 7 := by
  rw [circularPeirceBasis_norm_formula]
  constructor <;> intro h <;> linarith

theorem circularPeirceBasis_explicit_expansion (X : CZ) :
    X = circularCoordinate (cartesianZornLinearEquiv.symm X) 0 • cartesianZornLinearEquiv scalarPlus
      + (∑ i : Fin 3, circularCoordinate (cartesianZornLinearEquiv.symm X) ⟨i.val + 1, by omega⟩ • cartesianZornLinearEquiv (rootPlus i))
      + circularCoordinate (cartesianZornLinearEquiv.symm X) 4 • cartesianZornLinearEquiv scalarMinus
      + (∑ i : Fin 3, circularCoordinate (cartesianZornLinearEquiv.symm X) ⟨i.val + 5, by omega⟩ • cartesianZornLinearEquiv (rootMinus i)) := by
  have h := circularPeirceBasis_reconstruct X
  rw [Fin.sum_univ_eight] at h
  have h1 : ∑ i : Fin 3, circularCoordinate (cartesianZornLinearEquiv.symm X) ⟨i.val + 1, by omega⟩ • cartesianZornLinearEquiv (rootPlus i) =
    circularCoordinate (cartesianZornLinearEquiv.symm X) 1 • cartesianZornLinearEquiv (rootPlus 0)
      + circularCoordinate (cartesianZornLinearEquiv.symm X) 2 • cartesianZornLinearEquiv (rootPlus 1)
      + circularCoordinate (cartesianZornLinearEquiv.symm X) 3 • cartesianZornLinearEquiv (rootPlus 2) := by
    rw [Fin.sum_univ_three]; rfl
  have h2 : ∑ i : Fin 3, circularCoordinate (cartesianZornLinearEquiv.symm X) ⟨i.val + 5, by omega⟩ • cartesianZornLinearEquiv (rootMinus i) =
    circularCoordinate (cartesianZornLinearEquiv.symm X) 5 • cartesianZornLinearEquiv (rootMinus 0)
      + circularCoordinate (cartesianZornLinearEquiv.symm X) 6 • cartesianZornLinearEquiv (rootMinus 1)
      + circularCoordinate (cartesianZornLinearEquiv.symm X) 7 • cartesianZornLinearEquiv (rootMinus 2) := by
    rw [Fin.sum_univ_three]; rfl
  rw [h1, h2]
  have h0 : circularPeirceBasis 0 = cartesianZornLinearEquiv scalarPlus := circularPeirceBasis_apply 0
  have h1' : circularPeirceBasis 1 = cartesianZornLinearEquiv (rootPlus 0) := circularPeirceBasis_apply 1
  have h2' : circularPeirceBasis 2 = cartesianZornLinearEquiv (rootPlus 1) := circularPeirceBasis_apply 2
  have h3' : circularPeirceBasis 3 = cartesianZornLinearEquiv (rootPlus 2) := circularPeirceBasis_apply 3
  have h4' : circularPeirceBasis 4 = cartesianZornLinearEquiv scalarMinus := circularPeirceBasis_apply 4
  have h5' : circularPeirceBasis 5 = cartesianZornLinearEquiv (rootMinus 0) := circularPeirceBasis_apply 5
  have h6' : circularPeirceBasis 6 = cartesianZornLinearEquiv (rootMinus 1) := circularPeirceBasis_apply 6
  have h7' : circularPeirceBasis 7 = cartesianZornLinearEquiv (rootMinus 2) := circularPeirceBasis_apply 7
  rw [h0, h1', h2', h3', h4', h5', h6', h7'] at h
  exact Eq.symm h |>.trans (by abel)

end InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
