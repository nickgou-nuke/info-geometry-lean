import InfoGeometry.Physics.ChiralCausalCone
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.OperatorValuedJones
import InfoGeometry.Geometry.ParavectorZornBoundary

/-!
# Pauli/Weyl soldering and the circular causal packet

This file records the mediated first step of the chiral construction.  A
four-vector is soldered to a `2 × 2` matrix first; the matrix is then read in
the existing causal packet `(scalar, chiral, exchange, circular)`.  No Zorn
or Clifford identification is asserted here.
-/

noncomputable section

namespace InfoGeometry.Physics.ChiralCausalCone

open InfoGeometry.Clifford
open InfoGeometry.Canonical.ZornVectorMatrixExplicit
open InfoGeometry.Geometry.PauliParavectorBridge
open InfoGeometry.Geometry.ParavectorZornBoundary

/-- The causal packet of a four-vector in the repository's ordering. -/
def causalPacket (t x y z : ℂ) : CausalOperatorCoordinates ℂ :=
  ⟨t, z, x, y⟩

theorem causalPacket_injective :
    Function.Injective
      (fun p : ℂ × (ℂ × (ℂ × ℂ)) =>
        causalPacket p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  intro a b h
  rcases a with ⟨t, x, y, z⟩
  rcases b with ⟨t', x', y', z'⟩
  injection h with ht hz hx hy
  cases ht
  cases hz
  cases hx
  cases hy
  rfl

theorem causalPacket_eq_iff
    (t x y z t' x' y' z' : ℂ) :
    causalPacket t x y z = causalPacket t' x' y' z' ↔
      t = t' ∧ x = x' ∧ y = y' ∧ z = z' := by
  constructor
  · intro h
    injection h with ht hz hx hy
    exact ⟨ht, hx, hy, hz⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

/-- Pauli/Weyl soldering is the existing causal reconstruction of that packet. -/
theorem solder_eq_reconstruct_causalPacket (t x y z : ℂ) :
    SolderingSpinConnectionBogoliubov.solder t x y z =
      reconstruct_causal (causalPacket t x y z) := by
  rw [solder_in_chiral_basis]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [causalPacket, reconstruct_causal, σPlus, σMinus, σ3c,
      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply]
  all_goals ring

/-- The circular causal packet reads back the original four-vector entries. -/
theorem causalCoordinates_solder (t x y z : ℂ) :
    causalCoordinates (SolderingSpinConnectionBogoliubov.solder t x y z) =
      causalPacket t x y z := by
  rw [solder_eq_reconstruct_causalPacket]
  exact causalCoordinates_reconstruct (causalPacket t x y z)

theorem solder_eq_iff
    (t x y z t' x' y' z' : ℂ) :
    SolderingSpinConnectionBogoliubov.solder t x y z =
        SolderingSpinConnectionBogoliubov.solder t' x' y' z' ↔
      t = t' ∧ x = x' ∧ y = y' ∧ z = z' := by
  constructor
  · intro h
    have hc := congrArg causalCoordinates h
    rw [causalCoordinates_solder, causalCoordinates_solder] at hc
    exact (causalPacket_eq_iff t x y z t' x' y' z').mp hc
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

/-- The two circular chiral coefficients recover the Cartesian transverse
    coordinates used by the Zorn boundary. -/
theorem solder_chiral_coeffs_recover_transverse (t x y z : ℝ) :
    ((coeffPlus
        (SolderingSpinConnectionBogoliubov.solder
          (t : ℂ) (x : ℂ) (y : ℂ) (z : ℂ))) +
        coeffMinus
        (SolderingSpinConnectionBogoliubov.solder
          (t : ℂ) (x : ℂ) (y : ℂ) (z : ℂ))) / 2 = (x : ℂ) ∧
    ((coeffMinus
        (SolderingSpinConnectionBogoliubov.solder
          (t : ℂ) (x : ℂ) (y : ℂ) (z : ℂ))) -
        coeffPlus
        (SolderingSpinConnectionBogoliubov.solder
          (t : ℂ) (x : ℂ) (y : ℂ) (z : ℂ))) /
        (2 * Complex.I) = (y : ℂ) := by
  rcases solder_chiral_coeffs t x y z with ⟨_, hplus, hminus, _⟩
  rw [hplus, hminus]
  constructor
  · ring
  · field_simp
    ring

/-- The Zorn transverse slot is obtained only after the circular chiral
    coefficients have been changed back to Cartesian `(x,y)` coordinates. -/
theorem zornBoundary_transverse_from_chiral_coeffs (v : Minkowski4) :
    zornX (zornBoundaryOfMinkowski4 v) =
        ![
          (((coeffPlus
              (SolderingSpinConnectionBogoliubov.solder
                (v.t : ℂ) (v.x : ℂ) (v.y : ℂ) (v.z : ℂ))) +
              coeffMinus
              (SolderingSpinConnectionBogoliubov.solder
                (v.t : ℂ) (v.x : ℂ) (v.y : ℂ) (v.z : ℂ))) / 2).re,
          (((coeffMinus
              (SolderingSpinConnectionBogoliubov.solder
                (v.t : ℂ) (v.x : ℂ) (v.y : ℂ) (v.z : ℂ))) -
              coeffPlus
              (SolderingSpinConnectionBogoliubov.solder
                (v.t : ℂ) (v.x : ℂ) (v.y : ℂ) (v.z : ℂ))) /
              (2 * Complex.I)).re,
          0] := by
  rcases solder_chiral_coeffs_recover_transverse v.t v.x v.y v.z with
    ⟨hx, hy⟩
  rw [zornX_boundary]
  funext i
  fin_cases i
  · simp [xyPlaneVec, hx]
  · simp [xyPlaneVec, hy]
  · rfl

/-! The complete four-component readout: the two diagonal Zorn slots come from
the `(I, σ³)` coefficients and the two vector slots come from the circular
`(σ⁺, σ⁻)` coefficients after the Cartesian change of basis. -/

theorem zornBoundary_from_chiral_coeffs (v : Minkowski4) :
    zornBoundaryOfMinkowski4 v =
      zornMk
        (((coeffI
            (SolderingSpinConnectionBogoliubov.solder
              (v.t : ℂ) (v.x : ℂ) (v.y : ℂ) (v.z : ℂ))) +
            coeff3
            (SolderingSpinConnectionBogoliubov.solder
              (v.t : ℂ) (v.x : ℂ) (v.y : ℂ) (v.z : ℂ))).re)
        (((coeffI
            (SolderingSpinConnectionBogoliubov.solder
              (v.t : ℂ) (v.x : ℂ) (v.y : ℂ) (v.z : ℂ))) -
            coeff3
            (SolderingSpinConnectionBogoliubov.solder
              (v.t : ℂ) (v.x : ℂ) (v.y : ℂ) (v.z : ℂ))).re)
        ![
          (((coeffPlus
              (SolderingSpinConnectionBogoliubov.solder
                (v.t : ℂ) (v.x : ℂ) (v.y : ℂ) (v.z : ℂ))) +
              coeffMinus
              (SolderingSpinConnectionBogoliubov.solder
                (v.t : ℂ) (v.x : ℂ) (v.y : ℂ) (v.z : ℂ))) / 2).re,
          (((coeffMinus
              (SolderingSpinConnectionBogoliubov.solder
                (v.t : ℂ) (v.x : ℂ) (v.y : ℂ) (v.z : ℂ))) -
              coeffPlus
              (SolderingSpinConnectionBogoliubov.solder
                (v.t : ℂ) (v.x : ℂ) (v.y : ℂ) (v.z : ℂ))) /
              (2 * Complex.I)).re,
          0]
        ![
          (((coeffPlus
              (SolderingSpinConnectionBogoliubov.solder
                (v.t : ℂ) (v.x : ℂ) (v.y : ℂ) (v.z : ℂ))) +
              coeffMinus
              (SolderingSpinConnectionBogoliubov.solder
                (v.t : ℂ) (v.x : ℂ) (v.y : ℂ) (v.z : ℂ))) / 2).re,
          (((coeffMinus
              (SolderingSpinConnectionBogoliubov.solder
                (v.t : ℂ) (v.x : ℂ) (v.y : ℂ) (v.z : ℂ))) -
              coeffPlus
              (SolderingSpinConnectionBogoliubov.solder
                (v.t : ℂ) (v.x : ℂ) (v.y : ℂ) (v.z : ℂ))) /
              (2 * Complex.I)).re,
          0] := by
  rcases solder_chiral_coeffs v.t v.x v.y v.z with
    ⟨hI, hplus, hminus, h3⟩
  rw [hI, hplus, hminus, h3]
  have hyc :
      ((Complex.I * (v.y : ℂ) + Complex.I * (v.y : ℂ)) /
          (2 * Complex.I)) = (v.y : ℂ) := by
    field_simp
    ring
  have hy :
      ((Complex.I * (v.y : ℂ) + Complex.I * (v.y : ℂ)) /
          (2 * Complex.I)).re = v.y := by
    rw [hyc]
    simp
  ext <;>
    simp [zornBoundaryOfMinkowski4, xyPlaneVec, zornMk, hy]

/-! ## The existing Pauli-paravector/Zorn boundary readout -/

/- The Pauli matrix used by the geometric paravector owner is the same
   soldered matrix as the Weyl owner, after real coordinates are complexified. -/
theorem solder_real_eq_pauliMatrix (v : Minkowski4) :
    SolderingSpinConnectionBogoliubov.solder
        (v.t : ℂ) (v.x : ℂ) (v.y : ℂ) (v.z : ℂ) =
      pauliMatrix v := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [SolderingSpinConnectionBogoliubov.solder,
      SolderingSpinConnectionBogoliubov.σ1,
      SolderingSpinConnectionBogoliubov.σ2,
      SolderingSpinConnectionBogoliubov.σ3,
      pauliMatrix, toPauliParavector,
      InfoGeometry.Canonical.PauliHestenesSpinMomentum.PauliParavector.pauliMatrix]
    <;> ring
  · simp [SolderingSpinConnectionBogoliubov.solder,
      SolderingSpinConnectionBogoliubov.σ1,
      SolderingSpinConnectionBogoliubov.σ2,
      SolderingSpinConnectionBogoliubov.σ3,
      pauliMatrix, toPauliParavector,
      InfoGeometry.Canonical.PauliHestenesSpinMomentum.PauliParavector.pauliMatrix]
    <;> ring
  · simp [SolderingSpinConnectionBogoliubov.solder,
      SolderingSpinConnectionBogoliubov.σ1,
      SolderingSpinConnectionBogoliubov.σ2,
      SolderingSpinConnectionBogoliubov.σ3,
      pauliMatrix, toPauliParavector,
      InfoGeometry.Canonical.PauliHestenesSpinMomentum.PauliParavector.pauliMatrix]
    <;> ring
  · simp [SolderingSpinConnectionBogoliubov.solder,
      SolderingSpinConnectionBogoliubov.σ1,
      SolderingSpinConnectionBogoliubov.σ2,
      SolderingSpinConnectionBogoliubov.σ3,
      pauliMatrix, toPauliParavector,
      InfoGeometry.Canonical.PauliHestenesSpinMomentum.PauliParavector.pauliMatrix]
    <;> ring

/- The already existing Zorn boundary therefore has the same quadratic
   readout as the Pauli/Weyl soldering. -/
theorem zornBoundary_norm_eq_solder_det_re (v : Minkowski4) :
    zornNorm (zornBoundaryOfMinkowski4 v) =
      (Matrix.det
        (SolderingSpinConnectionBogoliubov.solder
          (v.t : ℂ) (v.x : ℂ) (v.y : ℂ) (v.z : ℂ))).re := by
  rw [solder_real_eq_pauliMatrix]
  exact zornNorm_boundary_eq_pauli_det_re v

theorem zornBoundary_null_iff_solder_det_zero (v : Minkowski4) :
    IsZornNull (zornBoundaryOfMinkowski4 v) ↔
      Matrix.det
        (SolderingSpinConnectionBogoliubov.solder
          (v.t : ℂ) (v.x : ℂ) (v.y : ℂ) (v.z : ℂ)) = 0 := by
  rw [isZornNull_boundary_iff_isNull, solder_real_eq_pauliMatrix,
    det_pauliMatrix]
  change v.q = 0 ↔ (v.q : ℂ) = 0
  constructor
  · intro h
    simpa [h]
  · intro h
    exact_mod_cast h

end InfoGeometry.Physics.ChiralCausalCone
