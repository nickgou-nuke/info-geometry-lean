import InfoGeometry.External.Auto.YangBaxterZornBridge
import InfoGeometry.External.Auto.ZornScalingFlow

/-!
# Scaling covariance of the Zorn braid representation

This module transports the canonical Zorn scaling action to the common
`Fin 8` coordinate carrier.  On the sixth-root automorphism locus it proves
that coordinate scaling conjugates every left-regular matrix to left
multiplication by the scaled Zorn element.

The API deliberately separates two layers:

* `scaledZornPhi p` is an inner conjugate of `zornPhi` for every `p : ℂˣ`,
  so its kernel, range up to conjugacy, faithfulness, and spectral invariants
  are unconditional;
* identifying that conjugation with left multiplication by `zornScale p X`
  requires `(p : ℂ) ^ 6 = 1`, exactly the locus where `zornScale` preserves
  the canonical Zorn multiplication.
-/

noncomputable section

namespace InfoGeometry.External.Auto.ZornBraidScalingCovariance

open Matrix
open InfoGeometry.External.Auto.SplitOctonionBraidSU3
open InfoGeometry.External.Auto.YangBaxterZornBridge

/-- Left multiplication by an arbitrary canonical Zorn element in `Fin 8` coordinates. -/
def leftRegularMatrix (X : Zorn) : Matrix (Fin 8) (Fin 8) ℂ :=
  fun i j =>
    let e_j : Fin 8 → ℂ := fun x => if x = j then 1 else 0
    zornToFin8 (zornMul X (fin8ToZorn e_j)) i

/-- Coordinate matrix of the unit scaling transformation. -/
def scaleMatrix (p : ℂˣ) : Matrix (Fin 8) (Fin 8) ℂ :=
  fun i j =>
    let e_j : Fin 8 → ℂ := fun x => if x = j then 1 else 0
    zornToFin8 (ZornScalingFlow.zornScale p (fin8ToZorn e_j)) i

/-- The generic left-regular matrix acts by canonical Zorn multiplication. -/
theorem leftRegularMatrix_mulVec (X : Zorn) (v : Fin 8 → ℂ) :
    leftRegularMatrix X *ᵥ v =
      zornToFin8 (zornMul X (fin8ToZorn v)) := by
  ext r
  fin_cases r <;>
    simp [leftRegularMatrix, Matrix.mulVec, dotProduct, zornToFin8,
      fin8ToZorn, zornMul, dot3, cross3, Fin.sum_univ_eight] <;> ring

/-- The scaling matrix acts by `zornScale` under the coordinate equivalence. -/
theorem scaleMatrix_mulVec (p : ℂˣ) (v : Fin 8 → ℂ) :
    scaleMatrix p *ᵥ v =
      zornToFin8 (ZornScalingFlow.zornScale p (fin8ToZorn v)) := by
  ext r
  fin_cases r <;>
    simp [scaleMatrix, Matrix.mulVec, dotProduct, zornToFin8,
      fin8ToZorn, ZornScalingFlow.zornScale]

/-- The generic construction recovers the existing Clifford matrices. -/
theorem leftRegularMatrix_Q_k (k : Fin 3) :
    leftRegularMatrix (Q_k k) = LeftMulQ k := by
  rfl

/-- The generic construction recovers the existing braid-generator matrices. -/
theorem leftRegularMatrix_R_k (k : Fin 3) :
    leftRegularMatrix (R_k k) = LeftMulR k := by
  rfl

/-- Coordinate scaling by `p⁻¹` is the inverse of coordinate scaling by `p`. -/
theorem scaleMatrix_mul_inv (p : ℂˣ) :
    scaleMatrix p * scaleMatrix p⁻¹ = (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  apply Matrix.mulVec_injective
  funext v
  rw [← Matrix.mulVec_mulVec, scaleMatrix_mulVec, scaleMatrix_mulVec,
    fin8ToZorn_zornToFin8]
  rw [ZornScalingFlow.zornScale_mul_parameter]
  simp [ZornScalingFlow.zornScale_one, zornToFin8_fin8ToZorn]

/-- The inverse scaling matrix also composes on the other side. -/
theorem scaleMatrix_inv_mul (p : ℂˣ) :
    scaleMatrix p⁻¹ * scaleMatrix p = (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  apply Matrix.mulVec_injective
  funext v
  rw [← Matrix.mulVec_mulVec, scaleMatrix_mulVec, scaleMatrix_mulVec,
    fin8ToZorn_zornToFin8]
  rw [ZornScalingFlow.zornScale_mul_parameter]
  simp [ZornScalingFlow.zornScale_one, zornToFin8_fin8ToZorn]

/-- The scaling matrix packaged as an element of `GL₈(ℂ)`. -/
def scaleUnit (p : ℂˣ) : GL8 where
  val := scaleMatrix p
  inv := scaleMatrix p⁻¹
  val_inv := scaleMatrix_mul_inv p
  inv_val := scaleMatrix_inv_mul p

/--
On the algebra-automorphism locus, coordinate scaling conjugates the complete
left-regular representation.
-/
theorem scale_conjugates_left_regular
    (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1) (X : Zorn) :
    scaleMatrix p * leftRegularMatrix X * scaleMatrix p⁻¹ =
      leftRegularMatrix (ZornScalingFlow.zornScale p X) := by
  apply Matrix.mulVec_injective
  funext v
  simp only [← Matrix.mulVec_mulVec]
  rw [scaleMatrix_mulVec, leftRegularMatrix_mulVec, scaleMatrix_mulVec,
    fin8ToZorn_zornToFin8, fin8ToZorn_zornToFin8,
    ZornScalingFlow.zornScale_zornMul_of_pow_six_eq_one p hp]
  rw [ZornScalingFlow.zornScale_mul_parameter]
  simp [ZornScalingFlow.zornScale_one]
  rw [leftRegularMatrix_mulVec]

/-- The scaled Clifford generator is its explicit `+2` and `-2` weight decomposition. -/
def scaledQ (p : ℂˣ) (k : Fin 3) : Zorn :=
  ZornScalingFlow.zornScale p (Q_k k)

/-- The scaled unnormalized braid generator. -/
def scaledR (p : ℂˣ) (k : Fin 3) : Zorn :=
  ZornScalingFlow.zornScale p (R_k k)

theorem scaledQ_formula (p : ℂˣ) (k : Fin 3) :
    scaledQ p k =
      zornAdd (zornSmul ((p : ℂ) ^ 2) (E_k k))
        (zornSmul (((p : ℂ)⁻¹) ^ 2) (F_k k)) := by
  exact ZornScalingFlow.zornScale_Q_k p k

/-- The existing braid matrix is carried to left multiplication by `scaledR`. -/
theorem scale_conjugates_LeftMulR
    (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1) (k : Fin 3) :
    scaleMatrix p * LeftMulR k * scaleMatrix p⁻¹ =
      leftRegularMatrix (scaledR p k) := by
  rw [← leftRegularMatrix_R_k]
  exact scale_conjugates_left_regular p hp (R_k k)

/-! ## Conjugated braid representation -/

/-- Inner conjugation by an element of `GL₈(ℂ)` as a group homomorphism. -/
def conjugationHom (S : GL8) : GL8 →* GL8 where
  toFun A := S * A * S⁻¹
  map_one' := by simp only [mul_one, mul_inv_cancel]
  map_mul' := by
    intro A B
    group

/-- The two scaled packaged braid generators. -/
def scaledBraidGen1 (p : ℂˣ) : GL8 :=
  scaleUnit p * braidGen1 * (scaleUnit p)⁻¹

def scaledBraidGen2 (p : ℂˣ) : GL8 :=
  scaleUnit p * braidGen2 * (scaleUnit p)⁻¹

/-- The scaled packaged generators satisfy the Artin relation. -/
theorem scaledBraidGen_B3_braid (p : ℂˣ) :
    scaledBraidGen1 p * scaledBraidGen2 p * scaledBraidGen1 p =
      scaledBraidGen2 p * scaledBraidGen1 p * scaledBraidGen2 p := by
  have h := congrArg (conjugationHom (scaleUnit p)) braidGen_B3_braid
  simpa only [map_mul, scaledBraidGen1, scaledBraidGen2, conjugationHom] using h

/-- The conjugated Zorn representation of the presented braid group. -/
def scaledZornPhi (p : ℂˣ) : B3PresentedGroup.B3 →* GL8 :=
  (conjugationHom (scaleUnit p)).comp zornPhi

/-- Representation-level conjugation covariance for every braid word. -/
theorem scaledZornPhi_conjugate (p : ℂˣ) (β : B3PresentedGroup.B3) :
    scaledZornPhi p β = scaleUnit p * zornPhi β * (scaleUnit p)⁻¹ := by
  rfl

/-- Trace is constant across the conjugated family of braid representations. -/
theorem scaledZornPhi_trace (p : ℂˣ) (β : B3PresentedGroup.B3) :
    Matrix.trace (scaledZornPhi p β).val = Matrix.trace (zornPhi β).val := by
  rw [scaledZornPhi_conjugate]
  exact Matrix.trace_units_conj (scaleUnit p) (zornPhi β).val

/-- Determinant is constant across the conjugated family of braid representations. -/
theorem scaledZornPhi_det (p : ℂˣ) (β : B3PresentedGroup.B3) :
    Matrix.det (scaledZornPhi p β).val = Matrix.det (zornPhi β).val := by
  rw [scaledZornPhi_conjugate]
  exact Matrix.det_units_conj (scaleUnit p) (zornPhi β).val

/-- Characteristic polynomial is constant across the conjugated representation family. -/
theorem scaledZornPhi_charpoly (p : ℂˣ) (β : B3PresentedGroup.B3) :
    Matrix.charpoly (scaledZornPhi p β).val =
      Matrix.charpoly (zornPhi β).val := by
  rw [scaledZornPhi_conjugate]
  exact Matrix.charpoly_units_conj (scaleUnit p) (zornPhi β).val

/-- Inner conjugation does not change the kernel of the braid representation. -/
theorem scaledZornPhi_ker (p : ℂˣ) :
    MonoidHom.ker (scaledZornPhi p) = MonoidHom.ker zornPhi := by
  ext β
  simp only [MonoidHom.mem_ker, scaledZornPhi_conjugate]
  constructor
  · intro h
    have h' := congrArg (fun A : GL8 => (scaleUnit p)⁻¹ * A * scaleUnit p) h
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right,
      inv_mul_cancel, mul_one, one_mul] using h'
  · intro h
    rw [h]
    group

/-- Conjugating the representation preserves and reflects faithfulness. -/
theorem scaledZornPhi_injective_iff (p : ℂˣ) :
    Function.Injective (scaledZornPhi p) ↔ Function.Injective zornPhi := by
  rw [← MonoidHom.ker_eq_bot_iff, ← MonoidHom.ker_eq_bot_iff,
    scaledZornPhi_ker]

/-- The scaled image is the image subgroup transported by inner conjugation. -/
theorem scaledZornPhi_range (p : ℂˣ) :
    MonoidHom.range (scaledZornPhi p) =
      (MonoidHom.range zornPhi).map (conjugationHom (scaleUnit p)) := by
  exact MonoidHom.range_comp (conjugationHom (scaleUnit p)) zornPhi

theorem scaledZornPhi_sig0 (p : ℂˣ) :
    scaledZornPhi p
        (PresentedGroup.of B3PresentedGroup.B3Gen.sig0 : B3PresentedGroup.B3) =
      scaledBraidGen1 p := by
  rw [scaledZornPhi_conjugate, zornPhi_sig0]
  rfl

theorem scaledZornPhi_sig1 (p : ℂˣ) :
    scaledZornPhi p
        (PresentedGroup.of B3PresentedGroup.B3Gen.sig1 : B3PresentedGroup.B3) =
      scaledBraidGen2 p := by
  rw [scaledZornPhi_conjugate, zornPhi_sig1]
  rfl

/-- The first conjugated packaged generator has the expected scaled matrix value. -/
theorem scaledBraidGen1_val
    (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1) :
    (scaledBraidGen1 p).val = leftRegularMatrix (scaledR p 0) := by
  change scaleMatrix p * LeftMulR 0 * scaleMatrix p⁻¹ =
    leftRegularMatrix (scaledR p 0)
  exact scale_conjugates_LeftMulR p hp 0

/-- The second conjugated packaged generator has the expected scaled matrix value. -/
theorem scaledBraidGen2_val
    (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1) :
    (scaledBraidGen2 p).val = leftRegularMatrix (scaledR p 1) := by
  change scaleMatrix p * LeftMulR 1 * scaleMatrix p⁻¹ =
    leftRegularMatrix (scaledR p 1)
  exact scale_conjugates_LeftMulR p hp 1

/-- On the automorphism locus, the first scaled representation generator is `L_(scaledR p 0)`. -/
theorem scaledZornPhi_sig0_val
    (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1) :
    (scaledZornPhi p
      (PresentedGroup.of B3PresentedGroup.B3Gen.sig0 : B3PresentedGroup.B3)).val =
      leftRegularMatrix (scaledR p 0) := by
  rw [scaledZornPhi_sig0]
  change scaleMatrix p * LeftMulR 0 * scaleMatrix p⁻¹ =
    leftRegularMatrix (scaledR p 0)
  exact scale_conjugates_LeftMulR p hp 0

/-- On the automorphism locus, the second scaled representation generator is `L_(scaledR p 1)`. -/
theorem scaledZornPhi_sig1_val
    (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1) :
    (scaledZornPhi p
      (PresentedGroup.of B3PresentedGroup.B3Gen.sig1 : B3PresentedGroup.B3)).val =
      leftRegularMatrix (scaledR p 1) := by
  rw [scaledZornPhi_sig1]
  change scaleMatrix p * LeftMulR 1 * scaleMatrix p⁻¹ =
    leftRegularMatrix (scaledR p 1)
  exact scale_conjugates_LeftMulR p hp 1

/-- The scaled left-regular braid matrices satisfy the Artin relation. -/
theorem scaled_leftMul_braid
    (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1) :
    leftRegularMatrix (scaledR p 0) * leftRegularMatrix (scaledR p 1) *
        leftRegularMatrix (scaledR p 0) =
      leftRegularMatrix (scaledR p 1) * leftRegularMatrix (scaledR p 0) *
        leftRegularMatrix (scaledR p 1) := by
  have h := congrArg Units.val (scaledBraidGen_B3_braid p)
  change
    (scaledBraidGen1 p).val * (scaledBraidGen2 p).val * (scaledBraidGen1 p).val =
      (scaledBraidGen2 p).val * (scaledBraidGen1 p).val * (scaledBraidGen2 p).val at h
  rw [scaledBraidGen1_val p hp, scaledBraidGen2_val p hp] at h
  simpa only using h

end InfoGeometry.External.Auto.ZornBraidScalingCovariance

end noncomputable section
