import InfoGeometry.Meta.Architecture
import InfoGeometry.Arithmetic.PrimeBooleanCube
import InfoGeometry.Arithmetic.PrimeMajoranaCAR
import InfoGeometry.Arithmetic.PrimeMajoranaInfiniteCAR

/-!
# InfoGeometry.Arithmetic.PrimeInfiniteArithmeticDictionary

Image-local arithmetic dictionary for the infinite transported prime-Majorana CAR lane.

This module consumes the owner-side image theorem corridor from
`PrimeMajoranaInfiniteCAR` and proves only readout facts for explicit stage images
inside a target ring.

Safe content:
- image-local CAR parity readout equals Boolean local parity;
- occupied local mode reads back as `-1`;
- vacant local mode reads back as `+1`.

No analytic continuation.
No Euler product.
No global infinite-state chirality theorem.
-/

noncomputable section

namespace PrimeInfiniteArithmeticDictionary

open InfoGeometry.Arithmetic.PrimeBooleanCube
open InfoGeometry.Arithmetic.PrimeMajoranaCAR (ExteriorCARPair)
open InfoGeometry.Arithmetic.PrimeMajoranaInfiniteCAR

/--
If the stage-`n` image of the transported number operator reads out as Boolean
occupation, then the stage-`n` image of the transported parity operator reads
out as the Boolean local parity `1 - 2N_p`.
-/
@[bridge_target_tag, rep_depth thermo]
theorem carParity_limit_readout_eq_booleanLocalParity
    {A : ℕ → Type*} [∀ n : ℕ, Ring (A n)]
    {L : Type*} [Ring L]
    (ι : ∀ n : ℕ, A n →+* L)
    (P : ∀ n : ℕ, ExteriorCARPair (A n))
    (χ : L →+* ℤ)
    (n p : ℕ)
    (S : Finset ℕ)
    (hN : χ (ι n ((P n).numberOp)) = occupationInt p S) :
    χ (ι n ((P n).parityOp)) = localParity p S := by
  have hpar' : χ (ι n ((P n).parityOp)) = 1 - 2 * χ (ι n ((P n).numberOp)) := by
    rw [exteriorCARPair_limit_image_parityOp_eq_one_sub_two_numberOp
      (A := A) (L := L) (ι := ι) (P := P) n]
    rw [map_sub, map_one, map_mul]
    have h2 : χ (2 : L) = (2 : ℤ) := by
      exact map_natCast χ 2
    rw [h2]
  by_cases hp : p ∈ S
  · have hOcc : χ (ι n ((P n).numberOp)) = 1 := by
      simpa [occupationInt, hp] using hN
    rw [localParity_eq_neg_one_of_mem hp]
    rw [hpar', hOcc]
    norm_num
  · have hOcc : χ (ι n ((P n).numberOp)) = 0 := by
      simpa [occupationInt, hp] using hN
    rw [localParity_eq_one_of_not_mem hp]
    rw [hpar', hOcc]
    norm_num

/-- Occupied local mode: the transported CAR parity image reads back as `-1`. -/
@[bridge_target_tag, rep_depth thermo]
theorem carParity_limit_readout_eq_neg_one_of_mem
    {A : ℕ → Type*} [∀ n : ℕ, Ring (A n)]
    {L : Type*} [Ring L]
    (ι : ∀ n : ℕ, A n →+* L)
    (P : ∀ n : ℕ, ExteriorCARPair (A n))
    (χ : L →+* ℤ)
    (n p : ℕ)
    {S : Finset ℕ}
    (hp : p ∈ S)
    (hN : χ (ι n ((P n).numberOp)) = occupationInt p S) :
    χ (ι n ((P n).parityOp)) = -1 := by
  rw [carParity_limit_readout_eq_booleanLocalParity ι P χ n p S hN]
  exact localParity_eq_neg_one_of_mem hp

/-- Vacant local mode: the transported CAR parity image reads back as `+1`. -/
@[bridge_target_tag, rep_depth thermo]
theorem carParity_limit_readout_eq_one_of_not_mem
    {A : ℕ → Type*} [∀ n : ℕ, Ring (A n)]
    {L : Type*} [Ring L]
    (ι : ∀ n : ℕ, A n →+* L)
    (P : ∀ n : ℕ, ExteriorCARPair (A n))
    (χ : L →+* ℤ)
    (n p : ℕ)
    {S : Finset ℕ}
    (hp : p ∉ S)
    (hN : χ (ι n ((P n).numberOp)) = occupationInt p S) :
    χ (ι n ((P n).parityOp)) = 1 := by
  rw [carParity_limit_readout_eq_booleanLocalParity ι P χ n p S hN]
  exact localParity_eq_one_of_not_mem hp

end PrimeInfiniteArithmeticDictionary
