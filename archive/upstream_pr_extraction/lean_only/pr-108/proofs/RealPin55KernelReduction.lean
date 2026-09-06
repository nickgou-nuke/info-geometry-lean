import proofs.RealPin55Kernel

/-! # Clifford reduction of the kernel of the Pin(5,5) action -/

noncomputable section
namespace RealPin55KernelReduction

open Clifford55
open RealPin55Core
open RealPin55TwistedAction
open RealPin55MatrixRepresentation
open RealPin55Kernel
open V55Fin10Coordinates

def gradeEvenPart (x : Cl55) : Cl55 :=
  (2 : ℝ)⁻¹ • (x + CliffordAlgebra.involute x)

def gradeOddPart (x : Cl55) : Cl55 :=
  (2 : ℝ)⁻¹ • (x - CliffordAlgebra.involute x)

theorem gradeEven_add_gradeOdd (x : Cl55) :
    gradeEvenPart x + gradeOddPart x = x := by
  simp [gradeEvenPart, gradeOddPart]
  module

theorem involute_eq_even_sub_odd (x : Cl55) :
    CliffordAlgebra.involute x = gradeEvenPart x - gradeOddPart x := by
  simp [gradeEvenPart, gradeOddPart]
  module

theorem twistedVector_eq_of_mem_kernel {g : FullPin55}
    (hg : g ∈ MonoidHom.ker fullPinToO55) (v : V55) :
    twistedVector g v = v := by
  apply v55Fin10Equiv.injective
  have hm := fullPinMatrix_mulVec g v
  have hunit : fullPinMatrixRepresentation g = 1 := by
    have hg' : fullPinToO55 g = 1 := hg
    exact congrArg Subtype.val hg'
  rw [hunit] at hm
  simpa using hm.symm

theorem kernel_twisted_relation {g : FullPin55}
    (hg : g ∈ MonoidHom.ker fullPinToO55) (v : V55) :
    CliffordAlgebra.involute (g.1 : Cl55) * ι55 v =
      ι55 v * (g.1 : Cl55) := by
  have hv := iota_twistedVector g v
  rw [twistedVector_eq_of_mem_kernel hg] at hv
  have hright : (((g.1⁻¹ : Cl55ˣ) : Cl55) * (g.1 : Cl55)) = 1 := by
    change (((g.1⁻¹ * g.1 : Cl55ˣ) : Cl55)) = 1
    simp
  calc
    CliffordAlgebra.involute (g.1 : Cl55) * ι55 v =
        (CliffordAlgebra.involute (g.1 : Cl55) * ι55 v *
          ((g.1⁻¹ : Cl55ˣ) : Cl55)) * (g.1 : Cl55) := by
            rw [mul_assoc, hright, mul_one]
    _ = ι55 v * (g.1 : Cl55) := by rw [← hv]

theorem kernel_reverse_twisted_relation {g : FullPin55}
    (hg : g ∈ MonoidHom.ker fullPinToO55) (v : V55) :
    (g.1 : Cl55) * ι55 v =
      ι55 v * CliffordAlgebra.involute (g.1 : Cl55) := by
  have h := congrArg CliffordAlgebra.involute (kernel_twisted_relation hg v)
  simpa only [map_mul, CliffordAlgebra.involute_involute,
    CliffordAlgebra.involute_ι, neg_mul, mul_neg, neg_inj] using h

theorem kernel_even_commutes {g : FullPin55}
    (hg : g ∈ MonoidHom.ker fullPinToO55) (v : V55) :
    gradeEvenPart (g.1 : Cl55) * ι55 v =
      ι55 v * gradeEvenPart (g.1 : Cl55) := by
  have h1 := kernel_twisted_relation hg v
  have h2 := kernel_reverse_twisted_relation hg v
  unfold gradeEvenPart
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  rw [h2, h1]
  module

theorem kernel_odd_anticommutes {g : FullPin55}
    (hg : g ∈ MonoidHom.ker fullPinToO55) (v : V55) :
    gradeOddPart (g.1 : Cl55) * ι55 v =
      -(ι55 v * gradeOddPart (g.1 : Cl55)) := by
  have h1 := kernel_twisted_relation hg v
  have h2 := kernel_reverse_twisted_relation hg v
  unfold gradeOddPart
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm]
  rw [h2, h1]
  module

end RealPin55KernelReduction
end noncomputable section
