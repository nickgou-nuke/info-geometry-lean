import InfoGeometry.Clifford.Cl55SpinorChirality
import Mathlib.LinearAlgebra.Trace

noncomputable section
namespace InfoGeometry.Lie.Pin55KreinConformalBridge

open InfoGeometry.CliffordTower

def χ : SplitSpace 5 →ₗ[ℝ] SplitSpace 5 :=
  { toFun := fun v => ((-v.1.1, v.1.2), ((-v.2.1.1, v.2.1.2), ((-v.2.2.1.1, v.2.2.1.2), ((-v.2.2.2.1.1, v.2.2.2.1.2), ((-v.2.2.2.2.1.1, v.2.2.2.2.1.2), 0)))))
    map_add' := fun x y => by
      rcases x with ⟨⟨t0, s0⟩, ⟨t1, s1⟩, ⟨t2, s2⟩, ⟨t3, s3⟩, ⟨t4, s4⟩, u⟩
      rcases y with ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, w⟩
      dsimp
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
      · refine Prod.ext ?_ ?_ <;> ring
      · refine Prod.ext ?_ ?_ <;> ring
      · refine Prod.ext ?_ ?_ <;> ring
      · refine Prod.ext ?_ ?_ <;> ring
      · refine Prod.ext ?_ ?_
        · refine Prod.ext ?_ ?_ <;> ring
        · ext i <;> nomatch i
    map_smul' := fun c x => by
      rcases x with ⟨⟨t0, s0⟩, ⟨t1, s1⟩, ⟨t2, s2⟩, ⟨t3, s3⟩, ⟨t4, s4⟩, u⟩
      dsimp
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
      · refine Prod.ext ?_ ?_ <;> ring
      · refine Prod.ext ?_ ?_ <;> ring
      · refine Prod.ext ?_ ?_ <;> ring
      · refine Prod.ext ?_ ?_ <;> ring
      · refine Prod.ext ?_ ?_
        · refine Prod.ext ?_ ?_ <;> ring
        · ext i <;> nomatch i }

def ε : SplitSpace 5 →ₗ[ℝ] SplitSpace 5 :=
  { toFun := fun v => ((-v.1.1, -v.1.2), ((-v.2.1.1, -v.2.1.2), ((v.2.2.1.1, v.2.2.1.2), ((v.2.2.2.1.1, v.2.2.2.1.2), ((v.2.2.2.2.1.1, v.2.2.2.2.1.2), 0)))))
    map_add' := fun x y => by
      rcases x with ⟨⟨t0, s0⟩, ⟨t1, s1⟩, ⟨t2, s2⟩, ⟨t3, s3⟩, ⟨t4, s4⟩, u⟩
      rcases y with ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, w⟩
      dsimp
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
      · refine Prod.ext ?_ ?_ <;> ring
      · refine Prod.ext ?_ ?_ <;> ring
      · refine Prod.ext ?_ ?_ <;> ring
      · refine Prod.ext ?_ ?_ <;> ring
      · refine Prod.ext ?_ ?_
        · refine Prod.ext ?_ ?_ <;> ring
        · ext i <;> nomatch i
    map_smul' := fun c x => by
      rcases x with ⟨⟨t0, s0⟩, ⟨t1, s1⟩, ⟨t2, s2⟩, ⟨t3, s3⟩, ⟨t4, s4⟩, u⟩
      dsimp
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
      · refine Prod.ext ?_ ?_ <;> ring
      · refine Prod.ext ?_ ?_ <;> ring
      · refine Prod.ext ?_ ?_ <;> ring
      · refine Prod.ext ?_ ?_ <;> ring
      · refine Prod.ext ?_ ?_
        · refine Prod.ext ?_ ?_ <;> ring
        · ext i <;> nomatch i }

theorem χ_sq : χ ∘ₗ χ = LinearMap.id := by
  refine LinearMap.ext (fun v => ?_)
  rcases v with ⟨⟨t0, s0⟩, ⟨t1, s1⟩, ⟨t2, s2⟩, ⟨t3, s3⟩, ⟨t4, s4⟩, u⟩
  dsimp [χ]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · refine Prod.ext ?_ ?_ <;> ring
  · refine Prod.ext ?_ ?_ <;> ring
  · refine Prod.ext ?_ ?_ <;> ring
  · refine Prod.ext ?_ ?_ <;> ring
  · refine Prod.ext ?_ ?_
    · refine Prod.ext ?_ ?_ <;> ring
    · ext i <;> nomatch i

theorem ε_sq : ε ∘ₗ ε = LinearMap.id := by
  refine LinearMap.ext (fun v => ?_)
  rcases v with ⟨⟨t0, s0⟩, ⟨t1, s1⟩, ⟨t2, s2⟩, ⟨t3, s3⟩, ⟨t4, s4⟩, u⟩
  dsimp [ε]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · refine Prod.ext ?_ ?_ <;> ring
  · refine Prod.ext ?_ ?_ <;> ring
  · refine Prod.ext ?_ ?_ <;> ring
  · refine Prod.ext ?_ ?_ <;> ring
  · refine Prod.ext ?_ ?_
    · refine Prod.ext ?_ ?_ <;> ring
    · ext i <;> nomatch i

end InfoGeometry.Lie.Pin55KreinConformalBridge
