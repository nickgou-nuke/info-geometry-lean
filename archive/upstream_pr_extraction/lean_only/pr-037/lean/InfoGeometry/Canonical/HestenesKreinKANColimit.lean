import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Canonical.FilteredHestenesIteratedTransport

/-!
# K/A/N interface transport on the Hestenes--Krein colimit

This owner is the real finite carrier for a Harish--Chandra/Iwasawa interface.
The three labels `compactK`, `hyperbolicA`, and `parabolicN` are predicates
supplied at each doubled stage.  Their compatibility is transported through
the native continuous-linear Hestenes cone.  The file proves only finite
predicate inheritance and representative equality; it does not assert an
Iwasawa decomposition, a spherical transform, a scattering formula, or
unitarity of a principal series.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinKANColimit

open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity
open InfoGeometry.Krein

structure StageSignatures (E : Type) where
  compactK : DoubledSpace E → Bool
  hyperbolicA : DoubledSpace E → Bool
  parabolicN : DoubledSpace E → Bool

structure LimitSignatures (E : Type) where
  compactK : DoubledSpace E → Bool
  hyperbolicA : DoubledSpace E → Bool
  parabolicN : DoubledSpace E → Bool

def limitSignatures
    {C : HestenesKreinCone}
    (stage : ∀ n, StageSignatures (C.Base n)) :
    LimitSignatures C.LimitBase := by
  classical
  exact {
    compactK := fun z =>
      if ∃ n x, C.ι n x = z ∧ (stage n).compactK x = true then true else false
    hyperbolicA := fun z =>
      if ∃ n x, C.ι n x = z ∧ (stage n).hyperbolicA x = true then true else false
    parabolicN := fun z =>
      if ∃ n x, C.ι n x = z ∧ (stage n).parabolicN x = true then true else false
  }

theorem limitSignatures_compactK_eq_true_iff
    {C : HestenesKreinCone}
    (stage : ∀ n, StageSignatures (C.Base n))
    (z : DoubledSpace C.LimitBase) :
    (limitSignatures stage).compactK z = true ↔
      ∃ n x, C.ι n x = z ∧ (stage n).compactK x = true := by
  classical
  simp [limitSignatures]

theorem limitSignatures_hyperbolicA_eq_true_iff
    {C : HestenesKreinCone}
    (stage : ∀ n, StageSignatures (C.Base n))
    (z : DoubledSpace C.LimitBase) :
    (limitSignatures stage).hyperbolicA z = true ↔
      ∃ n x, C.ι n x = z ∧ (stage n).hyperbolicA x = true := by
  classical
  simp [limitSignatures]

theorem limitSignatures_parabolicN_eq_true_iff
    {C : HestenesKreinCone}
    (stage : ∀ n, StageSignatures (C.Base n))
    (z : DoubledSpace C.LimitBase) :
    (limitSignatures stage).parabolicN z = true ↔
      ∃ n x, C.ι n x = z ∧ (stage n).parabolicN x = true := by
  classical
  simp [limitSignatures]

theorem limitSignatures_ext
    {C : HestenesKreinCone}
    {stage₁ stage₂ : ∀ n, StageSignatures (C.Base n)}
    (hK : ∀ n x, (stage₁ n).compactK x = (stage₂ n).compactK x)
    (hA : ∀ n x, (stage₁ n).hyperbolicA x = (stage₂ n).hyperbolicA x)
    (hN : ∀ n x, (stage₁ n).parabolicN x = (stage₂ n).parabolicN x) :
    limitSignatures stage₁ = limitSignatures stage₂ := by
  classical
  unfold limitSignatures
  congr 1
  · funext z
    have hz :
        (∃ n x, C.ι n x = z ∧ (stage₁ n).compactK x = true) ↔
          ∃ n x, C.ι n x = z ∧ (stage₂ n).compactK x = true := by
      constructor <;> rintro ⟨n, x, hx, h⟩
      · exact ⟨n, x, hx, hK n x ▸ h⟩
      · exact ⟨n, x, hx, (hK n x).symm ▸ h⟩
    simp only [hz]
  · funext z
    have hz :
        (∃ n x, C.ι n x = z ∧ (stage₁ n).hyperbolicA x = true) ↔
          ∃ n x, C.ι n x = z ∧ (stage₂ n).hyperbolicA x = true := by
      constructor <;> rintro ⟨n, x, hx, h⟩
      · exact ⟨n, x, hx, hA n x ▸ h⟩
      · exact ⟨n, x, hx, (hA n x).symm ▸ h⟩
    simp only [hz]
  · funext z
    have hz :
        (∃ n x, C.ι n x = z ∧ (stage₁ n).parabolicN x = true) ↔
          ∃ n x, C.ι n x = z ∧ (stage₂ n).parabolicN x = true := by
      constructor <;> rintro ⟨n, x, hx, h⟩
      · exact ⟨n, x, hx, hN n x ▸ h⟩
      · exact ⟨n, x, hx, (hN n x).symm ▸ h⟩
    simp only [hz]

theorem compactK_directLimit
    {C : HestenesKreinCone}
    (stage : ∀ n, StageSignatures (C.Base n))
    {n : ℕ} {x : DoubledSpace (C.Base n)}
    (hx : (stage n).compactK x = true) :
    (limitSignatures stage).compactK (C.ι n x) = true := by
  classical
  change (if h : ∃ m y, C.ι m y = C.ι n x ∧ (stage m).compactK y = true
    then true else false) = true
  rw [dif_pos]
  exact ⟨n, x, rfl, hx⟩

theorem hyperbolicA_directLimit
    {C : HestenesKreinCone}
    (stage : ∀ n, StageSignatures (C.Base n))
    {n : ℕ} {x : DoubledSpace (C.Base n)}
    (hx : (stage n).hyperbolicA x = true) :
    (limitSignatures stage).hyperbolicA (C.ι n x) = true := by
  classical
  change (if h : ∃ m y, C.ι m y = C.ι n x ∧ (stage m).hyperbolicA y = true
    then true else false) = true
  rw [dif_pos]
  exact ⟨n, x, rfl, hx⟩

theorem parabolicN_directLimit
    {C : HestenesKreinCone}
    (stage : ∀ n, StageSignatures (C.Base n))
    {n : ℕ} {x : DoubledSpace (C.Base n)}
    (hx : (stage n).parabolicN x = true) :
    (limitSignatures stage).parabolicN (C.ι n x) = true := by
  classical
  change (if h : ∃ m y, C.ι m y = C.ι n x ∧ (stage m).parabolicN y = true
    then true else false) = true
  rw [dif_pos]
  exact ⟨n, x, rfl, hx⟩

theorem property_bondIterate
    {C : HestenesKreinCone}
    (P : ∀ n, DoubledSpace (C.Base n) → Bool)
    (hP : ∀ n x, P n x = true → P (n + 1) (C.bond n x) = true) :
    ∀ n m x, P n x = true →
      P (n + m)
        (C.toFilteredPhaseCone.bondIterate n m x) = true := by
  intro n m
  induction m with
  | zero =>
      intro x hx
      simpa using hx
  | succ m ih =>
      intro x hx
      rw [FilteredPhaseCone.bondIterate_succ]
      exact hP (n + m)
        (C.toFilteredPhaseCone.bondIterate n m x)
        (ih x hx)

theorem compactK_bondIterate
    {C : HestenesKreinCone}
    (stage : ∀ n, StageSignatures (C.Base n))
    (hcompat : ∀ n x, (stage n).compactK x = true →
      (stage (n + 1)).compactK (C.bond n x) = true)
    (n m : ℕ) (x : DoubledSpace (C.Base n))
    (hx : (stage n).compactK x = true) :
    (stage (n + m)).compactK
      (C.toFilteredPhaseCone.bondIterate n m x) = true := by
  exact property_bondIterate (fun k y => (stage k).compactK y)
    hcompat n m x hx

theorem hyperbolicA_bondIterate
    {C : HestenesKreinCone}
    (stage : ∀ n, StageSignatures (C.Base n))
    (hcompat : ∀ n x, (stage n).hyperbolicA x = true →
      (stage (n + 1)).hyperbolicA (C.bond n x) = true)
    (n m : ℕ) (x : DoubledSpace (C.Base n))
    (hx : (stage n).hyperbolicA x = true) :
    (stage (n + m)).hyperbolicA
      (C.toFilteredPhaseCone.bondIterate n m x) := by
  exact property_bondIterate (fun k y => (stage k).hyperbolicA y)
    hcompat n m x hx

theorem parabolicN_bondIterate
    {C : HestenesKreinCone}
    (stage : ∀ n, StageSignatures (C.Base n))
    (hcompat : ∀ n x, (stage n).parabolicN x = true →
      (stage (n + 1)).parabolicN (C.bond n x) = true)
    (n m : ℕ) (x : DoubledSpace (C.Base n))
    (hx : (stage n).parabolicN x = true) :
    (stage (n + m)).parabolicN
      (C.toFilteredPhaseCone.bondIterate n m x) := by
  exact property_bondIterate (fun k y => (stage k).parabolicN y)
    hcompat n m x hx

theorem transported_point_eq
    {C : HestenesKreinCone} (n m : ℕ)
    (x : DoubledSpace (C.Base n)) :
    C.ι (n + m)
        (C.toFilteredPhaseCone.bondIterate n m x) = C.ι n x :=
  FilteredPhaseCone.ι_bondIterate_apply C.toFilteredPhaseCone n m x

theorem full_KAN_directLimit
    {C : HestenesKreinCone}
    (stage : ∀ n, StageSignatures (C.Base n))
    {n : ℕ} {x : DoubledSpace (C.Base n)}
    (hK : (stage n).compactK x = true)
    (hA : (stage n).hyperbolicA x = true)
    (hN : (stage n).parabolicN x = true) :
    (limitSignatures stage).compactK (C.ι n x) = true ∧
      (limitSignatures stage).hyperbolicA (C.ι n x) = true ∧
      (limitSignatures stage).parabolicN (C.ι n x) = true :=
  ⟨compactK_directLimit stage hK,
    hyperbolicA_directLimit stage hA,
    parabolicN_directLimit stage hN⟩

theorem full_KAN_bondIterate
    {C : HestenesKreinCone}
    (stage : ∀ n, StageSignatures (C.Base n))
    (hK : ∀ n x, (stage n).compactK x = true →
      (stage (n + 1)).compactK (C.bond n x) = true)
    (hA : ∀ n x, (stage n).hyperbolicA x = true →
      (stage (n + 1)).hyperbolicA (C.bond n x) = true)
    (hN : ∀ n x, (stage n).parabolicN x = true →
      (stage (n + 1)).parabolicN (C.bond n x) = true)
    (n m : ℕ) (x : DoubledSpace (C.Base n))
    (hx : (stage n).compactK x = true ∧
      (stage n).hyperbolicA x = true ∧
      (stage n).parabolicN x = true) :
    (stage (n + m)).compactK
        (C.toFilteredPhaseCone.bondIterate n m x) = true ∧
      (stage (n + m)).hyperbolicA
        (C.toFilteredPhaseCone.bondIterate n m x) = true ∧
      (stage (n + m)).parabolicN
        (C.toFilteredPhaseCone.bondIterate n m x) = true := by
  exact ⟨compactK_bondIterate stage hK n m x hx.1,
    hyperbolicA_bondIterate stage hA n m x hx.2.1,
    parabolicN_bondIterate stage hN n m x hx.2.2⟩

end InfoGeometry.Canonical.HestenesKreinKANColimit

end noncomputable section
