import Mathlib.Tactic
import Omega.CircleDimension.CertificateInverseLimitAddressing

namespace Omega.CircleDimension

/-- Any cofinal nested dyadic certificate chain with shrinking diameter has a unique limit point. -/
theorem paper_cdim_dyadic_cofinal_sparsification {Cert : Type*} (left right : Cert → ℝ)
    (chain : ℕ → Cert)
    (hnested :
      ∀ n,
        Set.Icc (left (chain (n + 1))) (right (chain (n + 1))) ⊆
          Set.Icc (left (chain n)) (right (chain n)))
    (hdiam : ∀ ε > 0, ∃ N, ∀ n ≥ N, right (chain n) - left (chain n) < ε)
    (hclosed : ∀ n, left (chain n) ≤ right (chain n)) :
    ∃! θ : ℝ, ∀ n, θ ∈ Set.Icc (left (chain n)) (right (chain n)) := by
  let S : Set ℝ := Set.range fun n => left (chain n)
  have hleftMono : Monotone (fun n => left (chain n)) := by
    intro m n hmn
    induction hmn with
    | refl => exact le_rfl
    | @step n _ ih =>
        have hmem : left (chain (n + 1)) ∈
            Set.Icc (left (chain (n + 1))) (right (chain (n + 1))) :=
          ⟨le_rfl, hclosed (n + 1)⟩
        exact le_trans ih (hnested n hmem).1
  have hrightAnti : Antitone (fun n => right (chain n)) := by
    intro m n hmn
    induction hmn with
    | refl => exact le_rfl
    | @step n _ ih =>
        have hmem : right (chain (n + 1)) ∈
            Set.Icc (left (chain (n + 1))) (right (chain (n + 1))) :=
          ⟨hclosed (n + 1), le_rfl⟩
        exact le_trans (hnested n hmem).2 ih
  have hupper : ∀ n, ∀ x ∈ S, x ≤ right (chain n) := by
    intro n x hx
    rcases hx with ⟨m, rfl⟩
    rcases Nat.le_total m n with hmn | hnm
    · exact le_trans (hleftMono hmn) (hclosed n)
    · exact le_trans (hclosed m) (hrightAnti hnm)
  have hSnonempty : S.Nonempty := ⟨left (chain 0), ⟨0, rfl⟩⟩
  have hSbdd : BddAbove S := ⟨right (chain 0), hupper 0⟩
  refine ⟨sSup S, ?_, ?_⟩
  · intro n
    exact ⟨le_csSup hSbdd ⟨n, rfl⟩, csSup_le hSnonempty (hupper n)⟩
  intro η hη
  by_contra hne
  have hpos : 0 < |sSup S - η| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
  obtain ⟨N, hN⟩ := hdiam |sSup S - η| hpos
  have hsmall : right (chain N) - left (chain N) < |sSup S - η| := hN N le_rfl
  have hsSupN := show sSup S ∈ Set.Icc (left (chain N)) (right (chain N)) from
    ⟨le_csSup hSbdd ⟨N, rfl⟩, csSup_le hSnonempty (hupper N)⟩
  have hηN := hη N
  have hgap : |sSup S - η| ≤ right (chain N) - left (chain N) := by
    rcases le_total (sSup S) η with hle | hle
    · rw [abs_of_nonpos (sub_nonpos.mpr hle)]
      nlinarith [hsSupN.1, hsSupN.2, hηN.1, hηN.2]
    · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
      nlinarith [hsSupN.1, hsSupN.2, hηN.1, hηN.2]
  linarith

end Omega.CircleDimension
