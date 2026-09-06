import InfoGeometry.Canonical.JordanWignerCelikKocakBridgeNDepth

/-!
# Finite two-site Jordan--Wigner closure

The one-site Çelik--Koçak packet proves nilpotency and the diagonal CAR
relation.  This owner adds the first genuinely multi-site closure theorem on
the native finite Cantor function space.  It is deliberately concrete: it
does not claim an all-depth theorem or an infinite Fock representation.
-/

noncomputable section

namespace InfoGeometry.Canonical.JordanWignerCelikKocakBridgeNDepth

open InfoGeometry.Canonical.CelikKocakCantorOperators

private lemma address_two_ext
    (x : ((Fin 2) → Bool))
    (h0 : x 0 = b0) (h1 : x 1 = b1) :
    x = fun k => if k = 0 then b0 else b1 := by
  funext k
  fin_cases k
  · simpa using h0
  · simpa using h1

private lemma two_site_pointwise_zero
    (op : (((Fin 2 → Bool) → ℂ) →ₗ[ℂ] ((Fin 2 → Bool) → ℂ)))
    (f : (((Fin 2) → Bool) → ℂ)) (x : ((Fin 2) → Bool))
    (h : ∀ b0 b1 : Bool,
      op f (fun k => if k = 0 then b0 else b1) = 0) :
    op f x = 0 := by
  cases h0 : x 0 <;> cases h1 : x 1
  · rw [address_two_ext x h0 h1]
    exact h false false
  · rw [address_two_ext x h0 h1]
    exact h false true
  · rw [address_two_ext x h0 h1]
    exact h true false
  · rw [address_two_ext x h0 h1]
    exact h true true

private lemma address_flip_comm (x : ((Fin 2) → Bool)) :
    CantorAddress.flipAt (1 : Fin 2)
        (CantorAddress.flipAt (0 : Fin 2) x) =
      CantorAddress.flipAt (0 : Fin 2)
        (CantorAddress.flipAt (1 : Fin 2) x) := by
  exact CantorAddress.flipAt_comm (i := (1 : Fin 2)) (j := (0 : Fin 2)) (by decide) _

theorem cantorCreation_two_sites_anticommute :
    cantorCreation 2 0 * cantorCreation 2 1 +
      cantorCreation 2 1 * cantorCreation 2 0 = 0 := by
  apply LinearMap.ext
  intro f
  apply funext
  intro x
  apply two_site_pointwise_zero
  intro b0 b1
  cases b0 <;> cases b1 <;>
    simp [cantorCreation_apply, cantorCreation, prefixSign,
      CantorAddress.flipAt, address_flip_comm, Bool.not_not]

theorem cantorAnnihilation_two_sites_anticommute :
    cantorAnnihilation 2 0 * cantorAnnihilation 2 1 +
      cantorAnnihilation 2 1 * cantorAnnihilation 2 0 = 0 := by
  apply LinearMap.ext
  intro f
  apply funext
  intro x
  apply two_site_pointwise_zero
  intro b0 b1
  cases b0 <;> cases b1 <;>
    simp [cantorAnnihilation_apply, cantorAnnihilation, prefixSign,
      CantorAddress.flipAt, address_flip_comm, Bool.not_not]

theorem cantorAnnihilation_creation_two_sites_anticommute :
    cantorAnnihilation 2 0 * cantorCreation 2 1 +
      cantorCreation 2 1 * cantorAnnihilation 2 0 = 0 := by
  apply LinearMap.ext
  intro f
  apply funext
  intro x
  apply two_site_pointwise_zero
  intro b0 b1
  cases b0 <;> cases b1 <;>
    simp [cantorAnnihilation_apply, cantorCreation_apply,
      cantorAnnihilation, cantorCreation, prefixSign,
      CantorAddress.flipAt, address_flip_comm, Bool.not_not]

theorem cantorCreation_annihilation_two_sites_anticommute :
    cantorCreation 2 0 * cantorAnnihilation 2 1 +
      cantorAnnihilation 2 1 * cantorCreation 2 0 = 0 := by
  apply LinearMap.ext
  intro f
  apply funext
  intro x
  apply two_site_pointwise_zero
  intro b0 b1
  cases b0 <;> cases b1 <;>
    simp [cantorAnnihilation_apply, cantorCreation_apply,
      cantorAnnihilation, cantorCreation, prefixSign,
      CantorAddress.flipAt, address_flip_comm, Bool.not_not]

theorem cantor_two_site_CAR_closure :
    cantorCreation 2 0 * cantorCreation 2 0 = 0 ∧
    cantorCreation 2 1 * cantorCreation 2 1 = 0 ∧
    cantorAnnihilation 2 0 * cantorAnnihilation 2 0 = 0 ∧
    cantorAnnihilation 2 1 * cantorAnnihilation 2 1 = 0 ∧
    cantorAnnihilation 2 0 * cantorCreation 2 0 +
        cantorCreation 2 0 * cantorAnnihilation 2 0 = 1 ∧
    cantorAnnihilation 2 1 * cantorCreation 2 1 +
        cantorCreation 2 1 * cantorAnnihilation 2 1 = 1 ∧
    (cantorCreation 2 0 * cantorCreation 2 1 +
      cantorCreation 2 1 * cantorCreation 2 0 = 0) ∧
    (cantorAnnihilation 2 0 * cantorAnnihilation 2 1 +
      cantorAnnihilation 2 1 * cantorAnnihilation 2 0 = 0) ∧
    (cantorAnnihilation 2 0 * cantorCreation 2 1 +
      cantorCreation 2 1 * cantorAnnihilation 2 0 = 0) ∧
    (cantorCreation 2 0 * cantorAnnihilation 2 1 +
      cantorAnnihilation 2 1 * cantorCreation 2 0 = 0) := by
  refine ⟨cantorCreation_sq_zero 2 0,
    cantorCreation_sq_zero 2 1,
    cantorAnnihilation_sq_zero 2 0,
    cantorAnnihilation_sq_zero 2 1,
    cantorAnnihilation_creation_anticomm_self 2 0,
    cantorAnnihilation_creation_anticomm_self 2 1,
    cantorCreation_two_sites_anticommute,
    cantorAnnihilation_two_sites_anticommute,
    cantorAnnihilation_creation_two_sites_anticommute,
    cantorCreation_annihilation_two_sites_anticommute⟩

end InfoGeometry.Canonical.JordanWignerCelikKocakBridgeNDepth
