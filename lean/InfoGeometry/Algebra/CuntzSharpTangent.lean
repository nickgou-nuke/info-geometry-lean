import Mathlib

/-!
# Cuntz tangents for an explicit involution

The involution is an explicit parameter, so operator algebras may use the
Krein adjoint without replacing the ordinary Hilbert-adjoint `Star` instance.
-/

namespace InfoGeometry.Algebra.Cuntz

variable {A : Type*} [Ring A]
variable {N : ℕ} (sharp : A → A)

structure InvolutiveDerivation where
  toAddHom : A →+ A
  leibniz' : ∀ x y,
    toAddHom (x * y) = toAddHom x * y + x * toAddHom y
  sharp' : ∀ x,
    toAddHom (sharp x) = sharp (toAddHom x)

instance : CoeFun (InvolutiveDerivation (A := A) sharp) (fun _ => A → A) :=
  ⟨fun D => D.toAddHom⟩

structure SharpCuntzFamily where
  S : Fin N → A
  isometry : ∀ i j,
    sharp (S i) * S j = if i = j then 1 else 0
  range_sum : ∑ i : Fin N, S i * sharp (S i) = 1

structure SharpCuntzTangent (O : SharpCuntzFamily (N := N) sharp) where
  X : Fin N → A
  tangent_isometry : ∀ i j,
    sharp (X i) * O.S j + sharp (O.S i) * X j = 0
  tangent_complete :
    ∑ i : Fin N,
      (X i * sharp (O.S i) + O.S i * sharp (X i)) = 0

lemma InvolutiveDerivation.map_zero
    (D : InvolutiveDerivation (A := A) sharp) : D 0 = 0 :=
  D.toAddHom.map_zero

lemma InvolutiveDerivation.map_one
    (D : InvolutiveDerivation (A := A) sharp) : D 1 = 0 := by
  have h := D.leibniz' (1 : A) 1
  have h' := congrArg (fun z => z - D 1) h
  have hz : (0 : A) = D 1 := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
  exact hz.symm

noncomputable def InvolutiveDerivation.cuntzTangent
    (D : InvolutiveDerivation (A := A) sharp)
    (O : SharpCuntzFamily (N := N) sharp) :
    SharpCuntzTangent sharp O := by
  let X : Fin N → A := fun i => D (O.S i)
  have hD1 : D (1 : A) = 0 := D.map_one
  have hisometry (i j : Fin N) :
      D (sharp (O.S i) * O.S j) =
        sharp (X i) * O.S j + sharp (O.S i) * X j := by
    rw [D.leibniz', D.sharp']
  have hsum :
      D (∑ i : Fin N, O.S i * sharp (O.S i)) =
        ∑ i : Fin N,
          (X i * sharp (O.S i) + O.S i * sharp (X i)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [D.leibniz', D.sharp']
  refine { X := X, tangent_isometry := ?_, tangent_complete := ?_ }
  · intro i j
    have hrel := congrArg D (O.isometry i j)
    rw [hisometry] at hrel
    by_cases hij : i = j
    · subst j
      simpa [hD1] using hrel
    · simpa [hij, D.map_zero] using hrel
  · have hrel := congrArg D O.range_sum
    rw [hsum] at hrel
    simpa [hD1] using hrel

end InfoGeometry.Algebra.Cuntz
