import InfoGeometry.Canonical.AlbertAlgebraGenerationsBridge

namespace InfoGeometry.Canonical

variable {R V : Type*} [Field R] [CharZero R] [AddCommGroup V] [Module R V]

@[simp] lemma peirce3_diag1 : (peirceIdempotent3 : AlbertMatrix R V).diag1 = 0 := rfl
@[simp] lemma peirce3_diag2 : (peirceIdempotent3 : AlbertMatrix R V).diag2 = 0 := rfl
@[simp] lemma peirce3_diag3 : (peirceIdempotent3 : AlbertMatrix R V).diag3 = 1 := rfl
@[simp] lemma peirce3_gen1 : (peirceIdempotent3 : AlbertMatrix R V).gen1 = 0 := rfl
@[simp] lemma peirce3_gen2 : (peirceIdempotent3 : AlbertMatrix R V).gen2 = 0 := rfl
@[simp] lemma peirce3_gen3 : (peirceIdempotent3 : AlbertMatrix R V).gen3 = 0 := rfl

theorem peirce2_idempotent :
    jordanMul (peirceIdempotent2 (R:=R) (V:=V)) (peirceIdempotent2 (R:=R) (V:=V)) =
      peirceIdempotent2 (R:=R) (V:=V) := by
  ext <;> (try dsimp [jordanMul, peirceIdempotent2]; try simp; try ring)

theorem peirce3_idempotent :
    jordanMul (peirceIdempotent3 (R:=R) (V:=V)) (peirceIdempotent3 (R:=R) (V:=V)) =
      peirceIdempotent3 (R:=R) (V:=V) := by
  ext <;> (try dsimp [jordanMul, peirceIdempotent3]; try simp; try ring)

theorem peirce_orthogonality_13 :
    jordanMul (peirceIdempotent1 (R:=R) (V:=V)) (peirceIdempotent3 (R:=R) (V:=V)) = 0 := by
  ext <;> (try dsimp [jordanMul, peirceIdempotent1, peirceIdempotent3, Zero.zero]; try simp; try ring)

theorem peirce_orthogonality_23 :
    jordanMul (peirceIdempotent2 (R:=R) (V:=V)) (peirceIdempotent3 (R:=R) (V:=V)) = 0 := by
  ext <;> (try dsimp [jordanMul, peirceIdempotent2, peirceIdempotent3, Zero.zero]; try simp; try ring)

def albertId : AlbertMatrix R V :=
  ⟨1, 1, 1, 0, 0, 0⟩

theorem albertId_eq_sum_peirce :
    albertId (R:=R) (V:=V) = albertAdd (peirceIdempotent1 (R:=R) (V:=V))
      (albertAdd (peirceIdempotent2 (R:=R) (V:=V)) (peirceIdempotent3 (R:=R) (V:=V))) := by
  ext <;> (try dsimp [albertId, albertAdd, peirceIdempotent1, peirceIdempotent2, peirceIdempotent3]; try simp; try ring)

end InfoGeometry.Canonical
