/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornPolarKetBra
import InfoGeometry.Canonical.ReflexiveNilpotentFlows
import InfoGeometry.Canonical.DeBruijnRotorAlternationCycle

/-! A normalized null pair supplies a reflexive square-zero pair on the full
Zorn module. Its support is proper, so the ambient Weyl unit needs the
complement. No Moore–Penrose or positive-adjoint identification is asserted. -/
noncomputable section
namespace InfoGeometry.Canonical.ZornNullPeirceWeyl
open _root_.InfoGeometry.Canonical.ZornVectorMatrixExplicit
open ZornPolarizationMetricBridge ZornPolarKetBra ReflexiveNilpotentFlows

theorem nullPair_reflexive (X Y : ZornCoord) (h : polarPair X Y = 1) :
    ketBra X X * ketBra Y Y * ketBra X X = ketBra X X := by
  rw [ketBra_mul, h, one_smul, ketBra_mul, polarPair_symm Y X, h, one_smul]

theorem nullPair_support (X Y : ZornCoord) (h : polarPair X Y = 1) :
    support (ketBra X X) (ketBra Y Y) = ketBra X Y + ketBra Y X := by
  unfold support
  rw [ketBra_mul, ketBra_mul, h, polarPair_symm Y X, h, one_smul, one_smul]

theorem nullPair_support_trace (X Y : ZornCoord) (h : polarPair X Y = 1) :
    LinearMap.trace ℝ ZornCoord (support (ketBra X X) (ketBra Y Y)) = 2 := by
  rw [nullPair_support X Y h, map_add, ketBra_trace, ketBra_trace,
    polarPair_symm Y X, h]
  norm_num

theorem nullPair_support_ne_one (X Y : ZornCoord) (h : polarPair X Y = 1) :
    support (ketBra X X) (ketBra Y Y) ≠ 1 := by
  intro he
  have ht := nullPair_support_trace X Y h
  rw [he, LinearMap.trace_one, native_dimensions.1] at ht
  norm_num at ht

def nullPairWeylUnit (X Y : ZornCoord) (hX : polarPair X X = 0)
    (hY : polarPair Y Y = 0) (h : polarPair X Y = 1) : (Module.End ℝ ZornCoord)ˣ :=
  weylUnit (ketBra_sq_zero X X hX) (ketBra_sq_zero Y Y hY)
    (nullPair_reflexive X Y h)

theorem nullPair_weyl_fourth (X Y : ZornCoord) (hX : polarPair X X = 0)
    (hY : polarPair Y Y = 0) (h : polarPair X Y = 1) :
    weyl (ketBra X X) (ketBra Y Y) ^ 4 = 1 := by
  exact weyl_fourth (ketBra_sq_zero X X hX) (ketBra_sq_zero Y Y hY)
    (nullPair_reflexive X Y h)
    (nullPair_reflexive Y X (by rwa [polarPair_symm]))

/-- A concrete normalization compatible with the existing null-vector witness. -/
theorem diagonal_null_pair_normalized :
    polarPair (zornMk 1 0 0 0) (zornMk 0 2 0 0) = 1 := by
  norm_num [polarPair, zornMk, zornA, zornB, zornX, zornY, dot3]

/-- Every normalized split-octonion Zorn null pair `(X, Y)` forms a reflexive
    dual seed pair `IsDualSeedPair (ketBra X X) (ketBra Y Y)` in `Module.End ℝ ZornCoord`. -/
theorem nullPair_isDualSeedPair (X Y : ZornCoord) (hX : polarPair X X = 0)
    (hY : polarPair Y Y = 0) (h : polarPair X Y = 1) :
    DeBruijnRotorAlternationCycle.IsDualSeedPair (ketBra X X) (ketBra Y Y) where
  d_sq := ketBra_sq_zero X X hX
  B_sq := ketBra_sq_zero Y Y hY
  dBd := nullPair_reflexive X Y h
  BdB := nullPair_reflexive Y X (by rwa [polarPair_symm])

/-- Along `c * c + s * s = 1`, the Zorn null-pair moving pole is idempotent,
    its chordal displacement square equals `(s * s) • support (ketBra X X) (ketBra Y Y)`
    with trace `(s * s) * 2`, and its sandwich compression is `(c * c) • (ketBra X X * ketBra Y Y)`. -/
theorem nullPair_movingPolePlus_chordal_and_trace (X Y : ZornCoord)
    (hX : polarPair X X = 0) (hY : polarPair Y Y = 0) (h : polarPair X Y = 1)
    {c s : ℝ} (hcs : c * c + s * s = 1) :
    let d := ketBra X X
    let B := ketBra Y Y
    IsIdempotentElem (DeBruijnRotorAlternationCycle.movingPolePlus c s d B) ∧
    (DeBruijnRotorAlternationCycle.movingPolePlus c s d B -
       DeBruijnRotorAlternationCycle.polePlus d B) *
     (DeBruijnRotorAlternationCycle.movingPolePlus c s d B -
       DeBruijnRotorAlternationCycle.polePlus d B) = (s * s) • support d B ∧
    LinearMap.trace ℝ ZornCoord
      ((DeBruijnRotorAlternationCycle.movingPolePlus c s d B -
          DeBruijnRotorAlternationCycle.polePlus d B) *
       (DeBruijnRotorAlternationCycle.movingPolePlus c s d B -
          DeBruijnRotorAlternationCycle.polePlus d B)) = (s * s) * 2 := by
  intro d B
  have hseed := nullPair_isDualSeedPair X Y hX hY h
  have hcomp := DeBruijnRotorAlternationCycle.movingPolePlus_chordal_square_and_compression hseed hcs
  have h_supp : DeBruijnRotorAlternationCycle.carrierSupport d B = support d B := rfl
  refine ⟨DeBruijnRotorAlternationCycle.movingPolePlus_idem hseed c s hcs, hcomp.1, ?_⟩
  rw [hcomp.1, h_supp, map_smul, nullPair_support_trace X Y h, smul_eq_mul]

end InfoGeometry.Canonical.ZornNullPeirceWeyl
