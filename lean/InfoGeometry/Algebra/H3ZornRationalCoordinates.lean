import InfoGeometry.Algebra.GenericH3ZornJordanSurface

/-!
# Exact rational coordinates for the split Albert carrier

The definitions here are coefficient-field generic.  In particular, the
specialization at `ℚ` is an executable exact shadow of the real coordinate
probe order used by the existing `f4Basis` evaluator.
-/

namespace InfoGeometry.Algebra

noncomputable section

open H3Zorn

variable {R : Type*} [Field R]

def h3ZornCoordinateR (X : H3Zorn R) : Fin 27 → R :=
  ![X.α₁, X.α₂, X.α₃,
    X.a.a, X.a.v 0, X.a.v 1, X.a.v 2, X.a.w 0, X.a.w 1, X.a.w 2, X.a.b,
    X.b.a, X.b.v 0, X.b.v 1, X.b.v 2, X.b.w 0, X.b.w 1, X.b.w 2, X.b.b,
    X.c.a, X.c.v 0, X.c.v 1, X.c.v 2, X.c.w 0, X.c.w 1, X.c.w 2, X.c.b]

def h3ZornDiagR (j : Fin 3) : H3Zorn R :=
  match j with
  | 0 => ⟨1, 0, 0, 0, 0, 0⟩
  | 1 => ⟨0, 1, 0, 0, 0, 0⟩
  | 2 => ⟨0, 0, 1, 0, 0, 0⟩

def zornBasisR (i : Fin 8) : ZornVectorMatrix R :=
  match i with
  | 0 => ⟨1, 0, 0, 0⟩
  | 1 => ⟨0, fun j => if j = 0 then 1 else 0, 0, 0⟩
  | 2 => ⟨0, fun j => if j = 1 then 1 else 0, 0, 0⟩
  | 3 => ⟨0, fun j => if j = 2 then 1 else 0, 0, 0⟩
  | 4 => ⟨0, 0, fun j => if j = 0 then 1 else 0, 0⟩
  | 5 => ⟨0, 0, fun j => if j = 1 then 1 else 0, 0⟩
  | 6 => ⟨0, 0, fun j => if j = 2 then 1 else 0, 0⟩
  | 7 => ⟨0, 0, 0, 1⟩

def h3ZornOffR (slot : Fin 3) (i : Fin 8) : H3Zorn R :=
  match slot with
  | 0 => ⟨0, 0, 0, zornBasisR i, 0, 0⟩
  | 1 => ⟨0, 0, 0, 0, zornBasisR i, 0⟩
  | 2 => ⟨0, 0, 0, 0, 0, zornBasisR i⟩

def h3ZornProbeR (j : Fin 27) : H3Zorn R :=
  ![h3ZornDiagR 0, h3ZornDiagR 1, h3ZornDiagR 2,
    h3ZornOffR 0 0, h3ZornOffR 0 1, h3ZornOffR 0 2, h3ZornOffR 0 3,
    h3ZornOffR 0 4, h3ZornOffR 0 5, h3ZornOffR 0 6, h3ZornOffR 0 7,
    h3ZornOffR 1 0, h3ZornOffR 1 1, h3ZornOffR 1 2, h3ZornOffR 1 3,
    h3ZornOffR 1 4, h3ZornOffR 1 5, h3ZornOffR 1 6, h3ZornOffR 1 7,
    h3ZornOffR 2 0, h3ZornOffR 2 1, h3ZornOffR 2 2, h3ZornOffR 2 3,
    h3ZornOffR 2 4, h3ZornOffR 2 5, h3ZornOffR 2 6, h3ZornOffR 2 7] j

@[simp] theorem h3ZornProbeR_coordinate_self (j : Fin 27) :
    h3ZornCoordinateR (R := R) (h3ZornProbeR (R := R) j) j = 1 := by
  fin_cases j <;>
    simp [h3ZornCoordinateR, h3ZornProbeR, h3ZornDiagR,
      h3ZornOffR, zornBasisR]

/-- One exact coordinate of an inner action, relative to the canonical probe
family.  The generator pair is explicit data, so this definition is suitable
for the later rational F₄ certificate without assuming any rank statement. -/
noncomputable def cubicJordanActionCoordinate
    (A B : H3Zorn R) (r c : Fin 27) : R :=
  h3ZornCoordinateR
    (cubicJordanInnerAction A B (h3ZornProbeR r)) c

/-- Row-major action matrix attached to an explicit finite family of generator
pairs. -/
noncomputable def cubicJordanActionMatrix
    (pairs : Fin 52 → H3Zorn R × H3Zorn R) :
    Matrix (Fin 52) (Fin 729) R :=
  fun i k => cubicJordanActionCoordinate (pairs i).1 (pairs i).2
    ⟨k.val / 27, by omega⟩ ⟨k.val % 27, by omega⟩

@[simp] theorem cubicJordanActionMatrix_apply
    (pairs : Fin 52 → H3Zorn R × H3Zorn R)
    (i : Fin 52) (r c : Fin 27) :
    cubicJordanActionMatrix pairs i ⟨27 * r.val + c.val, by omega⟩ =
      cubicJordanActionCoordinate (pairs i).1 (pairs i).2 r c := by
  dsimp [cubicJordanActionMatrix, cubicJordanActionCoordinate]
  have hr : (⟨(27 * r.val + c.val) / 27, by omega⟩ : Fin 27) = r := by
    ext
    dsimp
    omega
  have hc : (⟨(27 * r.val + c.val) % 27, by omega⟩ : Fin 27) = c := by
    ext
    dsimp
    omega
  rw [hr, hc]

/-- The 52 generator pairs in the canonical order used by `f4Basis`, now on
the coefficient-field-independent shadow carrier. -/
def f4GeneratorPairsR : Fin 52 → H3Zorn R × H3Zorn R :=
  ![
    (h3ZornDiagR 0, h3ZornOffR 0 0), (h3ZornDiagR 0, h3ZornOffR 0 1),
    (h3ZornDiagR 0, h3ZornOffR 0 2), (h3ZornDiagR 0, h3ZornOffR 0 3),
    (h3ZornDiagR 0, h3ZornOffR 0 4), (h3ZornDiagR 0, h3ZornOffR 0 5),
    (h3ZornDiagR 0, h3ZornOffR 0 6), (h3ZornDiagR 0, h3ZornOffR 0 7),
    (h3ZornDiagR 0, h3ZornOffR 2 0), (h3ZornDiagR 0, h3ZornOffR 2 1),
    (h3ZornDiagR 0, h3ZornOffR 2 2), (h3ZornDiagR 0, h3ZornOffR 2 3),
    (h3ZornDiagR 0, h3ZornOffR 2 4), (h3ZornDiagR 0, h3ZornOffR 2 5),
    (h3ZornDiagR 0, h3ZornOffR 2 6), (h3ZornDiagR 0, h3ZornOffR 2 7),
    (h3ZornDiagR 1, h3ZornOffR 1 0), (h3ZornDiagR 1, h3ZornOffR 1 1),
    (h3ZornDiagR 1, h3ZornOffR 1 2), (h3ZornDiagR 1, h3ZornOffR 1 3),
    (h3ZornDiagR 1, h3ZornOffR 1 4), (h3ZornDiagR 1, h3ZornOffR 1 5),
    (h3ZornDiagR 1, h3ZornOffR 1 6), (h3ZornDiagR 1, h3ZornOffR 1 7),
    (h3ZornOffR 0 0, h3ZornOffR 0 1), (h3ZornOffR 0 0, h3ZornOffR 0 2),
    (h3ZornOffR 0 0, h3ZornOffR 0 3), (h3ZornOffR 0 0, h3ZornOffR 0 4),
    (h3ZornOffR 0 0, h3ZornOffR 0 5), (h3ZornOffR 0 0, h3ZornOffR 0 6),
    (h3ZornOffR 0 0, h3ZornOffR 0 7), (h3ZornOffR 0 1, h3ZornOffR 0 2),
    (h3ZornOffR 0 1, h3ZornOffR 0 3), (h3ZornOffR 0 1, h3ZornOffR 0 4),
    (h3ZornOffR 0 1, h3ZornOffR 0 5), (h3ZornOffR 0 1, h3ZornOffR 0 6),
    (h3ZornOffR 0 1, h3ZornOffR 0 7), (h3ZornOffR 0 2, h3ZornOffR 0 3),
    (h3ZornOffR 0 2, h3ZornOffR 0 4), (h3ZornOffR 0 2, h3ZornOffR 0 5),
    (h3ZornOffR 0 2, h3ZornOffR 0 6), (h3ZornOffR 0 2, h3ZornOffR 0 7),
    (h3ZornOffR 0 3, h3ZornOffR 0 4), (h3ZornOffR 0 3, h3ZornOffR 0 5),
    (h3ZornOffR 0 3, h3ZornOffR 0 6), (h3ZornOffR 0 3, h3ZornOffR 0 7),
    (h3ZornOffR 0 4, h3ZornOffR 0 5), (h3ZornOffR 0 4, h3ZornOffR 0 6),
    (h3ZornOffR 0 4, h3ZornOffR 0 7), (h3ZornOffR 0 5, h3ZornOffR 0 6),
    (h3ZornOffR 0 5, h3ZornOffR 0 7), (h3ZornOffR 0 6, h3ZornOffR 0 7)]

noncomputable def f4GeneratorActionMatrixR :
    Matrix (Fin 52) (Fin 729) R :=
  cubicJordanActionMatrix f4GeneratorPairsR

/-- Exact rational specialization used as the input to the certificate
exporter. -/
noncomputable def f4GeneratorActionMatrixQ :
    Matrix (Fin 52) (Fin 729) ℚ :=
  f4GeneratorActionMatrixR (R := ℚ)

@[simp] theorem f4GeneratorActionMatrixQ_apply
    (i : Fin 52) (r c : Fin 27) :
    f4GeneratorActionMatrixQ i ⟨27 * r.val + c.val, by omega⟩ =
      cubicJordanActionCoordinate (f4GeneratorPairsR (R := ℚ) i).1
        (f4GeneratorPairsR (R := ℚ) i).2 r c := by
  exact cubicJordanActionMatrix_apply (pairs := f4GeneratorPairsR (R := ℚ)) i r c

end
end InfoGeometry.Algebra
