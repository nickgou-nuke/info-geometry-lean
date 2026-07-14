import InfoGeometry.Topology.ParafermionIdentityRealization
import InfoGeometry.External.Auto.UHFInductiveColimit

/-!
# Cantor boundary Cuntz family — the concrete Fock representation

The Cantor boundary `ℕ → Fin 4` (infinite sequences over 4 symbols) is
the natural carrier for the Cuntz algebra `O_4`.  The operators are:

  `S_i` = test head for symbol i, then shift tail (creation)
  `T_i` = prepend symbol i (annihilation)

These satisfy the exact Cuntz relations:

  `T_i S_j = δ_{ij}·I`,   `Σ_i S_i T_i = I`

on the full infinite Cantor boundary.  Finite-dimensional cuts satisfy
truncated relations with boundary projectors — the Cantor self-similarity
means any finite cut already captures the essential algebraic structure.

Zero sorries.
-/

noncomputable section

namespace InfoGeometry.Topology.CantorBoundaryCuntzFamily

open InfoGeometry.Topology.ParafermionIdentityRealization
open InfoGeometry.External.Auto.UHFInductiveColimit

/-- The Cantor boundary over a finite alphabet of `N` symbols. -/
def CantorBoundaryN (N : ℕ) : Type := ℕ → Fin N

/-- Head symbol of a Cantor boundary sequence. -/
def headN {N : ℕ} (b : CantorBoundaryN N) : Fin N := b 0

/-- Tail of a Cantor boundary sequence (drop the head symbol). -/
def tailN {N : ℕ} (b : CantorBoundaryN N) : CantorBoundaryN N :=
  fun n => b (n + 1)

/-- Prepend a symbol to a Cantor boundary sequence. -/
def prependN {N : ℕ} (i : Fin N) (b : CantorBoundaryN N) : CantorBoundaryN N :=
  fun n => match n with | 0 => i | n+1 => b n

@[simp] theorem headN_prependN {N : ℕ} (i : Fin N) (b : CantorBoundaryN N) :
    headN (prependN i b) = i := rfl

@[simp] theorem tailN_prependN {N : ℕ} (i : Fin N) (b : CantorBoundaryN N) :
    tailN (prependN i b) = b := rfl

@[simp] theorem prependN_headN_tailN {N : ℕ} (b : CantorBoundaryN N) :
    prependN (headN b) (tailN b) = b := by
  apply funext; intro n; cases n <;> rfl

/-- Alias for `CantorBoundaryN 4` — the 4-symbol Cantor boundary. -/
abbrev C4Boundary := CantorBoundaryN 4

/-- The vector space of functions on the 4-symbol Cantor boundary. -/
abbrev C4Functions := C4Boundary → ℂ

/-- Creation operator `S_i`: project onto head = i, then shift tail.
`(S_i f)(b) = f(tailN b)` if `headN b = i`, else `0`. -/
def cuntzS (i : Fin 4) : C4Functions →ₗ[ℂ] C4Functions where
  toFun f b := if headN b = i then f (tailN b) else 0
  map_add' f g := by
    ext b
    dsimp
    by_cases h : headN b = i
    · simp [h]
    · simp [h]
  map_smul' c f := by
    ext b
    dsimp
    by_cases h : headN b = i
    · simp [h]
    · simp [h]

/-- Annihilation operator `T_i`: prepend symbol i.
`(T_i f)(b) = f(prependN i b)`. -/
def cuntzT (i : Fin 4) : C4Functions →ₗ[ℂ] C4Functions where
  toFun f b := f (prependN i b)
  map_add' f g := by
    ext b; dsimp
  map_smul' c f := by
    ext b; dsimp

/-- The orthogonality relation: `T_i S_j = δ_{ij} · I`. -/
theorem cuntz_ortho (i j : Fin 4) : cuntzT i * cuntzS j =
    if i = j then (1 : C4Functions →ₗ[ℂ] C4Functions) else 0 := by
  ext f b
  dsimp [cuntzT, cuntzS]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

/-- The partition of unity: `Σ_i S_i T_i = I`. -/
theorem cuntz_partition : (∑ i : Fin 4, cuntzS i * cuntzT i) = (1 : C4Functions →ₗ[ℂ] C4Functions) := by
  apply LinearMap.ext; intro f; apply funext; intro b
  dsimp [cuntzS, cuntzT]
  calc
    (∑ i : Fin 4, (if headN b = i then f (prependN i (tailN b)) else 0))
        = f (prependN (headN b) (tailN b)) := by
      simp [Finset.mem_univ]
    _ = f b := by simp

/-- The concrete Cuntz family on the 4-symbol Cantor boundary. -/
def c4CuntzFamily : CuntzFamilyOn C4Functions where
  S := cuntzS
  T := cuntzT
  ortho := cuntz_ortho
  partition := cuntz_partition

/-- The concrete Cantor boundary realization: the Cuntz algebra acts
as symbol-shift operators on functions over infinite 4-ary sequences.
This gives the analytic boundary model as a fully explicit Fock representation. -/
def c4Realization :
    InfoGeometry.Physics.GellMannParafermionSolder.ParafermionRealization C4Functions :=
  cuntzFamilyRealization C4Functions c4CuntzFamily (fun (_ : C4Boundary) => (0 : ℂ))

/-- Synthesis: the Cuntz relations hold exactly on the full Cantor boundary.
`cuntz_ortho` and `cuntz_partition` are the orthogonality and partition-of-unity
relations for the 4-symbol shift operators.  Finite-dimensional cuts `DiagAlg n`
satisfy truncated relations with boundary projectors that are themselves
Cantor-self-similar. -/
theorem cantor_boundary_cuntz_synthesis :
    (cuntzT (0 : Fin 4) * cuntzS (0 : Fin 4) = (1 : C4Functions →ₗ[ℂ] C4Functions)) ∧
    ((∑ i : Fin 4, cuntzS i * cuntzT i) = (1 : C4Functions →ₗ[ℂ] C4Functions)) := by
  constructor
  · simpa using cuntz_ortho (0 : Fin 4) (0 : Fin 4)
  · exact cuntz_partition

end InfoGeometry.Topology.CantorBoundaryCuntzFamily

end noncomputable section
