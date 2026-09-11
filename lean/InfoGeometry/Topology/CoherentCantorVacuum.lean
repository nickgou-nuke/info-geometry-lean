import InfoGeometry.Canonical.RefinementGaloisConnection
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology

open InfoGeometry.Canonical.RefinementGaloisConnection
open InfoGeometry.Canonical.CantorCylinderLattice

structure CoherentCantorVacuum where
  seq : (n : ℕ) → Sector n
  coherent : ∀ n, coarseSector (seq (n + 1)) = seq n

namespace CoherentCantorVacuum

theorem ext {v w : CoherentCantorVacuum} (h : v.seq = w.seq) : v = w := by
  cases v with
  | mk v hv =>
      cases w with
      | mk w hw =>
          cases h
          rfl

def exactRefinementSequence (x : Sector 0) : (n : ℕ) → Sector n
  | 0 => x
  | n + 1 => refineSector (exactRefinementSequence x n)

def exactRefinementVacuum (x : Sector 0) : CoherentCantorVacuum where
  seq := exactRefinementSequence x
  coherent n := by
    change coarseSector (refineSector (exactRefinementSequence x n)) =
      exactRefinementSequence x n
    exact coarseSector_refineSector _

@[simp] theorem exactRefinementVacuum_zero (x : Sector 0) :
    (exactRefinementVacuum x).seq 0 = x := rfl

theorem exactRefinementVacuum_seq_succ (x : Sector 0) (n : ℕ) :
    (exactRefinementVacuum x).seq (n + 1) =
      refineSector ((exactRefinementVacuum x).seq n) := rfl

theorem coherent_iff_refine_le (v : CoherentCantorVacuum) (n : ℕ) :
    refineSector (v.seq n) ≤ v.seq (n + 1) := by
  rw [sector_galois_connection n]
  rw [v.coherent n]

theorem coherent_implies_refine_le (v : CoherentCantorVacuum) (n : ℕ) :
    refineSector (v.seq n) ≤ v.seq (n + 1) :=
  coherent_iff_refine_le v n

theorem exactRefinementSequence_le_of_coherent
    (v : CoherentCantorVacuum) (x : Sector 0)
    (hx : v.seq 0 = x) (n : ℕ) :
    exactRefinementSequence x n ≤ v.seq n := by
  induction n with
  | zero =>
      simpa [exactRefinementSequence, hx] using (le_rfl : x ≤ x)
  | succ n ih =>
      rw [exactRefinementSequence]
      rw [sector_galois_connection n]
      rw [v.coherent n]
      exact ih

theorem exactRefinementVacuum_le_of_zero_eq
    (v : CoherentCantorVacuum) (x : Sector 0)
    (hx : v.seq 0 = x) (n : ℕ) :
    (exactRefinementVacuum x).seq n ≤ v.seq n := by
  exact exactRefinementSequence_le_of_coherent v x hx n

theorem coherent_eq_exactRefinementVacuum
    (v : CoherentCantorVacuum)
    (h : ∀ n, refineSector (v.seq n) = v.seq (n + 1)) :
    v = exactRefinementVacuum (v.seq 0) := by
  apply ext
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
      have ih' : v.seq n = exactRefinementSequence (v.seq 0) n := by
        simpa [exactRefinementVacuum] using ih
      calc
        v.seq (n + 1) = refineSector (v.seq n) := (h n).symm
        _ = refineSector (exactRefinementSequence (v.seq 0) n) := by rw [ih']

theorem coherent_eq_exactRefinementVacuum_iff
    (v : CoherentCantorVacuum) :
    v = exactRefinementVacuum (v.seq 0) ↔
      ∀ n, refineSector (v.seq n) = v.seq (n + 1) := by
  constructor
  · intro hv n
    rw [hv]
    exact (exactRefinementVacuum_seq_succ (v.seq 0) n).symm
  · exact coherent_eq_exactRefinementVacuum v

def ExactRefinementVacuum : Type _ :=
  {v : CoherentCantorVacuum //
    ∀ n, refineSector (v.seq n) = v.seq (n + 1)}

noncomputable def exactRefinementVacuumEquiv :
    Sector 0 ≃ ExactRefinementVacuum where
  toFun x :=
    ⟨exactRefinementVacuum x, fun n =>
      (exactRefinementVacuum_seq_succ x n).symm⟩
  invFun v := v.1.seq 0
  left_inv x := rfl
  right_inv v := by
    apply Subtype.ext
    exact (coherent_eq_exactRefinementVacuum v.1 v.2).symm

@[simp] theorem exactRefinementVacuumEquiv_apply (x : Sector 0) :
    (exactRefinementVacuumEquiv x).1 = exactRefinementVacuum x := rfl

@[simp] theorem exactRefinementVacuumEquiv_symm_apply (v : ExactRefinementVacuum) :
    exactRefinementVacuumEquiv.symm v = v.1.seq 0 := rfl

instance exactRefinementVacuumLE : LE ExactRefinementVacuum where
  le v w := v.1.seq 0 ≤ w.1.seq 0

instance exactRefinementVacuumPartialOrder : PartialOrder ExactRefinementVacuum where
  le := (· ≤ ·)
  le_refl := by
    intro v
    change v.1.seq 0 ≤ v.1.seq 0
    exact le_rfl
  le_trans := by
    intro a b c hab hbc
    exact le_trans
      (show a.1.seq 0 ≤ b.1.seq 0 from hab)
      (show b.1.seq 0 ≤ c.1.seq 0 from hbc)
  le_antisymm := by
    intro a b hab hba
    apply Subtype.ext
    have hzero : a.1.seq 0 = b.1.seq 0 := le_antisymm
      (show a.1.seq 0 ≤ b.1.seq 0 from hab)
      (show b.1.seq 0 ≤ a.1.seq 0 from hba)
    calc
      a.1 = exactRefinementVacuum (a.1.seq 0) :=
        coherent_eq_exactRefinementVacuum a.1 a.2
      _ = exactRefinementVacuum (b.1.seq 0) := by rw [hzero]
      _ = b.1 := (coherent_eq_exactRefinementVacuum b.1 b.2).symm

noncomputable def exactRefinementVacuumOrderIso :
    Sector 0 ≃o ExactRefinementVacuum where
  toEquiv := exactRefinementVacuumEquiv
  map_rel_iff' := by
    intro x y
    change x ≤ y ↔ x ≤ y
    rfl

theorem coherent_not_exactRefinementVacuum_of_strict
    (v : CoherentCantorVacuum) (n : ℕ)
    (hstrict : refineSector (v.seq n) < v.seq (n + 1)) :
    v ≠ exactRefinementVacuum (v.seq 0) := by
  intro h
  have hdet : refineSector (v.seq n) = v.seq (n + 1) := by
    rw [h]
    exact (exactRefinementVacuum_seq_succ (v.seq 0) n).symm
  exact (ne_of_lt hstrict) hdet

def allTrueWord (n : ℕ) : Fin n → Bool := fun _ => true

def nonAllTrueSpatial (n : ℕ) : Set (Fin n → Bool) :=
  {w | w ≠ allTrueWord n}

def nonAllTrueSector (n : ℕ) : Sector n :=
  (nonAllTrueSpatial n, ⊥)

theorem truncateWord_allTrue (n : ℕ) :
    truncateWord (allTrueWord (n + 1)) = allTrueWord n := by
  funext i
  rfl

theorem coarseSpatial_nonAllTrue (n : ℕ) :
    coarseSpatial (nonAllTrueSpatial (n + 1)) = nonAllTrueSpatial n := by
  ext w
  change
    (∀ v, truncateWord v = w → v ≠ allTrueWord (n + 1)) ↔
      w ≠ allTrueWord n
  constructor
  · intro hw hwall
    have hbad := hw (allTrueWord (n + 1)) (by
      rw [truncateWord_allTrue, hwall])
    exact hbad rfl
  · intro hw v hv
    intro hvall
    apply hw
    calc
      w = truncateWord v := hv.symm
      _ = truncateWord (allTrueWord (n + 1)) := by rw [hvall]
      _ = allTrueWord n := truncateWord_allTrue n

def nonAllTrueVacuum : CoherentCantorVacuum where
  seq := nonAllTrueSector
  coherent n := by
    change
      (coarseSpatial (nonAllTrueSpatial (n + 1)), (⊥ : KreinSector)) =
        (nonAllTrueSpatial n, (⊥ : KreinSector))
    rw [coarseSpatial_nonAllTrue]

theorem nonAllTrueSpatial_zero :
    nonAllTrueSpatial 0 = (∅ : Set (Fin 0 → Bool)) := by
  ext w
  constructor
  · intro hw
    exact False.elim (hw (Subsingleton.elim w (allTrueWord 0)))
  · simp

theorem nonAllTrueSpatial_nonempty {n : ℕ} (hn : 0 < n) :
    (nonAllTrueSpatial n).Nonempty := by
  let w : Fin n → Bool := fun _ => false
  refine ⟨w, ?_⟩
  intro htrue
  have hzero := congrFun htrue ⟨0, hn⟩
  simp [w, allTrueWord] at hzero

theorem nonAllTrueSpatial_one_ne_refineSpatial_empty :
    nonAllTrueSpatial 1 ≠
      refineSpatial (∅ : Set (Fin 0 → Bool)) := by
  intro h
  let w : Fin 1 → Bool := fun _ => false
  have hw : w ∈ nonAllTrueSpatial 1 := by
    intro htrue
    have hzero := congrFun htrue ⟨0, by decide⟩
    simp [w, allTrueWord] at hzero
  rw [h] at hw
  simpa [refineSpatial] using hw

theorem nonAllTrueVacuum_not_exactRefinement :
    nonAllTrueVacuum ≠ exactRefinementVacuum (nonAllTrueVacuum.seq 0) := by
  intro h
  have hsp := congrArg
    (fun v : CoherentCantorVacuum => (v.seq 1).1) h
  have hsp' : nonAllTrueSpatial 1 =
      refineSpatial (nonAllTrueSpatial 0) := by
    simpa [nonAllTrueVacuum, exactRefinementVacuum,
      exactRefinementSequence, nonAllTrueSector] using hsp
  rw [nonAllTrueSpatial_zero] at hsp'
  exact nonAllTrueSpatial_one_ne_refineSpatial_empty hsp'

theorem nonAllTrueVacuum_strict_refinement_zero :
    refineSector (nonAllTrueVacuum.seq 0) < nonAllTrueVacuum.seq 1 := by
  apply lt_of_le_of_ne (coherent_implies_refine_le nonAllTrueVacuum 0)
  intro h
  have hsp := congrArg
    (fun s : Sector 1 => s.1) h
  have hsp' : refineSpatial (nonAllTrueSpatial 0) =
      nonAllTrueSpatial 1 := by
    simpa [nonAllTrueVacuum, nonAllTrueSector] using hsp
  apply nonAllTrueSpatial_one_ne_refineSpatial_empty
  rw [← hsp', nonAllTrueSpatial_zero]

theorem nonAllTrueVacuum_strict_refinement (n : ℕ) :
    refineSector (nonAllTrueVacuum.seq n) <
      nonAllTrueVacuum.seq (n + 1) := by
  apply lt_of_le_of_ne (coherent_implies_refine_le nonAllTrueVacuum n)
  intro h
  have hsp := congrArg
    (fun s : Sector (n + 1) => s.1) h
  have hsp' : refineSpatial (nonAllTrueSpatial n) =
      nonAllTrueSpatial (n + 1) := by
    simpa [nonAllTrueVacuum, nonAllTrueSector] using hsp
  have hw : leftChild (allTrueWord n) ∈ nonAllTrueSpatial (n + 1) := by
    intro htrue
    have hlast := congrFun htrue (Fin.last n)
    simp [allTrueWord, leftChild, extendWord] at hlast
  rw [← hsp'] at hw
  change truncateWord (leftChild (allTrueWord n)) ∈
    nonAllTrueSpatial n at hw
  rw [truncateWord_leftChild] at hw
  exact hw rfl

end CoherentCantorVacuum
end InfoGeometry.Topology
