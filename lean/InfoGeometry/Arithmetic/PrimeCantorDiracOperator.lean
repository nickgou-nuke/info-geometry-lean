import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Arithmetic.PrimeBooleanCube
import InfoGeometry.Arithmetic.PrimeMajoranaCARGate
import InfoGeometry.Arithmetic.PrimeMajoranaDiracFinite

/-!
# InfoGeometry.Arithmetic.PrimeCantorDiracOperator

Finite Cantor-lattice Dirac operator for prime-register arithmetic.

Vertices are finite square-free prime occupancy states `S ⊆ P.primes`.

The prime-axis move is the already-owned Majorana bit flip. The Cantor Dirac
operator is the finite weighted difference operator

  `D_κ f(S) = ∑_{p ∈ P} κ p * (f(S △ {p}) - f(S))`.

This is the graph/difference Dirac on the finite Boolean/Cantor cube.

Important boundary:

* This file does not identify `D_κ^2` with the arithmetic Hamiltonian.
* The arithmetic Hamiltonian remains the diagonal number operator
  `H(S) = ∑_{p ∈ S} λ p`.
* No infinite Euler product, analytic continuation, Hilbert--Pólya, Lee--Yang,
  or RH claim is made.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeCantorDiracOperator

open InfoGeometry.Arithmetic.PrimeBitWittenIndex (PrimeRegister)

/-! ## 1. Finite Cantor vertices and fields -/

/-- A finite prime Cantor vertex is the canonical Boolean-cube vertex. -/
@[rep_depth thermo]
abbrev CantorVertex (P : PrimeRegister) :=
  InfoGeometry.Arithmetic.PrimeBooleanCube.Vertex P

/-- Real fields on the finite prime Cantor cube. -/
@[rep_depth thermo]
abbrev CantorField (P : PrimeRegister) :=
  CantorVertex P → ℝ

/-- Prime-axis flip on the finite Cantor cube. -/
@[rep_depth thermo]
def axisFlip
    (P : PrimeRegister)
    (p : ℕ)
    (hp : p ∈ P.primes)
    (v : CantorVertex P) :
    CantorVertex P :=
  InfoGeometry.Arithmetic.PrimeBooleanCube.flipVertex p hp v

/-- Prime-axis flip is involutive. -/
@[simp, bridge_target_tag, rep_depth thermo]
theorem axisFlip_involutive
    (P : PrimeRegister)
    (p : ℕ)
    (hp : p ∈ P.primes)
    (v : CantorVertex P) :
    axisFlip P p hp (axisFlip P p hp v) = v := by
  simpa [axisFlip] using
    InfoGeometry.Arithmetic.PrimeBooleanCube.flipVertex_involutive p hp v

/-- The flipped mode is occupied iff it was previously unoccupied. -/
@[simp, bridge_target_tag, rep_depth thermo]
theorem mem_axisFlip_self
    (P : PrimeRegister)
    (p : ℕ)
    (hp : p ∈ P.primes)
    (v : CantorVertex P) :
    p ∈ (axisFlip P p hp v).val ↔ p ∉ v.val := by
  simpa [axisFlip] using
    InfoGeometry.Arithmetic.PrimeBooleanCube.mem_flipVertex_self p hp v

/-- Other modes are unaffected by the prime-axis flip. -/
@[simp, bridge_target_tag, rep_depth thermo]
theorem mem_axisFlip_of_ne
    (P : PrimeRegister)
    {p q : ℕ}
    (hp : p ∈ P.primes)
    (hqp : q ≠ p)
    (v : CantorVertex P) :
    q ∈ (axisFlip P p hp v).val ↔ q ∈ v.val := by
  simpa [axisFlip] using
    InfoGeometry.Arithmetic.PrimeBooleanCube.mem_flipVertex_of_ne hp hqp v


/-! ## 2. Axis difference and Cantor Dirac operator -/

/--
Prime-axis finite difference.

`∇_p f(S) = f(S △ {p}) - f(S)`.
-/
@[rep_depth thermo]
def axisDifference
    (P : PrimeRegister)
    (p : ℕ)
    (hp : p ∈ P.primes)
    (f : CantorField P)
    (v : CantorVertex P) : ℝ :=
  f (axisFlip P p hp v) - f v

/--
The axis difference flips sign after traversing the same edge.

This is the finite graph analogue of orientation reversal.
-/
@[bridge_target_tag, rep_depth thermo]
theorem axisDifference_after_axisFlip
    (P : PrimeRegister)
    (p : ℕ)
    (hp : p ∈ P.primes)
    (f : CantorField P)
    (v : CantorVertex P) :
    axisDifference P p hp f (axisFlip P p hp v)
      =
    - axisDifference P p hp f v := by
  unfold axisDifference axisFlip
  rw [InfoGeometry.Arithmetic.PrimeBooleanCube.flipVertex_involutive]
  ring

/--
The weighted finite Cantor-lattice Dirac/difference operator.

`D_κ f(S) = ∑_{p ∈ P} κ p * (f(S △ {p}) - f(S))`.
-/
@[rep_depth thermo]
def cantorDirac
    (P : PrimeRegister)
    (κ : ℕ → ℝ)
    (f : CantorField P)
    (v : CantorVertex P) : ℝ :=
  Finset.sum P.primes.attach (fun p =>
    κ p.1 * axisDifference P p.1 p.2 f v)

/--
The adjacency-only transport version.

This is useful for comparison, but `cantorDirac` is the difference operator.
-/
@[rep_depth thermo]
def cantorAdjacency
    (P : PrimeRegister)
    (κ : ℕ → ℝ)
    (f : CantorField P)
    (v : CantorVertex P) : ℝ :=
  Finset.sum P.primes.attach (fun p =>
    κ p.1 * f (axisFlip P p.1 p.2 v))

/-- The Cantor difference Dirac annihilates constant fields. -/
@[bridge_target_tag, rep_depth thermo]
theorem cantorDirac_const_zero
    (P : PrimeRegister)
    (κ : ℕ → ℝ)
    (c : ℝ)
    (v : CantorVertex P) :
    cantorDirac P κ (fun _ => c) v = 0 := by
  unfold cantorDirac axisDifference
  simp

/--
Pointwise expansion of the Cantor Dirac as adjacency minus diagonal degree
term.
-/
@[bridge_target_tag, rep_depth thermo]
theorem cantorDirac_eq_adjacency_sub_weight_sum
    (P : PrimeRegister)
    (κ : ℕ → ℝ)
    (f : CantorField P)
    (v : CantorVertex P) :
    cantorDirac P κ f v =
      cantorAdjacency P κ f v
        - (Finset.sum P.primes.attach (fun p => κ p.1)) * f v := by
  unfold cantorDirac cantorAdjacency axisDifference
  calc
    Finset.sum P.primes.attach
        (fun p => κ p.1 * (f (axisFlip P p.1 p.2 v) - f v))
        =
      Finset.sum P.primes.attach
        (fun p => κ p.1 * f (axisFlip P p.1 p.2 v) - κ p.1 * f v) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          ring
    _ =
      (Finset.sum P.primes.attach (fun p => κ p.1 * f (axisFlip P p.1 p.2 v)))
        -
      (Finset.sum P.primes.attach (fun p => κ p.1 * f v)) := by
          rw [Finset.sum_sub_distrib]
    _ =
      cantorAdjacency P κ f v
        - (Finset.sum P.primes.attach (fun p => κ p.1)) * f v := by
          rw [Finset.sum_mul]
          rfl


/-! ## 3. Diagonal arithmetic Hamiltonian readout -/

/--
Prime-weighted diagonal number-operator Hamiltonian on the Cantor lattice.

`H_λ(S) = ∑_{p ∈ S} λ p`.
-/
@[rep_depth thermo]
def arithmeticHamiltonian
    (P : PrimeRegister)
    (lam : ℕ → ℝ)
    (v : CantorVertex P) : ℝ :=
  Finset.sum v.val (fun p => lam p)

/--
Same Hamiltonian written as a register-wide occupancy sum.
-/
@[rep_depth thermo]
def occupancyHamiltonian
    (P : PrimeRegister)
    (lam : ℕ → ℝ)
    (v : CantorVertex P) : ℝ :=
  Finset.sum P.primes (fun p => if p ∈ v.val then lam p else 0)

/--
The register-wide occupancy Hamiltonian equals the occupied-mode sum.
-/
@[bridge_target_tag, rep_depth thermo]
theorem occupancyHamiltonian_eq_arithmeticHamiltonian
    (P : PrimeRegister)
    (lam : ℕ → ℝ)
    (v : CantorVertex P) :
    occupancyHamiltonian P lam v =
      arithmeticHamiltonian P lam v := by
  unfold occupancyHamiltonian arithmeticHamiltonian
  have hfilter :
      P.primes.filter (fun p => p ∈ v.val) = v.val := by
    ext p
    constructor
    · intro hp
      exact (Finset.mem_filter.mp hp).2
    · intro hp
      exact Finset.mem_filter.mpr ⟨v.property hp, hp⟩
  rw [← Finset.sum_filter]
  simpa [hfilter]

/--
For logarithmic prime weights, the Hamiltonian is the finite occupied log-sum.

This is the finite diagonal arithmetic Hamiltonian. It is not asserted to be
the square of the difference Dirac.
-/
@[rep_depth thermo]
def logArithmeticHamiltonian
    (P : PrimeRegister)
    (v : CantorVertex P) : ℝ :=
  arithmeticHamiltonian P (fun p => Real.log p) v


/-! ## 4. Bundled finite Cantor Dirac package -/

/--
Finite prime Cantor Dirac package.

`κ` controls the graph/difference Dirac.
`λ` controls the diagonal arithmetic Hamiltonian.
They are deliberately separate fields.
-/
@[rep_depth thermo]
structure FinitePrimeCantorDirac where
  P : PrimeRegister
  κ : ℕ → ℝ
  lam : ℕ → ℝ

namespace FinitePrimeCantorDirac

/-- Vertices of the finite Cantor lattice. -/
@[rep_depth thermo]
abbrev Vertex (D : FinitePrimeCantorDirac) :=
  CantorVertex D.P

/-- Real fields on the finite Cantor lattice. -/
@[rep_depth thermo]
abbrev Field (D : FinitePrimeCantorDirac) :=
  CantorField D.P

/-- The graph/difference Cantor Dirac operator. -/
@[rep_depth thermo]
def dirac
    (D : FinitePrimeCantorDirac)
    (f : D.Field)
    (v : D.Vertex) : ℝ :=
  cantorDirac D.P D.κ f v

/-- The diagonal arithmetic Hamiltonian. -/
@[rep_depth thermo]
def hamiltonian
    (D : FinitePrimeCantorDirac)
    (v : D.Vertex) : ℝ :=
  arithmeticHamiltonian D.P D.lam v

/-- The Dirac kills constant fields. -/
@[bridge_target_tag, rep_depth thermo]
theorem dirac_const_zero
    (D : FinitePrimeCantorDirac)
    (c : ℝ)
    (v : D.Vertex) :
    D.dirac (fun _ => c) v = 0 := by
  exact cantorDirac_const_zero D.P D.κ c v

/-- The Hamiltonian can be read as a register-wide occupancy sum. -/
@[bridge_target_tag, rep_depth thermo]
theorem occupancy_hamiltonian_eq_hamiltonian
    (D : FinitePrimeCantorDirac)
    (v : D.Vertex) :
    occupancyHamiltonian D.P D.lam v = D.hamiltonian v := by
  unfold hamiltonian
  exact occupancyHamiltonian_eq_arithmeticHamiltonian D.P D.lam v

end FinitePrimeCantorDirac


end InfoGeometry.Arithmetic.PrimeCantorDiracOperator
