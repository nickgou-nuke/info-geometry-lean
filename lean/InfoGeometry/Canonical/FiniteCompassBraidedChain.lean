import InfoGeometry.Canonical.FiniteMajoranaBraiding

/-!
# InfoGeometry.Canonical.FiniteCompassBraidedChain

Finite braided chains of Cayley--Klein/Krein compass operators.

A local compass packet records three algebraic geometry signatures:

* elliptic/involutive complex direction: `elliptic² = -1`;
* hyperbolic/reflection direction: `hyperbolic² = 1`;
* parabolic/nilpotent direction: `parabolic² = 0`.

A braid word acts on a chain by the finite permutation readout already proved in
`FiniteMajoranaBraiding`.  This file proves that permutation/braid transport
preserves the three local compass laws.

No infinite fractal limit.
No analytic completion.
No CPT theorem.
No physical final-state claim.
-/

namespace FiniteCompassBraidedChain

open InfoGeometry.Canonical.FiniteMajoranaBraiding

/--
A local Cayley--Klein/Krein compass packet with elliptic, hyperbolic, and
parabolic operator directions.
-/
structure CompassTriple (Op : Type*) [Mul Op] [One Op] [Zero Op] [Neg Op] where
  /-- Elliptic direction, modeled algebraically by square `-1`. -/
  elliptic : Op
  /-- Hyperbolic direction, modeled algebraically by square `1`. -/
  hyperbolic : Op
  /-- Parabolic direction, modeled algebraically by square `0`. -/
  parabolic : Op
  /-- Elliptic square law. -/
  elliptic_sq_neg_one : elliptic * elliptic = -1
  /-- Hyperbolic square law. -/
  hyperbolic_sq_one : hyperbolic * hyperbolic = 1
  /-- Parabolic nilpotence law. -/
  parabolic_sq_zero : parabolic * parabolic = 0

namespace CompassTriple

variable {Op : Type*} [Mul Op] [One Op] [Zero Op] [Neg Op]
variable (C : CompassTriple Op)

/-- The elliptic operator squares to `-1`. -/
theorem elliptic_sq :
    C.elliptic * C.elliptic = -1 :=
  C.elliptic_sq_neg_one

/-- The hyperbolic operator squares to `1`. -/
theorem hyperbolic_sq :
    C.hyperbolic * C.hyperbolic = 1 :=
  C.hyperbolic_sq_one

/-- The parabolic operator squares to `0`. -/
theorem parabolic_sq :
    C.parabolic * C.parabolic = 0 :=
  C.parabolic_sq_zero

end CompassTriple

/-- A finite/indexed compass chain. -/
abbrev CompassChain (ι Op : Type*) [Mul Op] [One Op] [Zero Op] [Neg Op] :=
  ι → CompassTriple Op

/-- Transport a compass chain along a permutation of sites. -/
def permuteChain {ι Op : Type*} [Mul Op] [One Op] [Zero Op] [Neg Op]
    (σ : Equiv.Perm ι) (C : CompassChain ι Op) : CompassChain ι Op :=
  fun i => C (σ.symm i)

@[simp]
theorem permuteChain_apply {ι Op : Type*} [Mul Op] [One Op] [Zero Op] [Neg Op]
    (σ : Equiv.Perm ι) (C : CompassChain ι Op) (i : ι) :
    permuteChain σ C i = C (σ.symm i) :=
  rfl

/-- Permutation transport preserves the elliptic compass law at every site. -/
theorem permuteChain_elliptic_sq {ι Op : Type*} [Mul Op] [One Op] [Zero Op] [Neg Op]
    (σ : Equiv.Perm ι) (C : CompassChain ι Op) (i : ι) :
    (permuteChain σ C i).elliptic * (permuteChain σ C i).elliptic = -1 :=
  (C (σ.symm i)).elliptic_sq

/-- Permutation transport preserves the hyperbolic compass law at every site. -/
theorem permuteChain_hyperbolic_sq {ι Op : Type*} [Mul Op] [One Op] [Zero Op] [Neg Op]
    (σ : Equiv.Perm ι) (C : CompassChain ι Op) (i : ι) :
    (permuteChain σ C i).hyperbolic * (permuteChain σ C i).hyperbolic = 1 :=
  (C (σ.symm i)).hyperbolic_sq

/-- Permutation transport preserves the parabolic compass law at every site. -/
theorem permuteChain_parabolic_sq {ι Op : Type*} [Mul Op] [One Op] [Zero Op] [Neg Op]
    (σ : Equiv.Perm ι) (C : CompassChain ι Op) (i : ι) :
    (permuteChain σ C i).parabolic * (permuteChain σ C i).parabolic = 0 :=
  (C (σ.symm i)).parabolic_sq

/-- Braid-word transport of a compass chain over countably indexed sites. -/
def braidTransport {Op : Type*} [Mul Op] [One Op] [Zero Op] [Neg Op]
    (w : BraidWord) (C : CompassChain ℕ Op) : CompassChain ℕ Op :=
  permuteChain (evalBraidWord w) C

@[simp]
theorem braidTransport_apply {Op : Type*} [Mul Op] [One Op] [Zero Op] [Neg Op]
    (w : BraidWord) (C : CompassChain ℕ Op) (i : ℕ) :
    braidTransport w C i = C ((evalBraidWord w).symm i) :=
  rfl

/-- Braid transport preserves the elliptic compass law at every site. -/
theorem braidTransport_elliptic_sq {Op : Type*} [Mul Op] [One Op] [Zero Op] [Neg Op]
    (w : BraidWord) (C : CompassChain ℕ Op) (i : ℕ) :
    (braidTransport w C i).elliptic * (braidTransport w C i).elliptic = -1 :=
  permuteChain_elliptic_sq (evalBraidWord w) C i

/-- Braid transport preserves the hyperbolic compass law at every site. -/
theorem braidTransport_hyperbolic_sq {Op : Type*} [Mul Op] [One Op] [Zero Op] [Neg Op]
    (w : BraidWord) (C : CompassChain ℕ Op) (i : ℕ) :
    (braidTransport w C i).hyperbolic * (braidTransport w C i).hyperbolic = 1 :=
  permuteChain_hyperbolic_sq (evalBraidWord w) C i

/-- Braid transport preserves the parabolic compass law at every site. -/
theorem braidTransport_parabolic_sq {Op : Type*} [Mul Op] [One Op] [Zero Op] [Neg Op]
    (w : BraidWord) (C : CompassChain ℕ Op) (i : ℕ) :
    (braidTransport w C i).parabolic * (braidTransport w C i).parabolic = 0 :=
  permuteChain_parabolic_sq (evalBraidWord w) C i

/-- Braid transport is invariant under the adjacent braid/Yang--Baxter rewrite. -/
theorem braidTransport_braid_rewrite {Op : Type*} [Mul Op] [One Op] [Zero Op] [Neg Op]
    (i : ℕ) (left right : BraidWord) (C : CompassChain ℕ Op) :
    braidTransport (left ++ [i, i + 1, i] ++ right) C =
      braidTransport (left ++ [i + 1, i, i + 1] ++ right) C := by
  unfold braidTransport
  rw [evalBraidWord_braid_rewrite]

/-- Braid transport is invariant under separated-commutation rewrites. -/
theorem braidTransport_commute_rewrite {Op : Type*} [Mul Op] [One Op] [Zero Op] [Neg Op]
    {i j : ℕ} (hsep : i + 1 < j) (left right : BraidWord) (C : CompassChain ℕ Op) :
    braidTransport (left ++ [i, j] ++ right) C =
      braidTransport (left ++ [j, i] ++ right) C := by
  unfold braidTransport
  rw [evalBraidWord_commute_rewrite hsep]

end FiniteCompassBraidedChain
