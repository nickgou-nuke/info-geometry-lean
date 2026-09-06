import InfoGeometry.Canonical.SplitG2DiscreteGaugeCochain

namespace InfoGeometry.Canonical

/-!
# Composition of discrete split-`G₂` parallel transports

`parallelTransport` is defined by a right fold of the edge automorphisms.
This owner records the resulting path-composition law.  It is the small
topological bridge needed before discussing path-groupoid actions or
curvature on cellular cochains; no smooth holonomy or quotient identification
is asserted here.
-/

@[simp] theorem SplitG2Automorphism.id_comp
    (φ : SplitG2Automorphism) :
    SplitG2Automorphism.comp SplitG2Automorphism.id φ = φ := by
  cases φ
  rfl

@[simp] theorem SplitG2Automorphism.comp_id
    (φ : SplitG2Automorphism) :
    SplitG2Automorphism.comp φ SplitG2Automorphism.id = φ := by
  cases φ
  rfl

theorem parallelTransport_append
    {E : Type*} (A : SplitG2GaugeConnection E)
    (p q : List E) :
    parallelTransport A (p ++ q) =
      SplitG2Automorphism.comp
        (parallelTransport A p) (parallelTransport A q) := by
  induction p with
  | nil =>
      simp
  | cons e p ih =>
      simp only [List.cons_append, parallelTransport_cons, ih]
      rfl

theorem parallelTransport_append_apply
    {E : Type*} (A : SplitG2GaugeConnection E)
    (p q : List E) (x : imaginarySplitOctonion) :
    parallelTransport A (p ++ q) x =
      parallelTransport A p (parallelTransport A q x) := by
  rw [parallelTransport_append]
  rfl

theorem parallelTransport_append_preserves_threeForm
    {E : Type*} (A : SplitG2GaugeConnection E)
    (p q : List E) (x y z : imaginarySplitOctonion) :
    canonicalSplitG2ThreeFormValue
        (parallelTransport A (p ++ q) x)
        (parallelTransport A (p ++ q) y)
        (parallelTransport A (p ++ q) z) =
      canonicalSplitG2ThreeFormValue x y z := by
  exact parallelTransport_preserves_threeForm A (p ++ q) x y z

theorem pathPullbackForm_append
    {E : Type*} {k : ℕ}
    (A : SplitG2GaugeConnection E)
    (p q : List E)
    (ω : AlternatingMap ℚ imaginarySplitOctonion ℚ (Fin k)) :
    pathPullbackForm A (p ++ q) ω =
      pathPullbackForm A q (pathPullbackForm A p ω) := by
  ext v
  change ω (fun i => parallelTransport A (p ++ q) (v i)) =
    ω (fun i => parallelTransport A p (parallelTransport A q (v i)))
  congr 1
  funext i
  exact parallelTransport_append_apply A p q (v i)

end InfoGeometry.Canonical
