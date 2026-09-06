import InfoGeometry.Canonical.G2HolonomyDifferentialForms
import InfoGeometry.Canonical.DiscreteRationalHodgeConjugation

namespace InfoGeometry.Canonical

/-!
# Clifford-sign convention for the finite Hodge--Dirac bridge

The repository's `rationalDiracKahler` uses the physicist convention `d + δ`.
Clifford analysis often uses `∇ = d - δ`.  This owner records the latter on
the same abstract rational module and proves its square identity.  It does
not assert a smooth monogenic decomposition or a boundary DN theorem.
-/

def cliffordHodgeDirac
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (d cod : V →ₗ[ℚ] V) : V →ₗ[ℚ] V :=
  d - cod

def cliffordMonogenic
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (d cod : V →ₗ[ℚ] V) (x : V) : Prop :=
  cliffordHodgeDirac d cod x = 0

theorem cliffordHodgeDirac_apply
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (d cod : V →ₗ[ℚ] V) (x : V) :
    cliffordHodgeDirac d cod x = d x - cod x := by
  rfl

theorem cliffordHodgeDirac_sq_eq_neg_hodgeLaplacian
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (d cod : V →ₗ[ℚ] V)
    (hd : d.comp d = 0)
    (hcod : cod.comp cod = 0) :
    (cliffordHodgeDirac d cod).comp
        (cliffordHodgeDirac d cod) =
      -(rationalHodgeLaplacian d cod) := by
  ext x
  simp only [cliffordHodgeDirac, LinearMap.sub_apply, LinearMap.comp_apply,
    rationalHodgeLaplacian, LinearMap.add_apply]
  have hd_x : d (d x) = 0 := by
    have h := congrArg (fun f : V →ₗ[ℚ] V => f x) hd
    simpa [LinearMap.comp_apply] using h
  have hcod_x : cod (cod x) = 0 := by
    have h := congrArg (fun f : V →ₗ[ℚ] V => f x) hcod
    simpa [LinearMap.comp_apply] using h
  simp only [map_sub]
  rw [hd_x, hcod_x]
  simp only [zero_sub, sub_zero, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.neg_apply]
  change -d (cod x) - cod (d x) = -(d (cod x) + cod (d x))
  abel

theorem cliffordMonogenic_iff
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (d cod : V →ₗ[ℚ] V) (x : V) :
    cliffordMonogenic d cod x ↔ d x = cod x := by
  unfold cliffordMonogenic cliffordHodgeDirac
  constructor
  · exact sub_eq_zero.mp
  · exact sub_eq_zero.mpr

theorem cliffordMonogenic_implies_hodge_harmonic
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (d cod : V →ₗ[ℚ] V)
    (hd : d.comp d = 0)
    (hcod : cod.comp cod = 0)
    {x : V}
    (hx : cliffordMonogenic d cod x) :
    rationalHodgeLaplacian d cod x = 0 := by
  have hDsq := congrArg
    (fun f : V →ₗ[ℚ] V => f x)
    (cliffordHodgeDirac_sq_eq_neg_hodgeLaplacian d cod hd hcod)
  have hzero :
      (cliffordHodgeDirac d cod).comp
          (cliffordHodgeDirac d cod) x = 0 := by
    simp only [LinearMap.comp_apply]
    rw [hx]
    simp
  have hDsq' :
      (cliffordHodgeDirac d cod).comp
          (cliffordHodgeDirac d cod) x =
        -(rationalHodgeLaplacian d cod x) := by
    simpa [LinearMap.comp_apply] using hDsq
  rw [hzero] at hDsq'
  have : -(rationalHodgeLaplacian d cod x) = 0 := by
    exact hDsq'.symm
  exact neg_eq_zero.mp this

theorem linearMap_commutes_cliffordHodgeDirac
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (g d cod : V →ₗ[ℚ] V)
    (hd : g.comp d = d.comp g)
    (hcod : g.comp cod = cod.comp g) :
    g.comp (cliffordHodgeDirac d cod) =
      (cliffordHodgeDirac d cod).comp g := by
  ext x
  simp only [cliffordHodgeDirac, LinearMap.comp_apply, LinearMap.sub_apply]
  have hd_x := congrArg (fun f : V →ₗ[ℚ] V => f x) hd
  have hcod_x := congrArg (fun f : V →ₗ[ℚ] V => f x) hcod
  simpa [LinearMap.comp_apply] using congrArg₂ (· - ·) hd_x hcod_x

theorem linearMap_preserves_cliffordMonogenic
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (g d cod : V →ₗ[ℚ] V)
    (hd : g.comp d = d.comp g)
    (hcod : g.comp cod = cod.comp g)
    {x : V}
    (hx : cliffordMonogenic d cod x) :
    cliffordMonogenic d cod (g x) := by
  unfold cliffordMonogenic at *
  have hcomm := linearMap_commutes_cliffordHodgeDirac g d cod hd hcod
  have hzero : g (cliffordHodgeDirac d cod x) = 0 := by
    rw [hx]
    simp
  have h := congrArg (fun f : V →ₗ[ℚ] V => f x) hcomm
  have h' : g (cliffordHodgeDirac d cod x) =
      cliffordHodgeDirac d cod (g x) := by
    simpa [LinearMap.comp_apply] using h
  rw [hzero] at h'
  exact h'.symm

theorem linearMap_commutes_hodgeLaplacian
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (g d cod : V →ₗ[ℚ] V)
    (hd : g.comp d = d.comp g)
    (hcod : g.comp cod = cod.comp g) :
    g.comp (rationalHodgeLaplacian d cod) =
      (rationalHodgeLaplacian d cod).comp g := by
  ext x
  have hd_cod := congrArg (fun f : V →ₗ[ℚ] V => f (cod x)) hd
  have hcod_d := congrArg (fun f : V →ₗ[ℚ] V => f (d x)) hcod
  have hd_x : g (d x) = d (g x) := by
    simpa [LinearMap.comp_apply] using congrArg
      (fun f : V →ₗ[ℚ] V => f x) hd
  have hcod_x : g (cod x) = cod (g x) := by
    simpa [LinearMap.comp_apply] using congrArg
      (fun f : V →ₗ[ℚ] V => f x) hcod
  simp only [rationalHodgeLaplacian, LinearMap.add_apply,
    LinearMap.comp_apply] at *
  simpa [add_comm, hcod_x, hd_x] using congrArg₂ (· + ·) hd_cod hcod_d

theorem linearMap_preserves_hodgeHarmonic
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (g d cod : V →ₗ[ℚ] V)
    (hd : g.comp d = d.comp g)
    (hcod : g.comp cod = cod.comp g)
    {x : V}
    (hx : rationalHodgeLaplacian d cod x = 0) :
    rationalHodgeLaplacian d cod (g x) = 0 := by
  have hcomm := linearMap_commutes_hodgeLaplacian g d cod hd hcod
  have h := congrArg (fun f : V →ₗ[ℚ] V => f x) hcomm
  have h' : g (rationalHodgeLaplacian d cod x) =
      rationalHodgeLaplacian d cod (g x) := by
    simpa [LinearMap.comp_apply] using h
  rw [hx] at h'
  simpa using h'.symm

end InfoGeometry.Canonical
