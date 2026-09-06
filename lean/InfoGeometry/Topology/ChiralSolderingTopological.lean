import Mathlib
import InfoGeometry.Algebra.ZornMatrix

/-!
# Topological chiral soldering on the native Zorn carrier

This owner equips the native algebraic `ZornMatrix ℂ` carrier with its
coordinate topology and proves continuity of native multiplication and of
the soldering evaluation `(X,S) ↦ leftMulOp X S`.  It introduces no second
Zorn carrier and makes no analytic completion claim.
-/

namespace InfoGeometry.Topology.ChiralSolderingTopological

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix

noncomputable section

abbrev Zorn := InfoGeometry.Algebra.ZornMatrix ℂ

instance zornTopologicalSpace : TopologicalSpace Zorn :=
  TopologicalSpace.induced (ZornMatrix.coordEquiv (R := ℂ)) inferInstance

theorem continuous_zorn_coordEquiv :
    Continuous (ZornMatrix.coordEquiv (R := ℂ) : Zorn → _ ) :=
  continuous_induced_dom

theorem continuous_zorn_a : Continuous (fun X : Zorn => X.a) := by
  exact continuous_fst.comp continuous_zorn_coordEquiv

theorem continuous_zorn_v : Continuous (fun X : Zorn => X.v) := by
  exact continuous_fst.comp (continuous_snd.comp continuous_zorn_coordEquiv)

theorem continuous_zorn_w : Continuous (fun X : Zorn => X.w) := by
  exact continuous_fst.comp (continuous_snd.comp
    (continuous_snd.comp continuous_zorn_coordEquiv))

theorem continuous_zorn_b : Continuous (fun X : Zorn => X.b) := by
  exact continuous_snd.comp (continuous_snd.comp
    (continuous_snd.comp continuous_zorn_coordEquiv))

private theorem continuous_vec3_dot :
    Continuous (fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) =>
      Vec3.dot p.1 p.2) := by
  unfold Vec3.dot
  fun_prop

private theorem continuous_vec3_cross :
    Continuous (fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) =>
      Vec3.cross p.1 p.2) := by
  unfold Vec3.cross
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) =>
      p.1 1 * p.2 2 - p.1 2 * p.2 1)
    fun_prop
  · change Continuous (fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) =>
      p.1 2 * p.2 0 - p.1 0 * p.2 2)
    fun_prop
  · change Continuous (fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) =>
      p.1 0 * p.2 1 - p.1 1 * p.2 0)
    fun_prop

private theorem continuous_vec3_add :
    Continuous (fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) =>
      Vec3.add p.1 p.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;>
    change Continuous (fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) =>
      p.1 _ + p.2 _)
  all_goals fun_prop

private theorem continuous_vec3_sub :
    Continuous (fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) =>
      Vec3.sub p.1 p.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;>
    change Continuous (fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) =>
      p.1 _ - p.2 _)
  all_goals fun_prop

private theorem continuous_vec3_smul :
    Continuous (fun p : ℂ × (Fin 3 → ℂ) =>
      Vec3.smul p.1 p.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;>
    change Continuous (fun p : ℂ × (Fin 3 → ℂ) => p.1 * p.2 _)
  all_goals fun_prop

theorem continuous_zorn_mul :
    Continuous (fun p : Zorn × Zorn => p.1 * p.2) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p : Zorn × Zorn =>
    ZornMatrix.coordEquiv (p.1 * p.2))
  simp only [ZornMatrix.coordEquiv, ZornMatrix.mul_eq_mul]
  change Continuous (fun p : Zorn × Zorn =>
    (p.1.a * p.2.a + Vec3.dot p.1.v p.2.w,
      Vec3.sub (Vec3.add (Vec3.smul p.1.a p.2.v)
        (Vec3.smul p.2.b p.1.v)) (Vec3.cross p.1.w p.2.w),
      Vec3.add (Vec3.add (Vec3.smul p.2.a p.1.w)
        (Vec3.smul p.1.b p.2.w)) (Vec3.cross p.1.v p.2.v),
      Vec3.dot p.1.w p.2.v + p.1.b * p.2.b))
  have ha : Continuous (fun p : Zorn × Zorn => p.1.a * p.2.a) :=
    (continuous_zorn_a.comp continuous_fst).mul
      (continuous_zorn_a.comp continuous_snd)
  have hb : Continuous (fun p : Zorn × Zorn => p.1.b * p.2.b) :=
    (continuous_zorn_b.comp continuous_fst).mul
      (continuous_zorn_b.comp continuous_snd)
  have hvw : Continuous (fun p : Zorn × Zorn =>
      Vec3.dot p.1.v p.2.w) :=
    continuous_vec3_dot.comp
      ((continuous_zorn_v.comp continuous_fst).prodMk
        (continuous_zorn_w.comp continuous_snd))
  have hwv : Continuous (fun p : Zorn × Zorn =>
      Vec3.dot p.1.w p.2.v) :=
    continuous_vec3_dot.comp
      ((continuous_zorn_w.comp continuous_fst).prodMk
        (continuous_zorn_v.comp continuous_snd))
  have hcrossww : Continuous (fun p : Zorn × Zorn =>
      Vec3.cross p.1.w p.2.w) :=
    continuous_vec3_cross.comp
      ((continuous_zorn_w.comp continuous_fst).prodMk
        (continuous_zorn_w.comp continuous_snd))
  have hcrossvv : Continuous (fun p : Zorn × Zorn =>
      Vec3.cross p.1.v p.2.v) :=
    continuous_vec3_cross.comp
      ((continuous_zorn_v.comp continuous_fst).prodMk
        (continuous_zorn_v.comp continuous_snd))
  have hsmul_av : Continuous (fun p : Zorn × Zorn =>
      Vec3.smul p.1.a p.2.v) :=
    continuous_vec3_smul.comp
      ((continuous_zorn_a.comp continuous_fst).prodMk
        (continuous_zorn_v.comp continuous_snd))
  have hsmul_bv : Continuous (fun p : Zorn × Zorn =>
      Vec3.smul p.2.b p.1.v) :=
    continuous_vec3_smul.comp
      ((continuous_zorn_b.comp continuous_snd).prodMk
        (continuous_zorn_v.comp continuous_fst))
  have hsmul_aw : Continuous (fun p : Zorn × Zorn =>
      Vec3.smul p.2.a p.1.w) :=
    continuous_vec3_smul.comp
      ((continuous_zorn_a.comp continuous_snd).prodMk
        (continuous_zorn_w.comp continuous_fst))
  have hsmul_bw : Continuous (fun p : Zorn × Zorn =>
      Vec3.smul p.1.b p.2.w) :=
    continuous_vec3_smul.comp
      ((continuous_zorn_b.comp continuous_fst).prodMk
        (continuous_zorn_w.comp continuous_snd))
  have hadd_v : Continuous (fun p : Zorn × Zorn =>
      Vec3.add (Vec3.smul p.1.a p.2.v) (Vec3.smul p.2.b p.1.v)) :=
    continuous_vec3_add.comp (hsmul_av.prodMk hsmul_bv)
  have hsub_v : Continuous (fun p : Zorn × Zorn =>
      Vec3.sub (Vec3.add (Vec3.smul p.1.a p.2.v)
        (Vec3.smul p.2.b p.1.v)) (Vec3.cross p.1.w p.2.w)) :=
    continuous_vec3_sub.comp (hadd_v.prodMk hcrossww)
  have hadd_w : Continuous (fun p : Zorn × Zorn =>
      Vec3.add (Vec3.add (Vec3.smul p.2.a p.1.w)
        (Vec3.smul p.1.b p.2.w)) (Vec3.cross p.1.v p.2.v)) :=
    continuous_vec3_add.comp
      ((continuous_vec3_add.comp (hsmul_aw.prodMk hsmul_bw)).prodMk hcrossvv)
  exact ha.add hvw |>.prodMk (hsub_v.prodMk (hadd_w.prodMk (hwv.add hb)))

theorem continuous_chiral_soldering_evaluation :
    Continuous (fun p : Zorn × Zorn =>
      p.1 * p.2) := by
  exact continuous_zorn_mul

theorem continuous_zorn_add :
    Continuous (fun p : Zorn × Zorn => p.1 + p.2) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p : Zorn × Zorn =>
    ZornMatrix.coordEquiv (p.1 + p.2))
  simp only [ZornMatrix.coordEquiv, ZornMatrix.add]
  change Continuous (fun p : Zorn × Zorn =>
    (p.1.a + p.2.a, Vec3.add p.1.v p.2.v,
      Vec3.add p.1.w p.2.w, p.1.b + p.2.b))
  exact (continuous_zorn_a.comp continuous_fst).add
      (continuous_zorn_a.comp continuous_snd) |>.prodMk
    ((continuous_vec3_add.comp
      ((continuous_zorn_v.comp continuous_fst).prodMk
        (continuous_zorn_v.comp continuous_snd))).prodMk
      ((continuous_vec3_add.comp
        ((continuous_zorn_w.comp continuous_fst).prodMk
          (continuous_zorn_w.comp continuous_snd))).prodMk
        ((continuous_zorn_b.comp continuous_fst).add
          (continuous_zorn_b.comp continuous_snd))))

/-- The native trace is a continuous scalar readout. -/
theorem continuous_zornTrace :
    Continuous (fun X : Zorn => ZornMatrix.zornTrace X) := by
  simpa [ZornMatrix.zornTrace] using continuous_zorn_a.add continuous_zorn_b

/-- The native quadratic norm is a continuous scalar readout. -/
theorem continuous_zornNorm :
    Continuous (fun X : Zorn => ZornMatrix.zornNorm X) := by
  have hab : Continuous (fun X : Zorn => X.a * X.b) :=
    continuous_zorn_a.mul continuous_zorn_b
  have hvw : Continuous (fun X : Zorn => Vec3.dot X.v X.w) :=
    continuous_vec3_dot.comp (continuous_zorn_v.prodMk continuous_zorn_w)
  simpa [ZornMatrix.zornNorm] using hab.sub hvw

/-! ### Associator data of the operator lift -/

/-- The two parenthesizations of a native Zorn triple, kept separate because
the carrier is nonassociative. -/
def zornAssociatorPair (X Y Z : Zorn) : Zorn × Zorn :=
  ((X * Y) * Z, X * (Y * Z))

theorem continuous_zornAssociatorPair :
    Continuous (fun p : Zorn × Zorn × Zorn =>
      zornAssociatorPair p.1 p.2.1 p.2.2) := by
  have hxy : Continuous (fun p : Zorn × Zorn × Zorn =>
      (p.1 * p.2.1, p.2.2)) := by
    exact (continuous_zorn_mul.comp
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
        (continuous_snd.comp continuous_snd)
  have hyz : Continuous (fun p : Zorn × Zorn × Zorn =>
      (p.1, p.2.1 * p.2.2)) := by
    exact (continuous_fst.prodMk
      (continuous_zorn_mul.comp
        ((continuous_fst.comp continuous_snd).prodMk
          (continuous_snd.comp continuous_snd))))
  exact (continuous_zorn_mul.comp hxy).prodMk
    (continuous_zorn_mul.comp hyz)

end
end InfoGeometry.Topology.ChiralSolderingTopological
