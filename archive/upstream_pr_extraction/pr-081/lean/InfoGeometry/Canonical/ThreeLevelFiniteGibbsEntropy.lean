import InfoGeometry.Canonical.ThreeLevelFiniteGibbsVariational
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators

namespace InfoGeometry.Canonical

namespace ThreeLevelFiniteGibbs

variable {SuperSector Sector : Type*}
  [Fintype SuperSector] [Nonempty SuperSector]
  [Fintype Sector] [Nonempty Sector] [DecidableEq SuperSector]
variable (State : Sector → Type*)
variable [∀ s, Fintype (State s)] [∀ s, Nonempty (State s)]

/-- Shannon entropy of a finite weight function. -/
noncomputable def finiteEntropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  -∑ x, p x * Real.log (p x)

/-- Entropy of a product distribution is the sum of the factor entropies. -/
theorem finiteEntropy_product_eq_add
    {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (q : β → ℝ)
    (hp_pos : ∀ a, 0 < p a) (hq_pos : ∀ b, 0 < q b)
    (hp_sum : ∑ a, p a = 1) (hq_sum : ∑ b, q b = 1) :
    finiteEntropy (fun z : α × β => p z.1 * q z.2) =
      finiteEntropy p + finiteEntropy q := by
  classical
  unfold finiteEntropy
  rw [Fintype.sum_prod_type]
  have hlog : ∀ a b, Real.log (p a * q b) = Real.log (p a) + Real.log (q b) := by
    intro a b
    exact Real.log_mul (ne_of_gt (hp_pos a)) (ne_of_gt (hq_pos b))
  simp_rw [hlog]
  simp_rw [mul_add]
  simp_rw [Finset.sum_add_distrib]
  have hfirst :
      ∑ a, ∑ b, p a * q b * Real.log (p a) =
        ∑ a, p a * Real.log (p a) := by
    apply Finset.sum_congr rfl
    intro a ha
    calc
      ∑ b, p a * q b * Real.log (p a) =
          ∑ b, q b * (p a * Real.log (p a)) := by
            apply Finset.sum_congr rfl
            intro b hb
            ring
      _ = (∑ b, q b) * (p a * Real.log (p a)) := by
            rw [Finset.sum_mul]
      _ = p a * Real.log (p a) := by
            rw [hq_sum]
            ring
  have hsecond :
      ∑ a, ∑ b, p a * q b * Real.log (q b) =
        ∑ b, q b * Real.log (q b) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    calc
      ∑ a, p a * q b * Real.log (q b) =
          ∑ a, p a * (q b * Real.log (q b)) := by
            apply Finset.sum_congr rfl
            intro a ha
            ring
      _ = (∑ a, p a) * (q b * Real.log (q b)) := by
            rw [Finset.sum_mul]
      _ = q b * Real.log (q b) := by
            rw [hp_sum]
            ring
  rw [hfirst, hsecond]
  ring

/-- Scaling a normalized finite distribution gives the corresponding weighted entropy. -/
theorem finiteEntropy_smul_normalized_eq
    {α : Type*} [Fintype α]
    (a : ℝ) (r : α → ℝ)
    (ha : 0 < a) (hr_pos : ∀ x, 0 < r x)
    (hr_sum : ∑ x, r x = 1) :
    finiteEntropy (fun x => a * r x) =
      a * finiteEntropy r - a * Real.log a := by
  classical
  unfold finiteEntropy
  have hlog : ∀ x, Real.log (a * r x) = Real.log a + Real.log (r x) := by
    intro x
    exact Real.log_mul (ne_of_gt ha) (ne_of_gt (hr_pos x))
  simp_rw [hlog, mul_add]
  simp_rw [Finset.sum_add_distrib]
  have hscale : ∑ x, a * r x * Real.log a = a * Real.log a := by
    calc
      ∑ x, a * r x * Real.log a =
          (∑ x, r x) * (a * Real.log a) := by
            rw [show (∑ x, a * r x * Real.log a) =
                ∑ x, r x * (a * Real.log a) by
                  apply Finset.sum_congr rfl
                  intro x hx
                  ring]
            rw [Finset.sum_mul]
      _ = a * Real.log a := by rw [hr_sum]; ring
  have hentropy : ∑ x, a * r x * Real.log (r x) =
      a * ∑ x, r x * Real.log (r x) := by
    rw [show (∑ x, a * r x * Real.log (r x)) =
        ∑ x, (r x * Real.log (r x)) * a by
          apply Finset.sum_congr rfl
          intro x hx
          ring]
    rw [← Finset.sum_mul]
    ring
  rw [hscale, hentropy]
  ring

/-- Entropy of the outer super-sector distribution. -/
noncomputable def outerEntropy
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ) : ℝ :=
  finiteEntropy (fun g => outerWeight State super energy particleNumber superNumber β μ ν g)

/-- Entropy inside one retained super-sector fiber. -/
noncomputable def fiberEntropy
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (g : SuperSector) : ℝ :=
  -(superFiber super g).sum (fun s =>
    fiberSectorWeight State super energy particleNumber β μ g s *
      Real.log (fiberSectorWeight State super energy particleNumber β μ g s))

/-- Entropy inside one sector conditioned on a fixed sector state. -/
noncomputable def conditionalEntropy
    (energy : ∀ s, State s → ℝ) (β : ℝ) (s : Sector) : ℝ :=
  finiteEntropy (fun x => conditionalWeight State energy β s x)

/-- Product-form three-level joint weight. -/
noncomputable def layeredJointWeight
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (g : SuperSector) (s : Sector) (x : State s) : ℝ :=
  outerWeight State super energy particleNumber superNumber β μ ν g *
    fiberSectorWeight State super energy particleNumber β μ g s *
    conditionalWeight State energy β s x

/-- Shannon entropy of the complete dependent three-level Gibbs tower. -/
noncomputable def layeredEntropy
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ) : ℝ :=
  -∑ g, (superFiber super g).sum (fun s => ∑ x,
    layeredJointWeight State super energy particleNumber superNumber β μ ν g s x *
      Real.log (layeredJointWeight State super energy particleNumber superNumber β μ ν g s x))

/-- Conditional weights are strictly positive. -/
theorem conditionalWeight_pos
    (energy : ∀ s, State s → ℝ) (β : ℝ) (s : Sector) (x : State s) :
    0 < conditionalWeight State energy β s x := by
  unfold conditionalWeight
  exact div_pos (Real.exp_pos _)
    (canonicalPartition_pos State energy β s)

/-- Fiber-sector weights are strictly positive on each retained fiber. -/
theorem fiberSectorWeight_pos
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (β μ : ℝ) (fiber_nonempty : ∀ g, (superFiber super g).Nonempty)
    (g : SuperSector) (s : Sector) :
    0 < fiberSectorWeight State super energy particleNumber β μ g s := by
  unfold fiberSectorWeight
  exact div_pos (middleNumerator_pos State energy particleNumber β μ s)
    (superPartition_pos State super energy particleNumber β μ fiber_nonempty g)

/-- Outer super-sector weights are strictly positive. -/
theorem outerWeight_pos
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty)
    (g : SuperSector) :
    0 < outerWeight State super energy particleNumber superNumber β μ ν g := by
  unfold outerWeight
  exact div_pos (outerNumerator_pos State super energy particleNumber superNumber
    β μ ν fiber_nonempty g)
      (grandPartition_pos State super energy particleNumber superNumber β μ ν fiber_nonempty)

/-- The product-form joint weight is the product of the three normalized layers. -/
theorem layeredJointWeight_eq_outerWeight_mul_fiberSectorWeight_mul_conditionalWeight
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (g : SuperSector) (s : Sector) (x : State s) :
    layeredJointWeight State super energy particleNumber superNumber β μ ν g s x =
      outerWeight State super energy particleNumber superNumber β μ ν g *
        fiberSectorWeight State super energy particleNumber β μ g s *
        conditionalWeight State energy β s x := by
  rfl

/-- The product-form three-level joint weight is strictly positive. -/
theorem layeredJointWeight_pos
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty)
    (g : SuperSector) (s : Sector) (x : State s) :
    0 < layeredJointWeight State super energy particleNumber superNumber β μ ν g s x := by
  rw [layeredJointWeight_eq_outerWeight_mul_fiberSectorWeight_mul_conditionalWeight]
  have houter := outerWeight_pos State super energy particleNumber superNumber β μ ν
    fiber_nonempty g
  have hfiber := fiberSectorWeight_pos State super energy particleNumber β μ fiber_nonempty g s
  have hcond := conditionalWeight_pos State energy β s x
  have hpair : 0 < outerWeight State super energy particleNumber superNumber β μ ν g *
      fiberSectorWeight State super energy particleNumber β μ g s :=
    mul_pos houter hfiber
  exact mul_pos hpair hcond

/-! The factorized hierarchy is not a second probability model: after the
    partition factors cancel, it is the canonical joint Gibbs weight. -/
theorem layeredJointWeight_eq_jointWeight
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty)
    (g : SuperSector) (s : Sector) (x : State s) :
    layeredJointWeight State super energy particleNumber superNumber β μ ν g s x =
      jointWeight State super energy particleNumber superNumber β μ ν g s x := by
  unfold layeredJointWeight outerWeight fiberSectorWeight conditionalWeight jointWeight
    outerNumerator middleNumerator jointNumerator
  have hcanonical : canonicalPartition State energy β s ≠ 0 :=
    ne_of_gt (canonicalPartition_pos State energy β s)
  have hsuper : superPartition State super energy particleNumber β μ g ≠ 0 :=
    ne_of_gt (superPartition_pos State super energy particleNumber β μ fiber_nonempty g)
  have hgrand : grandPartition State super energy particleNumber superNumber β μ ν ≠ 0 :=
    ne_of_gt (grandPartition_pos State super energy particleNumber superNumber β μ ν
      fiber_nonempty)
  field_simp [hcanonical, hsuper, hgrand]

/-- The canonical joint Gibbs weight is strictly positive on every retained state. -/
theorem jointWeight_pos
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty)
    (g : SuperSector) (s : Sector) (x : State s) :
    0 < jointWeight State super energy particleNumber superNumber β μ ν g s x := by
  rw [← layeredJointWeight_eq_jointWeight State super energy particleNumber superNumber
    β μ ν fiber_nonempty g s x]
  exact layeredJointWeight_pos State super energy particleNumber superNumber β μ ν
    fiber_nonempty g s x

/-- The canonical joint Gibbs weight never vanishes. -/
theorem jointWeight_ne_zero
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty)
    (g : SuperSector) (s : Sector) (x : State s) :
    jointWeight State super energy particleNumber superNumber β μ ν g s x ≠ 0 :=
  ne_of_gt (jointWeight_pos State super energy particleNumber superNumber β μ ν
    fiber_nonempty g s x)

/-- The joint surprisal potential splits additively across the three Gibbs layers. -/
theorem log_jointWeight_eq_sum_log_layeredWeights
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty)
    (g : SuperSector) (s : Sector) (x : State s) :
    Real.log (jointWeight State super energy particleNumber superNumber β μ ν g s x) =
      Real.log (outerWeight State super energy particleNumber superNumber β μ ν g) +
        Real.log (fiberSectorWeight State super energy particleNumber β μ g s) +
        Real.log (conditionalWeight State energy β s x) := by
  rw [← layeredJointWeight_eq_jointWeight State super energy particleNumber superNumber
    β μ ν fiber_nonempty g s x]
  rw [show layeredJointWeight State super energy particleNumber superNumber β μ ν g s x =
      (outerWeight State super energy particleNumber superNumber β μ ν g *
        fiberSectorWeight State super energy particleNumber β μ g s) *
        conditionalWeight State energy β s x by rfl]
  have houter : outerWeight State super energy particleNumber superNumber β μ ν g ≠ 0 :=
    ne_of_gt (outerWeight_pos State super energy particleNumber superNumber β μ ν
      fiber_nonempty g)
  have hfiber : fiberSectorWeight State super energy particleNumber β μ g s ≠ 0 :=
    ne_of_gt (fiberSectorWeight_pos State super energy particleNumber β μ
      fiber_nonempty g s)
  have hconditional : conditionalWeight State energy β s x ≠ 0 :=
    ne_of_gt (conditionalWeight_pos State energy β s x)
  rw [Real.log_mul (mul_ne_zero houter hfiber) hconditional]
  rw [Real.log_mul houter hfiber]

/-- Marginalizing the fine state leaves the outer and fiber weights. -/
theorem sum_layeredJointWeight_over_state
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (g : SuperSector) (s : Sector) :
    ∑ x, layeredJointWeight State super energy particleNumber superNumber β μ ν g s x =
      outerWeight State super energy particleNumber superNumber β μ ν g *
        fiberSectorWeight State super energy particleNumber β μ g s := by
  unfold layeredJointWeight
  calc
    ∑ x, outerWeight State super energy particleNumber superNumber β μ ν g *
        fiberSectorWeight State super energy particleNumber β μ g s *
        conditionalWeight State energy β s x =
      ∑ x, conditionalWeight State energy β s x *
        (outerWeight State super energy particleNumber superNumber β μ ν g *
          fiberSectorWeight State super energy particleNumber β μ g s) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
    _ = (∑ x, conditionalWeight State energy β s x) *
        (outerWeight State super energy particleNumber superNumber β μ ν g *
          fiberSectorWeight State super energy particleNumber β μ g s) := by
            rw [Finset.sum_mul]
    _ = outerWeight State super energy particleNumber superNumber β μ ν g *
        fiberSectorWeight State super energy particleNumber β μ g s := by
            have hconditional : (∑ x, conditionalWeight State energy β s x) = 1 := by
              classical
              unfold conditionalWeight
              simp_rw [div_eq_mul_inv]
              rw [← Finset.sum_mul]
              exact mul_inv_cancel₀ (ne_of_gt (canonicalPartition_pos State energy β s))
            rw [hconditional]
            ring

/-- Marginalizing a super-sector fiber recovers its outer Gibbs weight. -/
theorem sum_layeredJointWeight_over_sector
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty) (g : SuperSector) :
    (superFiber super g).sum (fun s => ∑ x,
      layeredJointWeight State super energy particleNumber superNumber β μ ν g s x) =
      outerWeight State super energy particleNumber superNumber β μ ν g := by
  rw [show (superFiber super g).sum (fun s => ∑ x,
      layeredJointWeight State super energy particleNumber superNumber β μ ν g s x) =
      (superFiber super g).sum (fun s =>
        outerWeight State super energy particleNumber superNumber β μ ν g *
          fiberSectorWeight State super energy particleNumber β μ g s) by
        apply Finset.sum_congr rfl
        intro s hs
        exact sum_layeredJointWeight_over_state State super energy particleNumber
          superNumber β μ ν g s]
  rw [show (superFiber super g).sum (fun s =>
      outerWeight State super energy particleNumber superNumber β μ ν g *
        fiberSectorWeight State super energy particleNumber β μ g s) =
      outerWeight State super energy particleNumber superNumber β μ ν g *
        (superFiber super g).sum (fun s =>
          fiberSectorWeight State super energy particleNumber β μ g s) by
        rw [Finset.mul_sum]]
  rw [sum_fiberSectorWeight_eq_one State super energy particleNumber β μ fiber_nonempty g]
  ring

/-- The conditional Gibbs weights normalize inside each sector. -/
theorem sum_conditionalWeight_eq_one
    (energy : ∀ s, State s → ℝ) (β : ℝ) (s : Sector) :
    ∑ x, conditionalWeight State energy β s x = 1 := by
  classical
  unfold conditionalWeight
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  exact mul_inv_cancel₀ (ne_of_gt (canonicalPartition_pos State energy β s))

/-- Fine-state entropy in a fixed sector is the weighted conditional entropy
    plus the surprisal of the retained outer/fiber mass. -/
theorem finiteEntropy_layeredJointWeight_over_state_eq
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty)
    (g : SuperSector) (s : Sector) :
    finiteEntropy (fun x =>
      layeredJointWeight State super energy particleNumber superNumber β μ ν g s x) =
      (outerWeight State super energy particleNumber superNumber β μ ν g *
        fiberSectorWeight State super energy particleNumber β μ g s) *
        conditionalEntropy State energy β s -
      (outerWeight State super energy particleNumber superNumber β μ ν g *
        fiberSectorWeight State super energy particleNumber β μ g s) *
        Real.log (outerWeight State super energy particleNumber superNumber β μ ν g *
          fiberSectorWeight State super energy particleNumber β μ g s) := by
  have houter : 0 < outerWeight State super energy particleNumber superNumber β μ ν g :=
    outerWeight_pos State super energy particleNumber superNumber β μ ν
      fiber_nonempty g
  have hfiber : 0 < fiberSectorWeight State super energy particleNumber β μ g s :=
    fiberSectorWeight_pos State super energy particleNumber β μ
      fiber_nonempty g s
  have hconditional : ∀ x, 0 < conditionalWeight State energy β s x :=
    fun x => conditionalWeight_pos State energy β s x
  have hconditional_sum : ∑ x, conditionalWeight State energy β s x = 1 :=
    sum_conditionalWeight_eq_one State energy β s
  simpa [layeredJointWeight, conditionalEntropy] using
    (finiteEntropy_smul_normalized_eq
      (outerWeight State super energy particleNumber superNumber β μ ν g *
        fiberSectorWeight State super energy particleNumber β μ g s)
      (fun x => conditionalWeight State energy β s x)
      (mul_pos houter hfiber) hconditional hconditional_sum)

/-- Summing the fine-state entropy over a super-sector fiber produces the
    fiber entropy and the conditional-entropy contribution, together with
    the outer surprisal term. -/
theorem sum_finiteEntropy_layeredJointWeight_over_sector_eq
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty) (g : SuperSector) :
    (superFiber super g).sum (fun s =>
      finiteEntropy (fun x =>
        layeredJointWeight State super energy particleNumber superNumber β μ ν g s x)) =
      outerWeight State super energy particleNumber superNumber β μ ν g *
        fiberEntropy State super energy particleNumber β μ g +
      outerWeight State super energy particleNumber superNumber β μ ν g *
        (superFiber super g).sum (fun s =>
          fiberSectorWeight State super energy particleNumber β μ g s *
            conditionalEntropy State energy β s) -
      outerWeight State super energy particleNumber superNumber β μ ν g *
        Real.log (outerWeight State super energy particleNumber superNumber β μ ν g) := by
  classical
  let P := outerWeight State super energy particleNumber superNumber β μ ν g
  let Q := fun s => fiberSectorWeight State super energy particleNumber β μ g s
  have hP : 0 < P := by
    dsimp [P]
    exact outerWeight_pos State super energy particleNumber superNumber β μ ν fiber_nonempty g
  have hQ : ∀ s, 0 < Q s := by
    intro s
    dsimp [Q]
    exact fiberSectorWeight_pos State super energy particleNumber β μ fiber_nonempty g s
  have hslice : ∀ s, finiteEntropy (fun x =>
      layeredJointWeight State super energy particleNumber superNumber β μ ν g s x) =
      (P * Q s) * conditionalEntropy State energy β s -
        (P * Q s) * Real.log (P * Q s) := by
    intro s
    simpa [P, Q] using
      (finiteEntropy_layeredJointWeight_over_state_eq State super energy particleNumber
        superNumber β μ ν fiber_nonempty g s)
  rw [show (superFiber super g).sum (fun s =>
      finiteEntropy (fun x =>
        layeredJointWeight State super energy particleNumber superNumber β μ ν g s x)) =
      (superFiber super g).sum (fun s =>
        (P * Q s) * conditionalEntropy State energy β s -
          (P * Q s) * Real.log (P * Q s)) by
        apply Finset.sum_congr rfl
        intro s hs
        exact hslice s]
  have hlog : ∀ s, Real.log (P * Q s) = Real.log P + Real.log (Q s) := by
    intro s
    exact Real.log_mul (ne_of_gt hP) (ne_of_gt (hQ s))
  simp_rw [hlog, mul_add]
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hQsum : (superFiber super g).sum Q = 1 := by
    dsimp [Q]
    exact sum_fiberSectorWeight_eq_one State super energy particleNumber β μ fiber_nonempty g
  have hcondsum : (superFiber super g).sum (fun s =>
      Q s * conditionalEntropy State energy β s) =
      (superFiber super g).sum (fun s =>
        fiberSectorWeight State super energy particleNumber β μ g s *
          conditionalEntropy State energy β s) := by
    rfl
  rw [show (superFiber super g).sum (fun s =>
      P * Q s * conditionalEntropy State energy β s) =
      P * (superFiber super g).sum (fun s =>
        Q s * conditionalEntropy State energy β s) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        ring]
  rw [show (superFiber super g).sum (fun s =>
      P * Q s * Real.log P) =
      P * Real.log P * (superFiber super g).sum Q by
        calc
          (superFiber super g).sum (fun s => P * Q s * Real.log P) =
              (superFiber super g).sum (fun s => (P * Q s) * Real.log P) := by
                apply Finset.sum_congr rfl
                intro s hs
                ring
          _ = ((superFiber super g).sum (fun s => P * Q s)) * Real.log P := by
                rw [Finset.sum_mul]
          _ = (P * (superFiber super g).sum Q) * Real.log P := by
                rw [Finset.mul_sum]
          _ = P * Real.log P * (superFiber super g).sum Q := by ring]
  rw [hQsum]
  rw [show (superFiber super g).sum (fun s =>
      P * Q s * Real.log (Q s)) =
      P * (superFiber super g).sum (fun s => Q s * Real.log (Q s)) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        ring]
  rw [hcondsum]
  simp [P, Q, fiberEntropy]
  ring

/-- Full hierarchical entropy decomposes into outer, fiber, and conditional
    contributions on the dependent Gibbs tower. -/
theorem layeredEntropy_eq_outerEntropy_add_fiberEntropy_add_conditionalEntropy
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty) :
    layeredEntropy State super energy particleNumber superNumber β μ ν =
      outerEntropy State super energy particleNumber superNumber β μ ν +
        (∑ g, outerWeight State super energy particleNumber superNumber β μ ν g *
          fiberEntropy State super energy particleNumber β μ g) +
        (∑ g, outerWeight State super energy particleNumber superNumber β μ ν g *
          (superFiber super g).sum (fun s =>
            fiberSectorWeight State super energy particleNumber β μ g s *
              conditionalEntropy State energy β s)) := by
  classical
  calc
    layeredEntropy State super energy particleNumber superNumber β μ ν =
        ∑ g, (superFiber super g).sum (fun s =>
          finiteEntropy (fun x =>
            layeredJointWeight State super energy particleNumber superNumber β μ ν g s x)) := by
          unfold layeredEntropy finiteEntropy
          simp_rw [Finset.sum_neg_distrib]
    _ = ∑ g, (outerWeight State super energy particleNumber superNumber β μ ν g *
          fiberEntropy State super energy particleNumber β μ g +
        outerWeight State super energy particleNumber superNumber β μ ν g *
          (superFiber super g).sum (fun s =>
            fiberSectorWeight State super energy particleNumber β μ g s *
              conditionalEntropy State energy β s) -
        outerWeight State super energy particleNumber superNumber β μ ν g *
          Real.log (outerWeight State super energy particleNumber superNumber β μ ν g)) := by
          apply Finset.sum_congr rfl
          intro g hg
          exact sum_finiteEntropy_layeredJointWeight_over_sector_eq State super energy
            particleNumber superNumber β μ ν fiber_nonempty g
    _ = outerEntropy State super energy particleNumber superNumber β μ ν +
        (∑ g, outerWeight State super energy particleNumber superNumber β μ ν g *
          fiberEntropy State super energy particleNumber β μ g) +
        (∑ g, outerWeight State super energy particleNumber superNumber β μ ν g *
          (superFiber super g).sum (fun s =>
            fiberSectorWeight State super energy particleNumber β μ g s *
              conditionalEntropy State energy β s)) := by
          unfold outerEntropy finiteEntropy
          simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
          ring

/-- The product-form three-level joint weight normalizes. -/
theorem sum_layeredJointWeight_eq_one
    (super : Sector → SuperSector)
    (energy : ∀ s, State s → ℝ) (particleNumber : Sector → ℝ)
    (superNumber : SuperSector → ℝ) (β μ ν : ℝ)
    (fiber_nonempty : ∀ g, (superFiber super g).Nonempty) :
    (∑ g, (superFiber super g).sum (fun s => ∑ x,
      layeredJointWeight State super energy particleNumber superNumber β μ ν g s x)) = 1 := by
  classical
  unfold layeredJointWeight
  have hinner :
      ∀ g s,
        ∑ x, outerWeight State super energy particleNumber superNumber β μ ν g *
          fiberSectorWeight State super energy particleNumber β μ g s *
          conditionalWeight State energy β s x =
          outerWeight State super energy particleNumber superNumber β μ ν g *
            fiberSectorWeight State super energy particleNumber β μ g s := by
    intro g s
    calc
      ∑ x, outerWeight State super energy particleNumber superNumber β μ ν g *
          fiberSectorWeight State super energy particleNumber β μ g s *
          conditionalWeight State energy β s x
          =
          ∑ x, conditionalWeight State energy β s x *
            (outerWeight State super energy particleNumber superNumber β μ ν g *
              fiberSectorWeight State super energy particleNumber β μ g s) := by
              apply Finset.sum_congr rfl
              intro x hx
              ring
      _ = (∑ x, conditionalWeight State energy β s x) *
          (outerWeight State super energy particleNumber superNumber β μ ν g *
            fiberSectorWeight State super energy particleNumber β μ g s) := by
              rw [Finset.sum_mul]
      _ = outerWeight State super energy particleNumber superNumber β μ ν g *
            fiberSectorWeight State super energy particleNumber β μ g s := by
              rw [sum_conditionalWeight_eq_one State energy β s]
              ring
  calc
    (∑ g, (superFiber super g).sum (fun s => ∑ x,
      layeredJointWeight State super energy particleNumber superNumber β μ ν g s x)) =
        ∑ g, (superFiber super g).sum (fun s =>
          outerWeight State super energy particleNumber superNumber β μ ν g *
            fiberSectorWeight State super energy particleNumber β μ g s) := by
          apply Finset.sum_congr rfl
          intro g hg
          apply Finset.sum_congr rfl
          intro s hs
          exact hinner g s
    _ = ∑ g, outerWeight State super energy particleNumber superNumber β μ ν g *
          (superFiber super g).sum (fun s =>
            fiberSectorWeight State super energy particleNumber β μ g s) := by
          simp_rw [Finset.mul_sum]
    _ = ∑ g, outerWeight State super energy particleNumber superNumber β μ ν g := by
          apply Finset.sum_congr rfl
          intro g hg
          rw [sum_fiberSectorWeight_eq_one State super energy particleNumber β μ
            fiber_nonempty g]
          ring
    _ = 1 := by
          exact sum_outerWeight_eq_one State super energy particleNumber superNumber β μ ν
            fiber_nonempty

end ThreeLevelFiniteGibbs

end InfoGeometry.Canonical
