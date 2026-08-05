import Mathlib
import InfoGeometry.Canonical.PoissonGibbsKANModuliCertificateTopological

/-!
# TopCat readouts for the continuous Poisson Gibbs certificate

The canonical KAN-moduli owner already proves continuity and positivity of
the finite coupling and its marginal targets.  This file exposes those
readouts as morphisms in `TopCat` without adding an optimization claim.
-/

namespace InfoGeometry.Topology.PoissonGibbsCertificateTopCat

noncomputable section

open InfoGeometry.Canonical.KANModuli
open InfoGeometry.Inference

variable {Data : Type*} {Theta : Type} [Fintype Data] [Nonempty Data]
  [TopologicalSpace Theta]

def couplingReadoutTopCatHom
    {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (ε : NonzeroTemperature) (i : Data) (k : Fin K) :
    TopCat.of (KANModuliSpace Theta K) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun q =>
        (poissonGibbsTransportCertificateOnModuli M ε q).coupling i k
      continuous_toFun :=
        continuous_poissonGibbsCertificate_coupling M hmean ε i k }

@[simp] theorem couplingReadoutTopCatHom_apply
    {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (ε : NonzeroTemperature) (i : Data) (k : Fin K)
    (q : KANModuliSpace Theta K) :
    couplingReadoutTopCatHom M hmean ε i k q =
      (poissonGibbsTransportCertificateOnModuli M ε q).coupling i k :=
  rfl

def rowTargetReadoutTopCatHom
    {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (ε : NonzeroTemperature) (i : Data) :
    TopCat.of (KANModuliSpace Theta K) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun q =>
        (poissonGibbsTransportCertificateOnModuli M ε q).targetRowMass i
      continuous_toFun :=
        continuous_poissonGibbsCertificate_rowTarget M hmean ε i }

@[simp] theorem rowTargetReadoutTopCatHom_apply
    {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (ε : NonzeroTemperature) (i : Data)
    (q : KANModuliSpace Theta K) :
    rowTargetReadoutTopCatHom M hmean ε i q =
    (poissonGibbsTransportCertificateOnModuli M ε q).targetRowMass i :=
  rfl

def colTargetReadoutTopCatHom
    {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (ε : NonzeroTemperature) (k : Fin K) :
    TopCat.of (KANModuliSpace Theta K) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun q =>
        (poissonGibbsTransportCertificateOnModuli M ε q).targetColMass k
      continuous_toFun :=
        continuous_poissonGibbsCertificate_colTarget M ε k }

@[simp] theorem colTargetReadoutTopCatHom_apply
    {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (ε : NonzeroTemperature) (k : Fin K)
    (q : KANModuliSpace Theta K) :
    colTargetReadoutTopCatHom M ε k q =
      (poissonGibbsTransportCertificateOnModuli M ε q).targetColMass k :=
  rfl

theorem couplingReadoutTopCatHom_nonnegative
    {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (ε : NonzeroTemperature) (q : KANModuliSpace Theta K)
    (i : Data) (k : Fin K) :
    0 ≤ couplingReadoutTopCatHom M hmean ε i k q := by
  exact (poissonGibbsTransportCertificateOnModuli M ε q).coupling_nonneg i k

theorem rowTargetReadoutTopCatHom_pos
    {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (hmean : ∀ i, Continuous (fun θ => M.mean i θ))
    (ε : NonzeroTemperature) (q : KANModuliSpace Theta K) (i : Data) :
    0 < rowTargetReadoutTopCatHom M hmean ε i q := by
  exact (poissonGibbsTransportCertificateOnModuli M ε q).target_row_mass_pos i

theorem colTargetReadoutTopCatHom_pos
    {K : ℕ} [NeZero K]
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (ε : NonzeroTemperature) (q : KANModuliSpace Theta K) (k : Fin K) :
    0 < colTargetReadoutTopCatHom M ε k q := by
  exact (poissonGibbsTransportCertificateOnModuli M ε q).target_col_mass_pos k

end
end InfoGeometry.Topology.PoissonGibbsCertificateTopCat
