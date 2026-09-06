import InfoGeometry.Canonical.DyadicScalarActionLaws

namespace InfoGeometry.Canonical

/-!
# Transported multiplication on the dyadic direct-limit carrier

`DyadicDirectLimit` already has its additive and topological structures.  This
owner exposes the multiplicative readout transported from `DyadicRational`.
It deliberately does not install a new `Ring` instance on the quotient
carrier: the operation is an explicit, reusable topological readout.
-/

noncomputable def dyadicDirectLimitMul
    (x y : DyadicDirectLimit) : DyadicDirectLimit :=
  dyadicDirectLimitEquiv.symm
    (dyadicScalarMul (dyadicDirectLimitEquiv x) (dyadicDirectLimitEquiv y))

noncomputable def dyadicDirectLimitOne : DyadicDirectLimit :=
  dyadicDirectLimitEquiv.symm dyadicOne

theorem dyadicDirectLimitMul_one (x : DyadicDirectLimit) :
    dyadicDirectLimitMul x dyadicDirectLimitOne = x := by
  apply dyadicDirectLimitEquiv.injective
  simp [dyadicDirectLimitMul, dyadicDirectLimitOne, dyadicScalarMul]

theorem dyadicDirectLimit_one_mul (x : DyadicDirectLimit) :
    dyadicDirectLimitMul dyadicDirectLimitOne x = x := by
  apply dyadicDirectLimitEquiv.injective
  simp [dyadicDirectLimitMul, dyadicDirectLimitOne, dyadicScalarMul]

theorem dyadicDirectLimitEquiv_mul
    (x y : DyadicDirectLimit) :
    dyadicDirectLimitEquiv (dyadicDirectLimitMul x y) =
      dyadicScalarMul (dyadicDirectLimitEquiv x) (dyadicDirectLimitEquiv y) := by
  simp [dyadicDirectLimitMul]

theorem continuous_dyadicDirectLimitMul :
    Continuous (fun p : DyadicDirectLimit × DyadicDirectLimit =>
      dyadicDirectLimitMul p.1 p.2) := by
  apply continuous_induced_rng.mpr
  have hpair : Continuous
      (fun p : DyadicDirectLimit × DyadicDirectLimit =>
        (dyadicDirectLimitEquiv p.1, dyadicDirectLimitEquiv p.2)) := by
    exact (continuous_dyadicDirectLimitEquiv.comp continuous_fst).prodMk
      (continuous_dyadicDirectLimitEquiv.comp continuous_snd)
  simpa [Function.comp_def, dyadicDirectLimitMul] using
    continuous_dyadicScalarMul.comp hpair

theorem dyadicDirectLimitMul_assoc
    (x y z : DyadicDirectLimit) :
    dyadicDirectLimitMul (dyadicDirectLimitMul x y) z =
      dyadicDirectLimitMul x (dyadicDirectLimitMul y z) := by
  apply dyadicDirectLimitEquiv.injective
  calc
    dyadicDirectLimitEquiv (dyadicDirectLimitMul (dyadicDirectLimitMul x y) z) =
        dyadicScalarMul
          (dyadicDirectLimitEquiv (dyadicDirectLimitMul x y))
          (dyadicDirectLimitEquiv z) :=
      dyadicDirectLimitEquiv_mul (dyadicDirectLimitMul x y) z
    _ = dyadicScalarMul
          (dyadicScalarMul (dyadicDirectLimitEquiv x)
            (dyadicDirectLimitEquiv y))
          (dyadicDirectLimitEquiv z) := by
      rw [dyadicDirectLimitEquiv_mul]
    _ = dyadicScalarMul (dyadicDirectLimitEquiv x)
          (dyadicScalarMul (dyadicDirectLimitEquiv y)
            (dyadicDirectLimitEquiv z)) :=
      (dyadicScalarMul_assoc
        (dyadicDirectLimitEquiv x)
        (dyadicDirectLimitEquiv y)
        (dyadicDirectLimitEquiv z)).symm
    _ = dyadicScalarMul (dyadicDirectLimitEquiv x)
          (dyadicDirectLimitEquiv (dyadicDirectLimitMul y z)) := by
      rw [dyadicDirectLimitEquiv_mul]
    _ = dyadicDirectLimitEquiv
          (dyadicDirectLimitMul x (dyadicDirectLimitMul y z)) :=
      (dyadicDirectLimitEquiv_mul x (dyadicDirectLimitMul y z)).symm

theorem dyadicDirectLimitMul_comm
    (x y : DyadicDirectLimit) :
    dyadicDirectLimitMul x y = dyadicDirectLimitMul y x := by
  apply dyadicDirectLimitEquiv.injective
  rw [dyadicDirectLimitEquiv_mul, dyadicDirectLimitEquiv_mul]
  apply Subtype.ext
  simp [dyadicScalarMul]
  ring

theorem dyadicDirectLimitMul_add_left
    (x y z : DyadicDirectLimit) :
    dyadicDirectLimitMul (x + y) z =
      dyadicDirectLimitMul x z + dyadicDirectLimitMul y z := by
  apply dyadicDirectLimitEquiv.injective
  calc
    dyadicDirectLimitEquiv (dyadicDirectLimitMul (x + y) z) =
        dyadicScalarMul (dyadicDirectLimitEquiv (x + y))
          (dyadicDirectLimitEquiv z) :=
      dyadicDirectLimitEquiv_mul (x + y) z
    _ = dyadicScalarMul
          (dyadicDirectLimitEquiv x + dyadicDirectLimitEquiv y)
          (dyadicDirectLimitEquiv z) := by
      rw [dyadicDirectLimitEquiv_add]
    _ = dyadicScalarMul (dyadicDirectLimitEquiv x)
          (dyadicDirectLimitEquiv z) +
        dyadicScalarMul (dyadicDirectLimitEquiv y)
          (dyadicDirectLimitEquiv z) :=
      dyadicScalarMul_add_left
        (dyadicDirectLimitEquiv x)
        (dyadicDirectLimitEquiv y)
        (dyadicDirectLimitEquiv z)
    _ = dyadicDirectLimitEquiv (dyadicDirectLimitMul x z) +
        dyadicDirectLimitEquiv (dyadicDirectLimitMul y z) := by
      rw [dyadicDirectLimitEquiv_mul, dyadicDirectLimitEquiv_mul]
    _ = dyadicDirectLimitEquiv
        (dyadicDirectLimitMul x z + dyadicDirectLimitMul y z) := by
      rw [dyadicDirectLimitEquiv_add]

theorem dyadicDirectLimitMul_add_right
    (x y z : DyadicDirectLimit) :
    dyadicDirectLimitMul x (y + z) =
      dyadicDirectLimitMul x y + dyadicDirectLimitMul x z := by
  apply dyadicDirectLimitEquiv.injective
  calc
    dyadicDirectLimitEquiv (dyadicDirectLimitMul x (y + z)) =
        dyadicScalarMul (dyadicDirectLimitEquiv x)
          (dyadicDirectLimitEquiv (y + z)) :=
      dyadicDirectLimitEquiv_mul x (y + z)
    _ = dyadicScalarMul (dyadicDirectLimitEquiv x)
          (dyadicDirectLimitEquiv y + dyadicDirectLimitEquiv z) := by
      rw [dyadicDirectLimitEquiv_add]
    _ = dyadicScalarMul (dyadicDirectLimitEquiv x)
          (dyadicDirectLimitEquiv y) +
        dyadicScalarMul (dyadicDirectLimitEquiv x)
          (dyadicDirectLimitEquiv z) :=
      dyadicScalarMul_add_right
        (dyadicDirectLimitEquiv x)
        (dyadicDirectLimitEquiv y)
        (dyadicDirectLimitEquiv z)
    _ = dyadicDirectLimitEquiv (dyadicDirectLimitMul x y) +
        dyadicDirectLimitEquiv (dyadicDirectLimitMul x z) := by
      rw [dyadicDirectLimitEquiv_mul, dyadicDirectLimitEquiv_mul]
    _ = dyadicDirectLimitEquiv
        (dyadicDirectLimitMul x y + dyadicDirectLimitMul x z) := by
      rw [dyadicDirectLimitEquiv_add]

end InfoGeometry.Canonical
