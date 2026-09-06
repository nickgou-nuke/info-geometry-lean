import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.Data.ZMod.Units

namespace InfoGeometry.Arithmetic

noncomputable section

/-- Restriction on cyclotomic Galois labels, induced by reduction modulo a divisor. -/
def cyclotomicGaloisRestrictionUnits
    {N M : ℕ} (hNM : N ∣ M) :
    (ZMod M)ˣ →* (ZMod N)ˣ :=
  ZMod.unitsMap hNM

@[simp] theorem cyclotomicGaloisRestrictionUnits_apply
    {N M : ℕ} (hNM : N ∣ M) (u : (ZMod M)ˣ) :
    cyclotomicGaloisRestrictionUnits hNM u = ZMod.unitsMap hNM u := rfl

end
end InfoGeometry.Arithmetic
