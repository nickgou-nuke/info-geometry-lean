import sys

with open('lean/InfoGeometry/Canonical/VirasoroProjectColimitBridge.lean', 'r') as f:
    text = f.read()

# 1. AddCommGroup V
text = text.replace('variable {V : Type} [AddGroup V] [Module 𝕂 V]', 'variable {V : Type} [AddCommGroup V] [Module 𝕂 V]')

# 2. AddCommGroup W
text = text.replace('SeminormedAddGroup', 'NormedAddCommGroup')

# 3. virasoroG n J ψ -> virasoroG n r J ψ or (fun s => virasoroG n s J ψ)
text = text.replace('virasoroG n J ψ', '(fun s => virasoroG n s J ψ)')
# Wait, let's fix the ones we messed up with replace: we want `(fun s => virasoroG n s J ψ)` for the mixedBracketLaw parameter.
# The text currently has:
# KVirasoroDatum.mixedBracketLaw (kVirasoroDatumAtStage n J ψ) m r (virasoroG n J ψ)
text = text.replace('m r (virasoroG n J ψ)', 'm r (fun s => virasoroG n s J ψ)')
text = text.replace('φ (virasoroG n r J ψ)⁆', 'φ (virasoroG n r J ψ)⁆') # Wait, this one was:
text = text.replace('⁅φ (kVirasoroDatumAtStage n J ψ |mode m), φ (virasoroG n r J ψ)⁆', '⁅φ ((kVirasoroDatumAtStage n J ψ).Lmode m), φ (virasoroG n r J ψ)⁆')

text = text.replace('|mode m', '.Lmode m')
text = text.replace('ψ).Lmode m', 'ψ).Lmode m') # If we just replaced, let's make sure parenthesis are right
text = text.replace('⁅realVirasoroDatumAtStage n J ψ .Lmode m', '⁅(realVirasoroDatumAtStage n J ψ).Lmode m')
text = text.replace('⁅φ (realVirasoroDatumAtStage n J ψ .Lmode m)', '⁅φ ((realVirasoroDatumAtStage n J ψ).Lmode m)')

# 4. bond definition
text = text.replace('def bond (n : ℕ) : EndV →+* EndV := RingHom.id EndV', 'def bond {𝕂 : Type*} [Field 𝕂] {V : Type*} [AddCommGroup V] [Module 𝕂 V] (n : ℕ) : Module.End 𝕂 V →+* Module.End 𝕂 V := RingHom.id (Module.End 𝕂 V)')

# 5. LG_coeff type coercion
text = text.replace('(LG_coeff m r) •', '(LG_coeff m r : ℝ) •')

# 6. constructor -> refine
text = text.replace('      φ (boundaryDefect_LG (𝕜 := 𝕂) (Int.ofNat n) m r J ψ) = 0) := by\n  constructor', '      φ (boundaryDefect_LG (𝕜 := 𝕂) (Int.ofNat n) m r J ψ) = 0) := by\n  refine ⟨?_, ?_, ?_⟩')

# 7. unused n
text = text.replace('def sugawaraDatumAtStage (n : ℕ) : SugawaraDatum where', 'def sugawaraDatumAtStage (_n : ℕ) : SugawaraDatum where')
text = text.replace('theorem sugawaraDatumAtStage_calibration (n : ℕ) :', 'theorem sugawaraDatumAtStage_calibration (_n : ℕ) :')
text = text.replace('sugawaraDatumAtStage n', 'sugawaraDatumAtStage _n')

# 8. centralCoefficient missing type
text = text.replace('centralCoefficient m n •', '(centralCoefficient m n : 𝕂) •')

with open('lean/InfoGeometry/Canonical/VirasoroProjectColimitBridge.lean', 'w') as f:
    f.write(text)
