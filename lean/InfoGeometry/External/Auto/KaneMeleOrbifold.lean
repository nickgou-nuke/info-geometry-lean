namespace KaneMeleOrbifold

/-- An abstract two-state label for a Kane--Mele-style phase.

This is only a finite label.  It is not a band-topology invariant until a
separate model supplies the relevant Bloch bundle and time-reversal data. -/
inductive KaneMeleLabel
| trivial
| nontrivial

/-- An abstract parity label, with no identification with a Pin group. -/
inductive AbstractParity
| even
| odd

/-- Chosen finite encoding of the two phase labels as abstract parity. -/
def kaneMeleParity : KaneMeleLabel → AbstractParity
| KaneMeleLabel.trivial => AbstractParity.even
| KaneMeleLabel.nontrivial => AbstractParity.odd

@[simp] theorem kaneMeleParity_trivial :
    kaneMeleParity KaneMeleLabel.trivial = AbstractParity.even := rfl

@[simp] theorem kaneMeleParity_nontrivial :
    kaneMeleParity KaneMeleLabel.nontrivial = AbstractParity.odd := rfl

/-! No theorem here identifies this encoding with actual band topology,
Pin(5,5), orientability, or an anomaly invariant. -/

end KaneMeleOrbifold
