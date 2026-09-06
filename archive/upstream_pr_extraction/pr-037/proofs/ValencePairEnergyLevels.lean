import proofs.HamiltonianCoriolisLieDynamics

/-!
# Valence-pair energy levels

Finite spectroscopy layer for modeling valence proton/neutron pair states with
the Goutev--Tonev Hamiltonian.  The model is intentionally small:

* each valence lane receives a Hamiltonian energy;
* a pair energy is the sum of the two lane energies minus a pairing binding;
* two competing pair configurations mix through the Coriolis/Lie-flow
  off-diagonal term already formalized in `HamiltonianCoriolisLieDynamics`.

This gives a concrete finite model for mirror-nucleus style level splitting and
avoided crossings.
-/

noncomputable section

namespace ValencePairEnergyLevels

open Matrix

/-- Minimal valence kind labels. -/
inductive ValenceKind where
  | proton
  | neutron
  deriving DecidableEq, Repr

/-- Coulomb/isospin offset assigned to one valence kind. -/
def valenceOffset (coulombShift : ℝ) : ValenceKind → ℝ
  | .proton => coulombShift
  | .neutron => 0

@[simp] theorem valenceOffset_proton (coulombShift : ℝ) :
    valenceOffset coulombShift ValenceKind.proton = coulombShift := rfl

@[simp] theorem valenceOffset_neutron (coulombShift : ℝ) :
    valenceOffset coulombShift ValenceKind.neutron = 0 := rfl

theorem valenceOffset_proton_sub_neutron (coulombShift : ℝ) :
    valenceOffset coulombShift ValenceKind.proton -
      valenceOffset coulombShift ValenceKind.neutron =
        coulombShift := by
  rw [valenceOffset_proton, valenceOffset_neutron]
  ring

/-- Pair channel labels. -/
inductive PairChannel where
  | pp
  | nn
  | pn
  deriving DecidableEq, Repr

/-- Pairing channel from two valence kinds. -/
def pairChannel : ValenceKind → ValenceKind → PairChannel
  | .proton, .proton => .pp
  | .neutron, .neutron => .nn
  | _, _ => .pn

/-- Pair energy: two lane energies plus offsets minus pairing binding. -/
def pairEnergy
    (E₁ E₂ pairingBinding offset₁ offset₂ : ℝ) : ℝ :=
  (E₁ + offset₁) + (E₂ + offset₂) - pairingBinding

theorem pairEnergy_exchange
    (E₁ E₂ pairingBinding offset₁ offset₂ : ℝ) :
    pairEnergy E₁ E₂ pairingBinding offset₁ offset₂ =
      pairEnergy E₂ E₁ pairingBinding offset₂ offset₁ := by
  unfold pairEnergy
  ring

@[simp] theorem pairChannel_pn_exchange :
    pairChannel ValenceKind.proton ValenceKind.neutron =
      pairChannel ValenceKind.neutron ValenceKind.proton := rfl

@[simp] theorem pairChannel_proton_neutron :
    pairChannel ValenceKind.proton ValenceKind.neutron = PairChannel.pn := rfl

@[simp] theorem pairChannel_neutron_proton :
    pairChannel ValenceKind.neutron ValenceKind.proton = PairChannel.pn := rfl

/-- Two-level pair-mixing Hamiltonian. -/
def pairMixingHamiltonian (Epair₁ Epair₂ flow : ℝ) :
    HamiltonianCoriolisLieDynamics.M2C :=
  HamiltonianCoriolisLieDynamics.twoLevelHamiltonian Epair₁ Epair₂ flow

@[simp] theorem pairMixing_trace (Epair₁ Epair₂ flow : ℝ) :
    Matrix.trace (pairMixingHamiltonian Epair₁ Epair₂ flow) =
      (Epair₁ + Epair₂ : ℂ) := by
  simp [pairMixingHamiltonian]

end ValencePairEnergyLevels
