import proofs.BoltzmannLnQTensorFlowToy

/-!
# ³¹P/³¹S mirror ln(Q) flow toy

Finite digest for `proofs/mirror31_ps_lnq_flow.py`.

The external script specializes the ln(Q) complete-graph Boltzmann-flow idea to
the mirror pair

```text
³¹P : Z = 15, N = 16, A = 31, 2Tz = +1
³¹S : Z = 16, N = 15, A = 31, 2Tz = -1
```

It avoids dense enumeration of the `2^31` state space by evolving a finite
mean-field vector field and storing the final factorized probability amplitude
as a rank-1 quantics tensor train with 31 binary cores using `trainsum`.

Lean records only the exact finite nuclear bookkeeping and tensor-shape data.
-/

namespace Mirror31PSLnQFlowToy

/-- Mass number of the mirror pair. -/
def A31 : ℕ := 31

/-- Proton and neutron counts. -/
def P31_Z : ℕ := 15

def P31_N : ℕ := 16

def S31_Z : ℕ := 16

def S31_N : ℕ := 15

/-- Twice the isospin projection `2Tz = N-Z`, represented over integers. -/
def P31_twoTz : ℤ := 1

def S31_twoTz : ℤ := -1

/-- Complete graph edge count for 31 coarse nodes. -/
def completeEdges31 : ℕ := A31 * (A31 - 1) / 2

/-- Dense state-count exponent; the full count would be `2^31`. -/
def stateCountLog2 : ℕ := 31

/-- Full binary configuration count. -/
def stateCount31 : ℕ := 2 ^ stateCountLog2

/-- Rank-one quantics tensor train has one binary core per node. -/
def qttCoreCount31 : ℕ := 31

/-- Number of two-state Q table entries. -/
def qTableEntries31 : ℕ := 31 * 2

/-- Number of Euler steps in the external mean-field run. -/
def mirrorFlowSteps : ℕ := 20

/-- Coulomb pair count `Z choose 2`. -/
def choose2 (n : ℕ) : ℕ := n * (n - 1) / 2

@[simp] theorem P31_mass_number : P31_Z + P31_N = A31 := rfl

@[simp] theorem S31_mass_number : S31_Z + S31_N = A31 := rfl

@[simp] theorem mirror_twoTz_sum_zero : P31_twoTz + S31_twoTz = 0 := rfl

@[simp] theorem complete_edges31_eq : completeEdges31 = 465 := rfl

@[simp] theorem state_count_log2_eq : stateCountLog2 = 31 := rfl

@[simp] theorem qtt_core_count31_eq : qttCoreCount31 = 31 := rfl

@[simp] theorem q_table_entries31_eq : qTableEntries31 = 62 := rfl

@[simp] theorem mirror_flow_steps_eq : mirrorFlowSteps = 20 := rfl

@[simp] theorem P31_coulomb_pairs : choose2 P31_Z = 105 := rfl

@[simp] theorem S31_coulomb_pairs : choose2 S31_Z = 120 := rfl

@[simp] theorem coulomb_pair_delta_S_minus_P : choose2 S31_Z - choose2 P31_Z = 15 := rfl

/-- Mirror labels. -/
inductive Mirror31Nucleus where
  | P31
  | S31
  deriving DecidableEq, Repr

/-- Coarse node kind in the external toy. -/
inductive CoarseNucleonNode where
  | protonLike
  | neutronLike
  deriving DecidableEq, Repr

/-- Flow observables emitted by the external run. -/
inductive MirrorFlowObservable where
  | thetaNorm
  | meanMagnetization
  | entropySum
  | expectedLnQMean
  | coulombPairCount
  deriving DecidableEq, Repr

/-- Observable inventory. -/
def mirrorFlowObservables : List MirrorFlowObservable :=
  [.thetaNorm, .meanMagnetization, .entropySum, .expectedLnQMean, .coulombPairCount]

@[simp] theorem mirror_flow_observable_count : mirrorFlowObservables.length = 5 := rfl

/-- Capstone: exact mirror-pair bookkeeping compiles. -/
theorem mirror31_ps_lnq_flow_toy_synthesis :
    P31_Z + P31_N = A31 ∧
    S31_Z + S31_N = A31 ∧
    P31_twoTz + S31_twoTz = 0 ∧
    completeEdges31 = 465 ∧
    stateCountLog2 = 31 ∧
    qttCoreCount31 = 31 ∧
    qTableEntries31 = 62 ∧
    mirrorFlowSteps = 20 ∧
    choose2 P31_Z = 105 ∧
    choose2 S31_Z = 120 ∧
    choose2 S31_Z - choose2 P31_Z = 15 ∧
    mirrorFlowObservables.length = 5 ∧
    QuaternionQuanticsBackendDigest.quanticsFullDimension 2 31 = stateCount31 := by
  norm_num [A31, P31_Z, P31_N, S31_Z, S31_N, P31_twoTz, S31_twoTz,
    completeEdges31, stateCountLog2, qttCoreCount31, qTableEntries31,
    mirrorFlowSteps, choose2, mirrorFlowObservables, stateCount31,
    QuaternionQuanticsBackendDigest.quanticsFullDimension]

end Mirror31PSLnQFlowToy
