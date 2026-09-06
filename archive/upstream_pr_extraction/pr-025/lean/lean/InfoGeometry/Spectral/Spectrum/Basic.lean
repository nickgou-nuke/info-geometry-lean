1|import Mathlib
2|import InfoGeometry.Canonical.SplitCliffordDirectLimit
3|
4|noncomputable section
5|
6|/-!
7|# Finite split-Clifford spectral readouts
8|
9|This file deliberately avoids claiming a port of HoTT spectra or a
10|spectrification theorem.  It exposes the finite split-Clifford tower as a
11|small prespectrum-style API and records the elementary readouts that are
12|available from the existing kernel-checked split-Clifford direct-limit lane.
13|-/
14|
15|namespace InfoGeometry.Spectral.Spectrum.Basic
16|
17|open InfoGeometry.Canonical.SplitCliffordDirectLimit
18|open InfoGeometry.Canonical.SplitCliffordTensorBridge
19|
20|/-- A minimal one-step prespectrum-style carrier. -/
21|structure Prespectrum where
22|  /-- Stage carrier. -/
23|  space : ℕ → Type
24|  /-- One-step structure map. -/
25|  step : ∀ n, space n → space (n + 1)
26|
27|namespace Prespectrum
28|
29|/-- Construct a prespectrum from a stage family and one-step maps. -/
30|def ofFun (X : ℕ → Type) (f : ∀ n, X n → X (n + 1)) : Prespectrum :=
31|  ⟨X, f⟩
32|
33|@[simp]
34|theorem ofFun_space (X : ℕ → Type) (f : ∀ n, X n → X (n + 1)) :
35|    (Prespectrum.ofFun X f).space = X :=
36|  rfl
37|
38|@[simp]
39|theorem ofFun_step (X : ℕ → Type) (f : ∀ n, X n → X (n + 1)) :
40|    (Prespectrum.ofFun X f).step = f :=
41|  rfl
42|
43|end Prespectrum
44|
45|/-- The existing split `Cl(n,n)` tower as a finite prespectrum-style object. -/
46|def SplitCliffordPrespectrum : Prespectrum :=
47|  Prespectrum.ofFun SplitClNNAlg (fun n x => splitCliffordStep n x)
48|
49|@[simp]
50|theorem SplitCliffordPrespectrum_space (n : ℕ) :
51|    SplitCliffordPrespectrum.space n = SplitClNNAlg n :=
52|  rfl
53|
54|@[simp]
55|theorem SplitCliffordPrespectrum_step (n : ℕ) (x : SplitClNNAlg n) :
56|    SplitCliffordPrespectrum.step n x = splitCliffordStep n x :=
57|  rfl
58|
59|/-- The Bott clock stage eight steps after `n`. -/
60|def bottClockStage (n : ℕ) : ℕ :=
61|  n + 8
62|
63|@[simp]
64|theorem bottClockStage_sub_self (n : ℕ) :
65|    bottClockStage n - n = 8 := by
66|  simp [bottClockStage]
67|
68|theorem bottClockStage_pos (n : ℕ) :
69|    n < bottClockStage n := by
70|  simp [bottClockStage]
71|
72|/-- The zero finite Dirac readout at stage `n`. -/
73|def diracOperator (n : ℕ) : SplitClNNAlg n :=
74|  0
75|
76|@[simp]
77|theorem diracOperator_sq (n : ℕ) :
78|    diracOperator n * diracOperator n = 0 := by
79|  simp [diracOperator]
80|
81|/-- Finite spectral readout for the zero Dirac operator. -/
82|def diracSpectrum (_n : ℕ) : Multiset ℝ :=
83|  {0}
84|
85|@[simp]
86|theorem mem_diracSpectrum_iff (n : ℕ) (lam : ℝ) :
87|    lam ∈ diracSpectrum n ↔ lam = 0 := by
88|  simp [diracSpectrum]
89|
90|@[simp]
91|theorem diracSpectrum_card (n : ℕ) :
92|    (diracSpectrum n).card = 1 := by
93|  simp [diracSpectrum]
94|
95|/-- A finite 8-periodic stable-homotopy readout used as a clock index. -/
96|def stableHomotopyClifford (k : ℕ) : Type :=
97|  Fin ((k % 8) + 1)
98|
99|theorem stableHomotopyClifford_nonempty (k : ℕ) :
100|    Nonempty (stableHomotopyClifford k) :=
101|  ⟨⟨0, Nat.succ_pos (k % 8)⟩⟩
102|
103|@[simp]
104|theorem stableHomotopyClifford_period (k : ℕ) :
105|    stableHomotopyClifford (k + 8) = stableHomotopyClifford k := by
106|  unfold stableHomotopyClifford
107|  rw [Nat.add_mod_right]
108|
109|end InfoGeometry.Spectral.Spectrum.Basic
110|