# Proof Gap Report

Generated: `2026-06-27 18:58:17`

This report lists unfinished or assumed formal statements (`sorry` and `axiom`) to support clean canonical reimplementation.

- Total gaps: **27**
- Files with gaps: **7**
- Files with `noncomputable`: **0**

## `InfoGeometry/Clifford/SORRIES/CliffordInjectivity.lean`

- L173: `sorry` in `theorem incl_Cl_split_injective` (decl starts L159)
  - Natural language: Unfinished proof for `incl_Cl_split_injective` (incl Cl split injective).
  - Source head: `theorem incl_Cl_split_injective (n : ℕ) : Function.Injective (incl_Cl_split n) := by`

## `InfoGeometry/Eval/ClosureDebtTest.lean`

- L19: `sorry` in `structure TestBridge` (decl starts L16)
  - Natural language: Unfinished proof for `TestBridge` (TestBridge).
  - Source head: `structure TestBridge where`
- L29: `sorry` in `structure TestData` (decl starts L25)
  - Natural language: Unfinished proof for `TestData` (TestData).
  - Source head: `structure TestData where`
- L35: `sorry` in `structure TestCertificate` (decl starts L32)
  - Natural language: Unfinished proof for `TestCertificate` (TestCertificate).
  - Source head: `structure TestCertificate where`
- L41: `sorry` in `structure TestValid` (decl starts L38)
  - Natural language: Unfinished proof for `TestValid` (TestValid).
  - Source head: `structure TestValid where`
- L47: `sorry` in `structure TestWitness` (decl starts L44)
  - Natural language: Unfinished proof for `TestWitness` (TestWitness).
  - Source head: `structure TestWitness where`
- L53: `sorry` in `structure TestBridge2` (decl starts L50)
  - Natural language: Unfinished proof for `TestBridge2` (TestBridge2).
  - Source head: `structure TestBridge2 where`

## `InfoGeometry/Lint/Pauli.lean`

- L12: `sorry` (no declaration context)
- L51: `sorry` in `def pauliLinter` (decl starts L48)
  - Natural language: Unfinished proof for `pauliLinter` (pauliLinter).
  - Source head: `def pauliLinter : Linter where`
- L92: `sorry` in `def pauliLinter` (decl starts L48)
  - Natural language: Unfinished proof for `pauliLinter` (pauliLinter).
  - Source head: `def pauliLinter : Linter where`

## `InfoGeometry/Spectral/Cohomology/Basic.lean`

- L32: `sorry` in `def cohomology` (decl starts L31)
  - Natural language: Unfinished proof for `cohomology` (cohomology).
  - Source head: `def cohomology (X : Type*) (Y : Spectrum) (n : ℤ) : AddCommGroup :=`

## `InfoGeometry/Spectral/Cohomology/Gysin.lean`

- L36: `sorry` in `def gysin_trivial_Epage` (decl starts L33)
  - Natural language: Unfinished proof for `gysin_trivial_Epage` (gysin trivial Epage).
  - Source head: `def gysin_trivial_Epage {E B : Type*} {n : ℕ} (HB : IsConnected 1 B) (f : E →* B)`
- L40: `sorry` in `def gysin_trivial_Epage2` (decl starts L38)
  - Natural language: Unfinished proof for `gysin_trivial_Epage2` (gysin trivial Epage2).
  - Source head: `def gysin_trivial_Epage2 {E B : Type*} {n : ℕ} (HB : IsConnected 1 B) (f : E →* B)`
- L43: `sorry` in `def gysin_sequence'` (decl starts L42)
  - Natural language: Unfinished proof for `gysin_sequence'` (gysin sequence').
  - Source head: `def gysin_sequence' {E B : Type*} {n : ℕ} (HB : IsConnected 1 B) (f : E →* B)`
- L47: `sorry` in `def gysin_sequence'_zero` (decl starts L45)
  - Natural language: Unfinished proof for `gysin_sequence'_zero` (gysin sequence' zero).
  - Source head: `def gysin_sequence'_zero {E B : Type*} {n : ℕ} (HB : IsConnected 1 B) (f : E →* B)`
- L51: `sorry` in `def gysin_sequence'_one` (decl starts L49)
  - Natural language: Unfinished proof for `gysin_sequence'_one` (gysin sequence' one).
  - Source head: `def gysin_sequence'_one {E B : Type*} {n : ℕ} (HB : IsConnected 1 B) (f : E →* B)`
- L55: `sorry` in `def gysin` (decl starts L53)
  - Natural language: Unfinished proof for `gysin` (gysin).
  - Source head: `def gysin gysin_sequence'_two {E B : Type*} {n : ℕ} (HB : IsConnected 1 B) (f : E →* B)`

## `InfoGeometry/Spectral/Cohomology/Serre.lean`

- L24: `sorry` in `def serre_spectral_sequence` (decl starts L23)
  - Natural language: Unfinished proof for `serre_spectral_sequence` (serre spectral sequence).
  - Source head: `def serre_spectral_sequence {B E : Type*} (f : E →* B) (F : Type*) (Y : Spectrum) (s₀ : ℤ) :`
- L32: `sorry` in `def gysin_sequence` (decl starts L31)
  - Natural language: Unfinished proof for `gysin_sequence` (gysin sequence).
  - Source head: `def gysin_sequence {B E : Type*} (n : ℕ) (f : E →* B) (e : Fiber f ≃* Sphere (n+1)) (A : AddCommGroup) :`

## `InfoGeometry/Spectral/HigherGroups/Basic.lean`

- L96: `sorry` in `def GType_equiv` (decl starts L92)
  - Natural language: Unfinished proof for `GType_equiv` (GType equiv).
  - Source head: `def GType_equiv (n k : ℕ) : GType n k ≃ (n + k)-Type*[k - 1] := by`
- L176: `sorry` in `def DecatAdjointDisc` (decl starts L175)
  - Natural language: Unfinished proof for `DecatAdjointDisc` (DecatAdjointDisc).
  - Source head: `def DecatAdjointDisc {n k : ℕ} (G : GType (n + 1) k) (H : GType n k) :`
- L182: `sorry` in `def DecatAdjointDiscNatural` (decl starts L178)
  - Natural language: Unfinished proof for `DecatAdjointDiscNatural` (DecatAdjointDiscNatural).
  - Source head: `def DecatAdjointDiscNatural {n k : ℕ} {G G' : GType (n + 1) k} {H H' : GType n k}`
- L188: `sorry` in `def DeloopAdjointLoop` (decl starts L187)
  - Natural language: Unfinished proof for `DeloopAdjointLoop` (DeloopAdjointLoop).
  - Source head: `def DeloopAdjointLoop {n k : ℕ} (G : GType n (k + 1)) (H : GType (n + 1) k) :`
- L194: `sorry` in `def DeloopAdjointLoopNatural` (decl starts L190)
  - Natural language: Unfinished proof for `DeloopAdjointLoopNatural` (DeloopAdjointLoopNatural).
  - Source head: `def DeloopAdjointLoopNatural {n k : ℕ} {G G' : GType n (k + 1)} {H H' : GType (n + 1) k}`
- L200: `sorry` in `def StabilizeAdjointForget` (decl starts L199)
  - Natural language: Unfinished proof for `StabilizeAdjointForget` (StabilizeAdjointForget).
  - Source head: `def StabilizeAdjointForget {n k : ℕ} (G : GType n k) (H : GType n (k + 1)) :`
- L206: `sorry` in `def StabilizeAdjointForgetNatural` (decl starts L202)
  - Natural language: Unfinished proof for `StabilizeAdjointForgetNatural` (StabilizeAdjointForgetNatural).
  - Source head: `def StabilizeAdjointForgetNatural {n k : ℕ} {G G' : GType n k} {H H' : GType n (k + 1)}`
- L209: `sorry` in `def StabilizeForget` (decl starts L208)
  - Natural language: Unfinished proof for `StabilizeForget` (StabilizeForget).
  - Source head: `def StabilizeForget {n k : ℕ} (H : k ≥ n + 2) (G : GType n k) :`
