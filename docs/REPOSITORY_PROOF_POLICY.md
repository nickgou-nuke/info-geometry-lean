# Repository Proof Policy

This repository admits abstract interfaces, local seeds, and conditional adapters.
It does **not** accept global realization claims without explicit data and proofs.

## Hard boundaries

1. **No global Souriau realization without concrete data**
   - No theorem claiming a completed coadjoint-orbit model for `G₂(2)`, `G₂*`, or `Spin(5,5)`
     unless explicit `Ad`, `Ad*`, cocycle, and dual-map data are defined and proved.

2. **No source current algebra claim without source witness construction**
   - Current/Sugawara bridge files may consume a supplied witness.
   - They may not claim split source completion automatically constructs
     `J`, `trunc`, and `comm` unless that theorem is proved.

3. **No associative matrix API for Zorn split-octonions**
   - Zorn cells are nonassociative vector-matrix coordinates with custom product.
   - Do not present them as ordinary associative `2×2` block matrix multiplication.

4. **No definitional equality `TwistorSpace = SplitOctonions`**
   - Allowed target: quantized twistor algebra *carries* split-octonion / `G₂*` structure.
   - Not allowed: definitional identification unless formally proved.

## Theorem debt policy

- If a proof is missing, expose it as explicit theorem debt (`sorry`) in the owner surface.
- Do not hide missing proofs behind wrapper certificates, `True` fields, or vacuous packets.
