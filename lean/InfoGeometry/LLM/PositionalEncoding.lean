import InfoGeometry.LLM.MaskedTransformerBlock

namespace InfoGeometry.LLM

/-- Positional-encoding abstraction over query/state space `Q`. -/
abbrev PositionalEncoding (Q : Type*) := Q → Q

namespace PositionalEncoding

variable {Q : Type*}

/-- Compatibility accessor for the native function representation. -/
abbrev encode (P : PositionalEncoding Q) : Q → Q := P

/-- Identity positional encoding. -/
def id : PositionalEncoding Q := fun q => q

/-- Sequential composition (`P2 ∘ P1`). -/
def comp (P1 P2 : PositionalEncoding Q) : PositionalEncoding Q :=
  fun q => P2 (P1 q)

@[simp] lemma id_apply (q : Q) : (id (Q := Q)).encode q = q := rfl
@[simp] lemma comp_apply (P1 P2 : PositionalEncoding Q) (q : Q) :
    (comp P1 P2).encode q = P2.encode (P1.encode q) := rfl

end PositionalEncoding

namespace TransformerBlock

variable {Q K Vh Vout ι : Type*} [DecidableEq ι]
variable [AddCommGroup Vh] [Module ℝ Vh]
variable [AddCommGroup Vout] [Module ℝ Vout]
variable {n : ℕ}

/-- Run a transformer block after positional encoding. -/
noncomputable def runWithPositionalEncoding
    (B : TransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (P : PositionalEncoding Q) : Q → Vout :=
  fun q => B.run (P.encode q)

lemma runWithPositionalEncoding_eq_comp
    (B : TransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (P : PositionalEncoding Q) :
    B.runWithPositionalEncoding P = B.run ∘ P.encode := rfl

@[simp] lemma runWithPositionalEncoding_id
    (B : TransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n) :
    B.runWithPositionalEncoding (PositionalEncoding.id (Q := Q)) = B.run := by
  funext q
  rfl

lemma runWithPositionalEncoding_comp
    (B : TransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (P1 P2 : PositionalEncoding Q) :
    B.runWithPositionalEncoding (PositionalEncoding.comp P1 P2)
      = (B.runWithPositionalEncoding P2) ∘ P1.encode := by
  funext q
  rfl

end TransformerBlock

namespace MaskedTransformerBlock

variable {Q K Vh Vout ι : Type*} [DecidableEq ι]
variable [AddCommGroup Vh] [Module ℝ Vh]
variable [AddCommGroup Vout] [Module ℝ Vout]
variable {n : ℕ}

/-- Run a masked transformer block after positional encoding. -/
noncomputable def runWithPositionalEncoding
    (M : MaskedTransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (P : PositionalEncoding Q) : Q → Vout :=
  fun q => M.run (P.encode q)

lemma runWithPositionalEncoding_eq_comp
    (M : MaskedTransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (P : PositionalEncoding Q) :
    M.runWithPositionalEncoding P = M.run ∘ P.encode := rfl

@[simp] lemma runWithPositionalEncoding_id
    (M : MaskedTransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n) :
    M.runWithPositionalEncoding (PositionalEncoding.id (Q := Q)) = M.run := by
  funext q
  rfl

lemma runWithPositionalEncoding_comp
    (M : MaskedTransformerBlock (Q := Q) (K := K) (Vh := Vh) (Vout := Vout) (ι := ι) n)
    (P1 P2 : PositionalEncoding Q) :
    M.runWithPositionalEncoding (PositionalEncoding.comp P1 P2)
      = (M.runWithPositionalEncoding P2) ∘ P1.encode := by
  funext q
  rfl

end MaskedTransformerBlock

end InfoGeometry.LLM
