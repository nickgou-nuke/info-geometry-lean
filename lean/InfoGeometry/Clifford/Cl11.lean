import InfoGeometry.Krein.DoubledSpace

/-!
# InfoGeometry.Clifford.Cl11

Compatibility shim re-exporting the canonical `InfoGeometry.Krein.DoubledSpace`
`Cl(1,1)` primitives under the legacy global names used by older modules.
-/

section KreinClifford

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Legacy global alias for the canonical doubled space `E ⊕ E`. -/
abbrev DoubledSpace (E : Type _) := InfoGeometry.Krein.DoubledSpace E

/-- Legacy global alias for the canonical swap involution `J`. -/
noncomputable abbrev modularJ : DoubledSpace E →L[ℝ] DoubledSpace E :=
  InfoGeometry.Krein.modularJ (E := E)

/-- Legacy global alias for the canonical sign involution `ε`. -/
noncomputable abbrev spectralEpsilon : DoubledSpace E →L[ℝ] DoubledSpace E :=
  InfoGeometry.Krein.spectralEpsilon (E := E)

/-- Legacy global compatibility definition `I = J ∘ ε`. -/
noncomputable abbrev complexI : DoubledSpace E →L[ℝ] DoubledSpace E :=
  InfoGeometry.Krein.complexI (E := E)

/-- Legacy global alias for `Cl(1,1)` relation packaging. -/
abbrev Cl11Relations (J ε : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  InfoGeometry.Krein.Cl11Relations J ε

/-- Legacy global alias for the `Cl(1,1)` relation marker. -/
abbrev Cl11Algebra (J ε : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  InfoGeometry.Krein.Cl11Algebra J ε

@[simp] lemma modularJ_apply (v : DoubledSpace E) :
    modularJ (E := E) v = InfoGeometry.Krein.toDoubled v.snd v.fst := rfl

@[simp] lemma spectralEpsilon_apply (v : DoubledSpace E) :
    spectralEpsilon (E := E) v = InfoGeometry.Krein.toDoubled v.fst (-v.snd) := rfl

@[simp] lemma complexI_apply (v : DoubledSpace E) :
    complexI (E := E) v = InfoGeometry.Krein.toDoubled (-v.snd) v.fst := rfl

lemma modularJ_involution :
    modularJ (E := E).comp (modularJ (E := E))
      = ContinuousLinearMap.id ℝ (DoubledSpace E) :=
  InfoGeometry.Krein.modularJ_involution (E := E)

lemma spectralEpsilon_involution :
    spectralEpsilon (E := E).comp (spectralEpsilon (E := E))
      = ContinuousLinearMap.id ℝ (DoubledSpace E) :=
  InfoGeometry.Krein.spectralEpsilon_involution (E := E)

lemma modularJ_spectralEpsilon_anticommute :
    modularJ (E := E).comp (spectralEpsilon (E := E)) =
      -((spectralEpsilon (E := E)).comp (modularJ (E := E))) :=
  InfoGeometry.Krein.modularJ_spectralEpsilon_anticommute (E := E)

/-- The canonical generator `I = J ∘ ε` squares to `-id`. -/
lemma complexI_sq :
    (complexI (E := E)).comp (complexI (E := E))
      = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) :=
  InfoGeometry.Krein.complexI_sq (E := E)

theorem modularJ_spectralEpsilon_hasCl11Relations :
    Cl11Relations (modularJ (E := E)) (spectralEpsilon (E := E)) :=
  InfoGeometry.Krein.modularJ_spectralEpsilon_hasCl11Relations (E := E)

theorem modularJ_spectralEpsilon_isCl11 :
    Cl11Algebra (modularJ (E := E)) (spectralEpsilon (E := E)) :=
  InfoGeometry.Krein.modularJ_spectralEpsilon_isCl11 (E := E)

end KreinClifford
