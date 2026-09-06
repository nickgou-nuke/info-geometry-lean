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
abbrev modularJ : DoubledSpace E →L[ℝ] DoubledSpace E :=
  InfoGeometry.Krein.modularJ (E := E)

/-- Legacy global alias for the canonical sign involution `ε`. -/
abbrev spectralEpsilon : DoubledSpace E →L[ℝ] DoubledSpace E :=
  InfoGeometry.Krein.spectralEpsilon (E := E)

/-- Legacy global compatibility definition `I = J ∘ ε`. -/
def complexI : DoubledSpace E →L[ℝ] DoubledSpace E :=
  modularJ.comp spectralEpsilon

/-- Legacy global alias for `Cl(1,1)` relation packaging. -/
abbrev Cl11Relations (J ε : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  InfoGeometry.Krein.Cl11Relations J ε

/-- Legacy global alias for the `Cl(1,1)` relation marker. -/
abbrev Cl11Algebra (J ε : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  InfoGeometry.Krein.Cl11Algebra J ε

@[simp] lemma modularJ_apply (v : DoubledSpace E) :
    modularJ (E := E) v = (v.2, v.1) := by
  simp [modularJ]

@[simp] lemma spectralEpsilon_apply (v : DoubledSpace E) :
    spectralEpsilon (E := E) v = (v.1, -v.2) := by
  simp [spectralEpsilon]

@[simp] lemma complexI_apply (v : DoubledSpace E) :
    complexI (E := E) v = (-v.2, v.1) := by
  simp [complexI]

lemma modularJ_involution :
    modularJ (E := E).comp (modularJ (E := E))
      = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  simpa [modularJ] using (InfoGeometry.Krein.modularJ_involution (E := E))

lemma spectralEpsilon_involution :
    spectralEpsilon (E := E).comp (spectralEpsilon (E := E))
      = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  simpa [spectralEpsilon] using (InfoGeometry.Krein.spectralEpsilon_involution (E := E))

lemma modularJ_spectralEpsilon_anticommute :
    modularJ (E := E).comp (spectralEpsilon (E := E)) =
      -((spectralEpsilon (E := E)).comp (modularJ (E := E))) := by
  simpa [modularJ, spectralEpsilon] using
    (InfoGeometry.Krein.modularJ_spectralEpsilon_anticommute (E := E))

/-- The canonical generator `I = J ∘ ε` squares to `-id`. -/
lemma complexI_sq :
    (complexI (E := E)).comp (complexI (E := E))
      = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
  simpa [complexI] using (InfoGeometry.Krein.complexI_sq (E := E))

theorem modularJ_spectralEpsilon_hasCl11Relations :
    Cl11Relations (modularJ (E := E)) (spectralEpsilon (E := E)) := by
  simpa [Cl11Relations, modularJ, spectralEpsilon] using
    (InfoGeometry.Krein.modularJ_spectralEpsilon_hasCl11Relations (E := E))

theorem modularJ_spectralEpsilon_isCl11 :
    Cl11Algebra (modularJ (E := E)) (spectralEpsilon (E := E)) := by
  simpa [Cl11Algebra, modularJ, spectralEpsilon] using
    (InfoGeometry.Krein.modularJ_spectralEpsilon_isCl11 (E := E))

end KreinClifford
