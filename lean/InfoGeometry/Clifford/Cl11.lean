import InfoGeometry.Krein.DoubledSpace

/-! Compatibility exports for the canonical doubled-space Clifford lane. -/

section KreinClifford

noncomputable section

variable {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev DoubledSpace (E : Type _) := InfoGeometry.Krein.DoubledSpace E

abbrev modularJ : DoubledSpace E →L[ℝ] DoubledSpace E :=
  InfoGeometry.Krein.modular_j (E := E)

abbrev spectralEpsilon : DoubledSpace E →L[ℝ] DoubledSpace E :=
  InfoGeometry.Krein.spectral_epsilon (E := E)

def complexI : DoubledSpace E →L[ℝ] DoubledSpace E :=
  modularJ.comp spectralEpsilon

abbrev Cl11Relations (J ε : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  InfoGeometry.Krein.cl11_relations J ε

abbrev Cl11Algebra (J ε : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  InfoGeometry.Krein.cl11_algebra J ε

@[simp] lemma modularJ_apply (v : DoubledSpace E) :
    modularJ (E := E) v = WithLp.toLp (2 : ENNReal) (WithLp.snd v, WithLp.fst v) := rfl

@[simp] lemma spectralEpsilon_apply (v : DoubledSpace E) :
    spectralEpsilon (E := E) v = WithLp.toLp (2 : ENNReal) (WithLp.fst v, -WithLp.snd v) := rfl

@[simp] lemma complexI_apply (v : DoubledSpace E) :
    complexI (E := E) v = WithLp.toLp (2 : ENNReal) (-WithLp.snd v, WithLp.fst v) := by
  rfl

lemma modularJ_involution :
    modularJ (E := E).comp (modularJ (E := E)) = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  simpa [modularJ] using (InfoGeometry.Krein.modular_j_involution (E := E))

lemma spectralEpsilon_involution :
    spectralEpsilon (E := E).comp (spectralEpsilon (E := E)) = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  simpa [spectralEpsilon] using (InfoGeometry.Krein.spectral_epsilon_involution (E := E))

lemma modularJ_spectralEpsilon_anticommute :
    modularJ (E := E).comp (spectralEpsilon (E := E)) =
      -((spectralEpsilon (E := E)).comp (modularJ (E := E))) := by
  simpa [modularJ, spectralEpsilon] using
    (InfoGeometry.Krein.modular_j_spectral_epsilon_anticommute (E := E))

lemma complexI_sq :
    (complexI (E := E)).comp (complexI (E := E)) =
      -(ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
  simpa [complexI] using (InfoGeometry.Krein.complex_i_sq (E := E))

theorem modularJ_spectralEpsilon_hasCl11Relations :
    Cl11Relations (modularJ (E := E)) (spectralEpsilon (E := E)) := by
  simpa [Cl11Relations, modularJ, spectralEpsilon] using
    (InfoGeometry.Krein.modular_j_spectral_epsilon_has_cl11_relations (E := E))

theorem modularJ_spectralEpsilon_isCl11 :
    Cl11Algebra (modularJ (E := E)) (spectralEpsilon (E := E)) := by
  simpa [Cl11Algebra, modularJ, spectralEpsilon] using
    (InfoGeometry.Krein.modular_j_spectral_epsilon_is_cl11 (E := E))

end
end KreinClifford
