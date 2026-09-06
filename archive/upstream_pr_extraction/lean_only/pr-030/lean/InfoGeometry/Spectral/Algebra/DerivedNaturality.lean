import InfoGeometry.Spectral.Algebra.GenericDerivedCouple

/-!
# Naturality of derived exact-couple pages

This file proves the functorial part of the exact-couple construction directly
from commuting families of linear maps.  No separate morphism record is
introduced: the hypotheses are exactly the two commutative squares needed by
the differential `d = j ∘ k`.
-/

namespace InfoGeometry.Spectral.Algebra

universe u v

variable {R : Type u} [Ring R]
variable {I : Type v}
variable {D E D' E' : I → Type u}
variable [∀ p, AddCommGroup (D p)] [∀ p, AddCommGroup (E p)]
variable [∀ p, AddCommGroup (D' p)] [∀ p, AddCommGroup (E' p)]
variable [∀ p, Module R (D p)] [∀ p, Module R (E p)]
variable [∀ p, Module R (D' p)] [∀ p, Module R (E' p)]
variable {iDeg jDeg kDeg : I ≃ I}

namespace GradedExactCouple

variable
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (C' : GradedExactCouple R I D' E' iDeg jDeg kDeg)
    (fD : ∀ p, D p →ₗ[R] D' p)
    (fE : ∀ p, E p →ₗ[R] E' p)

/-- Commutativity with `j` and `k` makes the induced page maps commute with
the exact-couple differential `d = j ∘ k`. -/
theorem differential_natural
    (hj : ∀ p, (fE (jDeg p)).comp (C.j p) = (C'.j p).comp (fD p))
    (hk : ∀ p, (fD (kDeg p)).comp (C.k p) = (C'.k p).comp (fE p))
    (p : I) :
    (fE (C.differentialDegree p)).comp (C.differential p) =
      (C'.differential p).comp (fE p) := by
  ext x
  change fE (jDeg (kDeg p)) (C.j (kDeg p) (C.k p x)) =
    C'.j (kDeg p) (C'.k p (fE p x))
  have hjx := LinearMap.congr_fun (hj (kDeg p)) (C.k p x)
  have hkx := LinearMap.congr_fun (hk p) x
  simp only [LinearMap.comp_apply] at hjx hkx
  rw [hjx, hkx]

/-- A commuting page map restricts to a linear map between cycle modules. -/
noncomputable def targetCycleMap
    (hj : ∀ p, (fE (jDeg p)).comp (C.j p) = (C'.j p).comp (fD p))
    (hk : ∀ p, (fD (kDeg p)).comp (C.k p) = (C'.k p).comp (fE p))
    (p : I) :
    C.targetCycles p →ₗ[R] C'.targetCycles p where
  toFun x :=
    ⟨fE (C.differentialDegree p) x.1, by
      change C'.differential (jDeg (kDeg p))
          (fE (jDeg (kDeg p)) x.1) = 0
      have h :
          fE (jDeg (kDeg (jDeg (kDeg p))))
              (C.differential (jDeg (kDeg p)) x.1) =
            C'.differential (jDeg (kDeg p))
              (fE (jDeg (kDeg p)) x.1) := by
        simpa only [differentialDegree, LinearMap.comp_apply] using
          LinearMap.congr_fun
            (differential_natural C C' fD fE hj hk (C.differentialDegree p)) x.1
      have hx := x.2
      change C.differential (jDeg (kDeg p)) x.1 = 0 at hx
      rw [← h, hx, map_zero]⟩
  map_add' x y := by
    ext
    exact map_add _ _ _
  map_smul' r x := by
    ext
    exact map_smul _ _ _

/-- The restricted cycle map sends boundaries to boundaries. -/
theorem targetCycleMap_maps_boundaries
    (hj : ∀ p, (fE (jDeg p)).comp (C.j p) = (C'.j p).comp (fD p))
    (hk : ∀ p, (fD (kDeg p)).comp (C.k p) = (C'.k p).comp (fE p))
    (p : I) :
    C.targetBoundariesInCycles p ≤
      Submodule.comap (targetCycleMap C C' fD fE hj hk p)
        (C'.targetBoundariesInCycles p) := by
  intro x hx
  change fE (C.differentialDegree p) x.1 ∈
    LinearMap.range (C'.differential p)
  change x.1 ∈ LinearMap.range (C.differential p) at hx
  rcases hx with ⟨y, hy⟩
  refine ⟨fE p y, ?_⟩
  change C'.differential p (fE p y) =
    fE (jDeg (kDeg p)) x.1
  calc
    C'.differential p (fE p y) =
        fE (jDeg (kDeg p)) (C.differential p y) := by
      symm
      simpa only [differentialDegree, LinearMap.comp_apply] using
        LinearMap.congr_fun (differential_natural C C' fD fE hj hk p) y
    _ = fE (jDeg (kDeg p)) x.1 := by rw [hy]

/-- A map commuting with the exact-couple legs induces the native quotient
map from cycles modulo boundaries to cycles modulo boundaries. -/
noncomputable def derivedPageMap
    (hj : ∀ p, (fE (jDeg p)).comp (C.j p) = (C'.j p).comp (fD p))
    (hk : ∀ p, (fD (kDeg p)).comp (C.k p) = (C'.k p).comp (fE p))
    (p : I) :
    C.DerivedE p →ₗ[R] C'.DerivedE p :=
  Submodule.mapQ
    (C.targetBoundariesInCycles p)
    (C'.targetBoundariesInCycles p)
    (targetCycleMap C C' fD fE hj hk p)
    (targetCycleMap_maps_boundaries C C' fD fE hj hk p)

/-- The quotient map is represented by the restricted cycle map on every
cycle representative. -/
@[simp]
theorem derivedPageMap_mk
    (hj : ∀ p, (fE (jDeg p)).comp (C.j p) = (C'.j p).comp (fD p))
    (hk : ∀ p, (fD (kDeg p)).comp (C.k p) = (C'.k p).comp (fE p))
    (p : I) (x : C.targetCycles p) :
    derivedPageMap C C' fD fE hj hk p (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (targetCycleMap C C' fD fE hj hk p x) :=
  Submodule.mapQ_apply _ _ _ _

/-- Identity linear maps commute with the `j` leg. -/
theorem identity_j_comm (p : I) :
    (LinearMap.id (R := R) (M := E (jDeg p))).comp (C.j p) =
      (C.j p).comp (LinearMap.id (R := R) (M := D p)) := by
  simp

/-- Identity linear maps commute with the `k` leg. -/
theorem identity_k_comm (p : I) :
    (LinearMap.id (R := R) (M := D (kDeg p))).comp (C.k p) =
      (C.k p).comp (LinearMap.id (R := R) (M := E p)) := by
  simp

/-- The map induced on a derived page by identity maps is the identity. -/
theorem derivedPageMap_identity (p : I) :
    derivedPageMap C C
        (fun q => LinearMap.id (R := R) (M := D q))
        (fun q => LinearMap.id (R := R) (M := E q))
        (identity_j_comm C) (identity_k_comm C) p =
      LinearMap.id := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := (C.targetBoundariesInCycles p).mkQ_surjective q
  rfl

end GradedExactCouple

namespace GradedExactCouple

variable
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (C' : GradedExactCouple R I D' E' iDeg jDeg kDeg)
    (fD : ∀ p, D p →ₗ[R] D' p)

/-- An indexed family of linear maps commutes with canonical equality
transport in its index. -/
theorem indexedLinearMap_cast
    {p q : I} (h : p = q) (x : D p) :
    fD q (LinearEquiv.cast (R := R) (M := D) h x) =
      LinearEquiv.cast (R := R) (M := D') h (fD p x) := by
  subst q
  rfl

/-- Commutativity with `i` also holds for the incoming, reindexed `i` map. -/
theorem incomingI_natural
    (hi : ∀ p, (fD (iDeg p)).comp (C.i p) = (C'.i p).comp (fD p))
    (p : I) :
    (fD p).comp (C.incomingI p) =
      (C'.incomingI p).comp (fD (iDeg.symm p)) := by
  ext x
  simp only [LinearMap.comp_apply, incomingI_apply]
  rw [indexedLinearMap_cast fD (iDeg.apply_symm_apply p)]
  have hix := LinearMap.congr_fun (hi (iDeg.symm p)) x
  simp only [LinearMap.comp_apply] at hix
  rw [hix]

/-- A map commuting with `i` restricts to the image module that forms the
derived `D` term. -/
noncomputable def directDerivedDMap
    (hi : ∀ p, (fD (iDeg p)).comp (C.i p) = (C'.i p).comp (fD p))
    (p : I) :
    C.DirectDerivedD p →ₗ[R] C'.DirectDerivedD p where
  toFun x :=
    ⟨fD p x.1, by
      rcases x.2 with ⟨y, hy⟩
      refine ⟨fD (iDeg.symm p) y, ?_⟩
      have hnat := LinearMap.congr_fun (incomingI_natural C C' fD hi p) y
      simp only [LinearMap.comp_apply] at hnat
      calc
        C'.incomingI p (fD (iDeg.symm p) y) =
            fD p (C.incomingI p y) := hnat.symm
        _ = fD p x.1 := by rw [hy]⟩
  map_add' x y := by
    ext
    exact map_add _ _ _
  map_smul' r x := by
    ext
    exact map_smul _ _ _

/-- The restricted image map commutes with the derived `i′` map. -/
theorem directDerivedI_natural
    (hi : ∀ p, (fD (iDeg p)).comp (C.i p) = (C'.i p).comp (fD p))
    (p : I) :
    (directDerivedDMap C C' fD hi (derivedIDegree iDeg p)).comp
        (C.directDerivedI p) =
      (C'.directDerivedI p).comp
        (directDerivedDMap C C' fD hi p) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change fD (iDeg p) (C.i p x.1) =
    C'.i p (fD p x.1)
  simpa only [LinearMap.comp_apply] using
    LinearMap.congr_fun (hi p) x.1

/-- The cycle-valued `j` map is natural under commuting `j` and `k` maps. -/
theorem jToTargetCycles_natural
    (fE : ∀ p, E p →ₗ[R] E' p)
    (hj : ∀ p, (fE (jDeg p)).comp (C.j p) = (C'.j p).comp (fD p))
    (hk : ∀ p, (fD (kDeg p)).comp (C.k p) = (C'.k p).comp (fE p))
    (p : I) :
    (targetCycleMap C C' fD fE hj hk (C.derivedJPageIndex p)).comp
        (C.jToTargetCycles p) =
      (C'.jToTargetCycles p).comp (fD (iDeg.symm p)) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change fE (C.differentialDegree (C.derivedJPageIndex p))
      (C.jToTargetCycles p x).1 =
    (C'.jToTargetCycles p (fD (iDeg.symm p) x)).1
  rw [C.jToTargetCycles_coe, C'.jToTargetCycles_coe]
  rw [indexedLinearMap_cast fE
    (C.differentialDegree_derivedJPageIndex p).symm]
  have hjx := LinearMap.congr_fun (hj (iDeg.symm p)) x
  simp only [LinearMap.comp_apply] at hjx
  rw [hjx]
  rfl

/-- The class induced by `j` is natural in homology. -/
theorem jToDerivedE_natural
    (fE : ∀ p, E p →ₗ[R] E' p)
    (hj : ∀ p, (fE (jDeg p)).comp (C.j p) = (C'.j p).comp (fD p))
    (hk : ∀ p, (fD (kDeg p)).comp (C.k p) = (C'.k p).comp (fE p))
    (p : I) (x : D (iDeg.symm p)) :
    derivedPageMap C C' fD fE hj hk (C.derivedJPageIndex p)
        (C.jToDerivedE p x) =
      C'.jToDerivedE p (fD (iDeg.symm p) x) := by
  rw [C.jToDerivedE_apply, C'.jToDerivedE_apply]
  rw [derivedPageMap_mk]
  apply congrArg Submodule.Quotient.mk
  exact LinearMap.congr_fun
    (jToTargetCycles_natural C C' fD fE hj hk p) x

/-- The induced maps on the derived `D` and `E` terms commute with `j′`. -/
theorem directDerivedJ_natural
    (fE : ∀ p, E p →ₗ[R] E' p)
    (hi : ∀ p, (fD (iDeg p)).comp (C.i p) = (C'.i p).comp (fD p))
    (hj : ∀ p, (fE (jDeg p)).comp (C.j p) = (C'.j p).comp (fD p))
    (hk : ∀ p, (fD (kDeg p)).comp (C.k p) = (C'.k p).comp (fE p))
    (p : I) :
    (derivedPageMap C C' fD fE hj hk
        (C.derivedJPageIndex p)).comp
        (C.directDerivedJ p) =
      (C'.directDerivedJ p).comp
        (directDerivedDMap C C' fD hi p) := by
  apply LinearMap.ext
  intro z
  rcases z.2 with ⟨x, hx⟩
  have hz :
      z = ⟨C.incomingI p x, ⟨x, rfl⟩⟩ := by
    apply Subtype.ext
    exact hx.symm
  subst z
  change
    derivedPageMap C C' fD fE hj hk (C.derivedJPageIndex p)
        (C.directDerivedJ p
          ⟨C.incomingI p x, ⟨x, rfl⟩⟩) =
      C'.directDerivedJ p
        (directDerivedDMap C C' fD hi p
          ⟨C.incomingI p x, ⟨x, rfl⟩⟩)
  rw [C.directDerivedJ_imageRepresentative]
  have hnat := LinearMap.congr_fun (incomingI_natural C C' fD hi p) x
  simp only [LinearMap.comp_apply] at hnat
  have hD :
      directDerivedDMap C C' fD hi p
          ⟨C.incomingI p x, ⟨x, rfl⟩⟩ =
        ⟨C'.incomingI p (fD (iDeg.symm p) x),
          ⟨fD (iDeg.symm p) x, rfl⟩⟩ := by
    apply Subtype.ext
    exact hnat
  rw [hD, C'.directDerivedJ_imageRepresentative]
  exact jToDerivedE_natural C C' fD fE hj hk p x

/-- The map on the `E` object of the derived couple is the homology map at
the canonically preceding differential degree. -/
noncomputable def directDerivedEMap
    (fE : ∀ p, E p →ₗ[R] E' p)
    (hj : ∀ p, (fE (jDeg p)).comp (C.j p) = (C'.j p).comp (fD p))
    (hk : ∀ p, (fD (kDeg p)).comp (C.k p) = (C'.k p).comp (fE p))
    (p : I) :
    C.DirectDerivedE p →ₗ[R] C'.DirectDerivedE p :=
  derivedPageMap C C' fD fE hj hk (C.differentialDegree.symm p)

/-- The derived `E` map acts on a represented cycle by applying the original
`E` map to that cycle. -/
@[simp]
theorem directDerivedEMap_mk
    (fE : ∀ p, E p →ₗ[R] E' p)
    (hj : ∀ p, (fE (jDeg p)).comp (C.j p) = (C'.j p).comp (fD p))
    (hk : ∀ p, (fD (kDeg p)).comp (C.k p) = (C'.k p).comp (fE p))
    (p : I)
    (x : C.targetCycles (C.differentialDegree.symm p)) :
    directDerivedEMap C C' fD fE hj hk p (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (targetCycleMap C C' fD fE hj hk
          (C.differentialDegree.symm p) x) :=
  derivedPageMap_mk C C' fD fE hj hk _ x

/-- Canonical transport of a cycle to its actual degree commutes with an
indexed family of linear maps. -/
theorem directCycleValue_natural
    (fE : ∀ p, E p →ₗ[R] E' p)
    (hj : ∀ p, (fE (jDeg p)).comp (C.j p) = (C'.j p).comp (fD p))
    (hk : ∀ p, (fD (kDeg p)).comp (C.k p) = (C'.k p).comp (fE p))
    (p : I)
    (x : C.targetCycles (C.differentialDegree.symm p)) :
    fE p (C.directCycleValue p x) =
      C'.directCycleValue p
        (targetCycleMap C C' fD fE hj hk
          (C.differentialDegree.symm p) x) := by
  change
    fE p
        (LinearEquiv.cast (R := R) (M := E)
          (C.differentialDegree.apply_symm_apply p) x.1) =
      LinearEquiv.cast (R := R) (M := E')
        (C'.differentialDegree.apply_symm_apply p)
        (fE (C.differentialDegree (C.differentialDegree.symm p)) x.1)
  exact indexedLinearMap_cast fE
    (C.differentialDegree.apply_symm_apply p) x.1

/-- The induced maps on derived homology and the incoming image commute with
the derived `k′` map. -/
theorem directDerivedK_natural
    (fE : ∀ p, E p →ₗ[R] E' p)
    (hi : ∀ p, (fD (iDeg p)).comp (C.i p) = (C'.i p).comp (fD p))
    (hj : ∀ p, (fE (jDeg p)).comp (C.j p) = (C'.j p).comp (fD p))
    (hk : ∀ p, (fD (kDeg p)).comp (C.k p) = (C'.k p).comp (fE p))
    (p : I) :
    (directDerivedDMap C C' fD hi (derivedKDegree kDeg p)).comp
        (C.directDerivedK p) =
      (C'.directDerivedK p).comp
        (directDerivedEMap C C' fD fE hj hk p) := by
  apply LinearMap.ext
  intro z
  refine Submodule.Quotient.induction_on
    (C.targetBoundariesInCycles (C.differentialDegree.symm p)) z ?_
  intro x
  change
    directDerivedDMap C C' fD hi (derivedKDegree kDeg p)
        (C.directDerivedK p (Submodule.Quotient.mk x)) =
      C'.directDerivedK p
        (directDerivedEMap C C' fD fE hj hk p
          (Submodule.Quotient.mk x))
  rw [C.directDerivedK_mk, directDerivedEMap_mk,
    C'.directDerivedK_mk]
  apply Subtype.ext
  change
    fD (kDeg p) (C.k p (C.directCycleValue p x)) =
      C'.k p
        (C'.directCycleValue p
          (targetCycleMap C C' fD fE hj hk
            (C.differentialDegree.symm p) x))
  have hkx := LinearMap.congr_fun (hk p) (C.directCycleValue p x)
  simp only [LinearMap.comp_apply] at hkx
  rw [hkx, directCycleValue_natural C C' fD fE hj hk p x]

end GradedExactCouple

namespace GradedExactCouple

variable {D'' E'' : I → Type u}
variable [∀ p, AddCommGroup (D'' p)] [∀ p, AddCommGroup (E'' p)]
variable [∀ p, Module R (D'' p)] [∀ p, Module R (E'' p)]

variable
    (C : GradedExactCouple R I D E iDeg jDeg kDeg)
    (C' : GradedExactCouple R I D' E' iDeg jDeg kDeg)
    (C'' : GradedExactCouple R I D'' E'' iDeg jDeg kDeg)
    (fD : ∀ p, D p →ₗ[R] D' p)
    (fE : ∀ p, E p →ₗ[R] E' p)
    (gD : ∀ p, D' p →ₗ[R] D'' p)
    (gE : ∀ p, E' p →ₗ[R] E'' p)

/-- Commutativity with `j` is closed under pointwise composition. -/
theorem composite_j_comm
    (hf : ∀ p, (fE (jDeg p)).comp (C.j p) = (C'.j p).comp (fD p))
    (hg : ∀ p, (gE (jDeg p)).comp (C'.j p) = (C''.j p).comp (gD p))
    (p : I) :
    ((gE (jDeg p)).comp (fE (jDeg p))).comp (C.j p) =
      (C''.j p).comp ((gD p).comp (fD p)) := by
  rw [LinearMap.comp_assoc, hf p, ← LinearMap.comp_assoc, hg p,
    LinearMap.comp_assoc]

/-- Commutativity with `k` is closed under pointwise composition. -/
theorem composite_k_comm
    (hf : ∀ p, (fD (kDeg p)).comp (C.k p) = (C'.k p).comp (fE p))
    (hg : ∀ p, (gD (kDeg p)).comp (C'.k p) = (C''.k p).comp (gE p))
    (p : I) :
    ((gD (kDeg p)).comp (fD (kDeg p))).comp (C.k p) =
      (C''.k p).comp ((gE p).comp (fE p)) := by
  rw [LinearMap.comp_assoc, hf p, ← LinearMap.comp_assoc, hg p,
    LinearMap.comp_assoc]

/-- Restriction to cycle kernels preserves composition exactly. -/
theorem targetCycleMap_comp
    (hfj : ∀ p, (fE (jDeg p)).comp (C.j p) = (C'.j p).comp (fD p))
    (hfk : ∀ p, (fD (kDeg p)).comp (C.k p) = (C'.k p).comp (fE p))
    (hgj : ∀ p, (gE (jDeg p)).comp (C'.j p) = (C''.j p).comp (gD p))
    (hgk : ∀ p, (gD (kDeg p)).comp (C'.k p) = (C''.k p).comp (gE p))
    (p : I) :
    targetCycleMap C C''
        (fun q => (gD q).comp (fD q))
        (fun q => (gE q).comp (fE q))
        (composite_j_comm C C' C'' fD fE gD gE hfj hgj)
        (composite_k_comm C C' C'' fD fE gD gE hfk hgk) p =
      (targetCycleMap C' C'' gD gE hgj hgk p).comp
        (targetCycleMap C C' fD fE hfj hfk p) := by
  apply LinearMap.ext
  intro x
  rfl

/-- Passing from cycles to cycles modulo boundaries preserves composition. -/
theorem derivedPageMap_comp
    (hfj : ∀ p, (fE (jDeg p)).comp (C.j p) = (C'.j p).comp (fD p))
    (hfk : ∀ p, (fD (kDeg p)).comp (C.k p) = (C'.k p).comp (fE p))
    (hgj : ∀ p, (gE (jDeg p)).comp (C'.j p) = (C''.j p).comp (gD p))
    (hgk : ∀ p, (gD (kDeg p)).comp (C'.k p) = (C''.k p).comp (gE p))
    (p : I) :
    derivedPageMap C C''
        (fun q => (gD q).comp (fD q))
        (fun q => (gE q).comp (fE q))
        (composite_j_comm C C' C'' fD fE gD gE hfj hgj)
        (composite_k_comm C C' C'' fD fE gD gE hfk hgk) p =
      (derivedPageMap C' C'' gD gE hgj hgk p).comp
        (derivedPageMap C C' fD fE hfj hfk p) := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := (C.targetBoundariesInCycles p).mkQ_surjective q
  rfl

end GradedExactCouple

end InfoGeometry.Spectral.Algebra
