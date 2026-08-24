/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.AlgebraicTopologyI.code.Section1
import Atlas.AlgebraicTopologyI.code.Section5
import Atlas.AlgebraicTopologyI.code.Section11
import Atlas.AlgebraicTopologyI.code.LocalityPrinciple

open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI

open Set in
/-- **Definition 10.1 (Excisive triple).** *The triple `(X, A, U)` is **excisive** when
`closure U ⊆ interior A`, i.e. the closure of `U` lies in the topological interior of `A`.*

This is the hypothesis under which the excision theorem (Theorem 10.2) asserts that the
inclusion `(X ∖ U, A ∖ U) → (X, A)` induces an isomorphism on relative homology. -/
def IsExcisive (X : Type*) [TopologicalSpace X] (A U : Set X) : Prop :=
  closure U ⊆ interior A

namespace Excision

open AlgebraicTopology

noncomputable section

/-- The singular chain complex functor with integer coefficients,
`X ↦ C_*(X; \mathbb{Z})`. -/
abbrev singularChainZ : TopCat.{0} ⥤ ChainComplex AddCommGrpCat ℕ :=
  (singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)

/-- The continuous inclusion `A ↪ X` of a subspace, as a morphism in `TopCat`. -/
def subspaceTopInclusion {X : Type} [TopologicalSpace X] (A : Set X) :
    TopCat.of A ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The chain map `C_*(A; ℤ) → C_*(X; ℤ)` induced by the subspace inclusion `A ↪ X`. -/
def subspaceChainInclusion (X : Type) [TopologicalSpace X] (A : Set X) :
    singularChainZ.obj (TopCat.of A) ⟶ singularChainZ.obj (TopCat.of X) :=
  singularChainZ.map (subspaceTopInclusion A)

/-- The *relative singular chain complex* `C_*(X, A; ℤ) := C_*(X) / C_*(A)`, defined as the
cokernel of the chain inclusion `C_*(A) ↪ C_*(X)`. -/
def relativeSingularChainComplex (X : Type) [TopologicalSpace X] (A : Set X) :
    ChainComplex AddCommGrpCat ℕ :=
  cokernel (subspaceChainInclusion X A)

/-- The `n`-th *relative singular homology group* `H_n(X, A; ℤ)`, defined as the `n`-th
homology of the relative singular chain complex `C_*(X, A)`. -/
def RelativeSingularHomologyGroup (n : ℕ) (X : Type) [TopologicalSpace X] (A : Set X) :
    AddCommGrpCat :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n).obj
    (relativeSingularChainComplex X A)

variable (X : Type) [TopologicalSpace X] (A U : Set X)

/-- The continuous inclusion `A ∖ U ↪ A` obtained by viewing `A \ U` first as a subset of
`X \ U` and then forgetting the complement. -/
def excisedSubsetToSubspace :
    TopCat.of (Subtype.val ⁻¹' A : Set (Uᶜ : Set X)) ⟶ TopCat.of A :=
  TopCat.ofHom ⟨fun ⟨⟨x, _⟩, hx⟩ => ⟨x, hx⟩, by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val⟩

/-- The continuous inclusion `X ∖ U ↪ X`. -/
def complementInclusion :
    TopCat.of (Uᶜ : Set X) ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Commutativity of the square `(A ∖ U) ↪ (X ∖ U); (A ∖ U) ↪ A` with `(X ∖ U) ↪ X; A ↪ X`,
which is what makes the excision pair-inclusion a well-defined morphism of pairs. -/
lemma excision_square_comm :
    subspaceTopInclusion (Subtype.val ⁻¹' A : Set (Uᶜ : Set X)) ≫
      complementInclusion X U =
    excisedSubsetToSubspace X A U ≫ subspaceTopInclusion A := by
  ext ⟨⟨_, _⟩, _⟩; rfl

/-- The chain map between relative chain complexes
`C_*(X ∖ U, A ∖ U) → C_*(X, A)` induced by the pair inclusion. Excision asserts that this
map is a quasi-isomorphism whenever `(X, A, U)` is excisive. -/
def excisionRelativeChainMap :
    relativeSingularChainComplex (Uᶜ : Set X) (Subtype.val ⁻¹' A) ⟶
    relativeSingularChainComplex X A :=
  cokernel.map _ _
    (singularChainZ.map (excisedSubsetToSubspace X A U))
    (singularChainZ.map (complementInclusion X U))
    (by
      show singularChainZ.map _ ≫ singularChainZ.map _ =
        singularChainZ.map _ ≫ singularChainZ.map _
      rw [← singularChainZ.map_comp, ← singularChainZ.map_comp, excision_square_comm])

/-- The induced map on degree-`n` relative homology
`H_n(X ∖ U, A ∖ U) → H_n(X, A)` coming from the excision chain map. -/
def excisionHomologyMap (n : ℕ) :
    RelativeSingularHomologyGroup n (Uᶜ : Set X) (Subtype.val ⁻¹' A) ⟶
    RelativeSingularHomologyGroup n X A :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n).map
    (excisionRelativeChainMap X A U)

end

end Excision

namespace Excision

open AlgebraicTopology Set

noncomputable section

/-- An excisive triple `(X, A, U)` produces an open cover of `X` by `interior A` and
`interior Uᶜ`. This converts the excision hypothesis into the form needed by the locality
principle. -/
lemma cover_of_excisive {X : Type} [TopologicalSpace X] {A U : Set X}
    (hexc : IsExcisive X A U) : interior A ∪ interior Uᶜ = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  by_cases hx : x ∈ interior A
  · exact Set.mem_union_left _ hx
  · refine Set.mem_union_right _ ?_
    rw [interior_compl]
    exact fun hcl => hx (hexc hcl)

/-- The *small chain complex* `C^{\{A, B\}}_*(X)` for the two-element cover `{A, B}`: the
image of the chain map `C_*(A) ⊕ C_*(B) → C_*(X)` sending a pair to the sum of its
components in `C_*(X)`. -/
def smallChainComplex (X : Type) [TopologicalSpace X] (A B : Set X) :
    ChainComplex AddCommGrpCat ℕ :=
  image (biprod.desc (subspaceChainInclusion X A) (subspaceChainInclusion X B))

/-- The inclusion `C^{\{A, B\}}_*(X) ↪ C_*(X)` of the small chain complex into the full
singular chain complex (the canonical image inclusion). -/
def smallChainInclusion (X : Type) [TopologicalSpace X] (A B : Set X) :
    smallChainComplex X A B ⟶ singularChainZ.obj (TopCat.of X) :=
  image.ι _

/-- If `interior A ∪ interior B = X`, then `{A, B}` is a cover of `X` in the sense required
by the locality principle. -/
lemma twoElementCover_isCover {X : Type} [TopologicalSpace X] {A B : Set X}
    (hcover : interior A ∪ interior B = Set.univ) :
    IsCover ({A, B} : Set (Set X)) := by
  rw [isCover_iff]
  intro x
  have hx := eq_univ_iff_forall.mp hcover x
  rcases hx with hA | hB
  · exact ⟨A, Or.inl rfl, hA⟩
  · exact ⟨B, Or.inr (mem_singleton_iff.mpr rfl), hB⟩


/-- The inclusion of small singular chains into all singular chains is a monomorphism. -/
instance smallSingularInclusion_mono (X : Type) [TopologicalSpace X]
    (𝒜 : Set (Set X)) : Mono (LocalityPrinciple.smallSingularInclusion (TopCat.of X) 𝒜) := by
  apply HomologicalComplex.mono_of_mono_f
  intro i
  exact ConcreteCategory.mono_of_injective _
    (LocalityPrinciple.smallSingularInclusion_injective (TopCat.of X) 𝒜 i)


/-- The canonical strong epimorphism `C_*(A) ⊕ C_*(B) ↠ C^{\{A, B\}}_*(X)` from the
biproduct to the small singular chain complex for the two-element cover `{A, B}`. -/
noncomputable def smallChainFactorization (X : Type) [TopologicalSpace X] (A B : Set X) :
    singularChainZ.obj (TopCat.of A) ⊞ singularChainZ.obj (TopCat.of B) ⟶
    LocalityPrinciple.smallSingularChainComplex (TopCat.of X) {A, B} := by sorry


/-- The factorization map `C_*(A) ⊕ C_*(B) → C^{\{A, B\}}_*(X)` is a strong epimorphism. -/
theorem smallChainFactorization_strongEpi (X : Type) [TopologicalSpace X]
    (A B : Set X) : StrongEpi (smallChainFactorization X A B) := by sorry

attribute [instance] smallChainFactorization_strongEpi


/-- Compatibility: the factorization through the small chain complex composed with the
inclusion into `C_*(X)` recovers the canonical biproduct map
`C_*(A) ⊕ C_*(B) → C_*(X)`. -/
theorem smallChainFactorization_comp (X : Type) [TopologicalSpace X] (A B : Set X) :
    smallChainFactorization X A B ≫
      LocalityPrinciple.smallSingularInclusion (TopCat.of X) ({A, B} : Set (Set X)) =
    biprod.desc (subspaceChainInclusion X A) (subspaceChainInclusion X B) := by sorry

/-- The image presentation `smallChainComplex X A B` is canonically isomorphic to the small
singular chain complex `C^{\{A, B\}}_*(X)` defined via the cover machinery. -/
noncomputable def smallChainIso_of_twoElementCover
    (X : Type) [TopologicalSpace X] (A B : Set X) :
    smallChainComplex X A B ≅
      LocalityPrinciple.smallSingularChainComplex (TopCat.of X) {A, B} :=
  (image.isoStrongEpiMono
    (smallChainFactorization X A B)
    (LocalityPrinciple.smallSingularInclusion (TopCat.of X) ({A, B} : Set (Set X)))
    (smallChainFactorization_comp X A B)).symm

/-- Compatibility of the isomorphism `smallChainIso_of_twoElementCover` with the inclusions
into `C_*(X)`: the two presentations of `C^{\{A, B\}}_*(X) ↪ C_*(X)` agree. -/
theorem smallChainInclusion_comm_of_twoElementCover
    (X : Type) [TopologicalSpace X] (A B : Set X) :
    (smallChainIso_of_twoElementCover X A B).hom ≫
      LocalityPrinciple.smallSingularInclusion (TopCat.of X) {A, B} =
    smallChainInclusion X A B :=
  image.isoStrongEpiMono_inv_comp_mono
    (smallChainFactorization X A B)
    (LocalityPrinciple.smallSingularInclusion (TopCat.of X) ({A, B} : Set (Set X)))
    (smallChainFactorization_comp X A B)

/-- **Locality principle (two-element cover form).** *If `{A, B}` is a topological cover of
`X` (i.e. `interior A ∪ interior B = X`), then the inclusion `C^{\{A, B\}}_*(X) ↪ C_*(X)`
is a quasi-isomorphism.*

This is the key technical input to the excision theorem: it says that every singular chain
can be subdivided into one supported on `A` or `B` without changing homology. -/
theorem localityPrinciple (X : Type) [TopologicalSpace X] (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) :
    QuasiIso (smallChainInclusion X A B) := by

  have h𝒜 := twoElementCover_isCover hcover

  haveI hqi := LocalityPrinciple.locality_principle (TopCat.of X) {A, B} h𝒜

  haveI : QuasiIso (smallChainIso_of_twoElementCover X A B).hom :=
    quasiIso_of_isIso _

  haveI : QuasiIso ((smallChainIso_of_twoElementCover X A B).hom ≫
      LocalityPrinciple.smallSingularInclusion (TopCat.of X) {A, B}) :=
    inferInstance

  exact (smallChainInclusion_comm_of_twoElementCover X A B) ▸ ‹_›

/-- The chain map `C_*(A) → C^{\{A, B\}}_*(X)` factoring the inclusion `C_*(A) ↪ C_*(X)`
through the small chain complex. -/
def smallChainInclusionA (X : Type) [TopologicalSpace X] (A B : Set X) :
    singularChainZ.obj (TopCat.of A) ⟶ smallChainComplex X A B :=
  biprod.inl ≫ factorThruImage (biprod.desc (subspaceChainInclusion X A) (subspaceChainInclusion X B))

/-- Compatibility: the small-complex factorization of `C_*(A) ↪ C_*(X)` composed with the
inclusion of the small complex into `C_*(X)` recovers the original inclusion. -/
lemma smallChainInclusionA_comp_ι (X : Type) [TopologicalSpace X] (A B : Set X) :
    smallChainInclusionA X A B ≫ smallChainInclusion X A B =
    subspaceChainInclusion X A := by
  change (biprod.inl ≫ factorThruImage
    (biprod.desc (subspaceChainInclusion X A) (subspaceChainInclusion X B))) ≫
    image.ι (biprod.desc (subspaceChainInclusion X A) (subspaceChainInclusion X B)) = _
  rw [Category.assoc, image.fac, biprod.inl_desc]

/-- The defining short exact sequence of the relative chain complex
`0 → C_*(A) → C_*(X) → C_*(X, A) → 0`. -/
def bottomSES (X : Type) [TopologicalSpace X] (A : Set X) :
    ShortComplex (ChainComplex AddCommGrpCat ℕ) :=
  ShortComplex.mk (subspaceChainInclusion X A)
    (cokernel.π (subspaceChainInclusion X A))

/-- The short exact sequence with `A`-chains, small chains, and their cokernel:
`0 → C_*(A) → C^{\{A, B\}}_*(X) → C^{\{A, B\}}_*(X) / C_*(A) → 0`. Used to compare with
`bottomSES` via the excision SES morphism. -/
def topSES (X : Type) [TopologicalSpace X] (A B : Set X) :
    ShortComplex (ChainComplex AddCommGrpCat ℕ) :=
  ShortComplex.mk (smallChainInclusionA X A B)
    (cokernel.π (smallChainInclusionA X A B))

/-- The morphism of short exact sequences from `topSES X A B` (small chains) to
`bottomSES X A` (full chains), with identity on `C_*(A)`, the small inclusion on the middle
term, and the induced map on cokernels on the right. -/
def excisionSESMorphism (X : Type) [TopologicalSpace X] (A B : Set X) :
    topSES X A B ⟶ bottomSES X A :=
  ShortComplex.Hom.mk
    (τ₁ := 𝟙 _)
    (τ₂ := smallChainInclusion X A B)
    (τ₃ := cokernel.map (smallChainInclusionA X A B)
      (subspaceChainInclusion X A)
      (𝟙 _) (smallChainInclusion X A B)
      (by rw [Category.id_comp, smallChainInclusionA_comp_ι]))
    (comm₁₂ := by
      show 𝟙 _ ≫ subspaceChainInclusion X A =
        smallChainInclusionA X A B ≫ smallChainInclusion X A B
      rw [Category.id_comp, smallChainInclusionA_comp_ι])
    (comm₂₃ := by
      show smallChainInclusion X A B ≫ cokernel.π (subspaceChainInclusion X A) =
        cokernel.π (smallChainInclusionA X A B) ≫ cokernel.map _ _ (𝟙 _) _ _
      rw [cokernel.π_desc])

/-- For a fixed abelian group `R`, the constant-coefficient `J ↦ ⊕_J R` functor sends
injective functions to monomorphisms. (Split mono when `J` is nonempty; zero object when
empty.) -/
lemma sigmaConst_map_mono_of_injective
    (J K : Type) (f : J → K) (hf : Function.Injective f)
    (R : AddCommGrpCat) :
    Mono ((sigmaConst.obj R).map (show J ⟶ K from f)) := by
  by_cases hJ : Nonempty J
  · exact (⟨Function.invFun f, Function.invFun_comp hf⟩ :
      SplitMono (show J ⟶ K from f)).map (sigmaConst.obj R) |>.mono
  · rw [not_nonempty_iff] at hJ
    exact (show IsZero ((sigmaConst.obj R).obj J) by
      rw [IsZero.iff_id_eq_zero]
      apply Sigma.hom_ext
      intro j; exact (hJ.false j).elim).mono _

/-- The total singular simplicial set functor `TopCat ⥤ SSet` preserves monomorphisms: an
injective continuous map is sent to a degreewise-injective map of simplicial sets. -/
instance toSSet_preservesMono : TopCat.toSSet.{0}.PreservesMonomorphisms where
  preserves {X Y} f hf := by
    rw [NatTrans.mono_iff_mono_app]
    intro n; rw [mono_iff_injective]
    intro σ₁ σ₂ h
    simp only [TopCat.toSSet, Presheaf.restrictedULiftYoneda, Functor.comp_map,
      Functor.whiskeringLeft, uliftYoneda] at h
    dsimp [Functor.whiskerLeft, yoneda, uliftFunctor] at h
    have h' : σ₁.down ≫ f = σ₂.down ≫ f := by
      have := congr_arg ULift.down h; simp at this; exact this
    exact ULift.ext _ _ ((cancel_mono f).mp h')

/-- The singular chain functor `C_*(-; ℤ) : TopCat ⥤ ChainComplex AddCommGrp` preserves
monomorphisms. -/
instance singularChainZ_preservesMono : singularChainZ.PreservesMonomorphisms where
  preserves {X Y} f hf := by
    apply HomologicalComplex.mono_of_mono_f
    intro i
    change Mono ((sigmaConst.obj (AddCommGrpCat.of ℤ)).map
      ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk i))))
    apply sigmaConst_map_mono_of_injective
    haveI : Mono (TopCat.toSSet.map f) := Functor.map_mono TopCat.toSSet f
    have hmono_app : Mono ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk i))) :=
      (NatTrans.mono_iff_mono_app (TopCat.toSSet.map f)).mp this _
    exact (mono_iff_injective _).mp hmono_app


/-- The chain inclusion `C_*(A) ↪ C_*(X)` induced by `A ↪ X` is a monomorphism. -/
instance subspaceChainInclusion_mono (X : Type) [TopologicalSpace X] (A : Set X) :
    Mono (subspaceChainInclusion X A) := by
  unfold subspaceChainInclusion
  haveI : Mono (subspaceTopInclusion A) := by
    rw [TopCat.mono_iff_injective]; exact Subtype.val_injective
  exact Functor.map_mono singularChainZ (subspaceTopInclusion A)

attribute [instance] subspaceChainInclusion_mono

/-- The map `C_*(A) → C^{\{A, B\}}_*(X)` is a monomorphism. -/
instance smallChainInclusionA_mono (X : Type) [TopologicalSpace X] (A B : Set X) :
    Mono (smallChainInclusionA X A B) :=
  mono_of_mono_fac (smallChainInclusionA_comp_ι X A B)

/-- The first map in `topSES X A B` is a monomorphism. -/
instance topSES_mono_f (X : Type) [TopologicalSpace X] (A B : Set X) :
    Mono (topSES X A B).f := smallChainInclusionA_mono X A B

/-- The second map in `topSES X A B` is an epimorphism (as a cokernel projection). -/
instance topSES_epi_g (X : Type) [TopologicalSpace X] (A B : Set X) :
    Epi (topSES X A B).g := by
  show Epi (cokernel.π (smallChainInclusionA X A B))
  infer_instance

/-- The short complex `topSES X A B` is short-exact. -/
lemma topSES_shortExact (X : Type) [TopologicalSpace X] (A B : Set X) :
    (topSES X A B).ShortExact :=
  { exact := ShortComplex.exact_cokernel _ }

/-- The first map in `bottomSES X A` is a monomorphism. -/
instance bottomSES_mono_f (X : Type) [TopologicalSpace X] (A : Set X) :
    Mono (bottomSES X A).f := subspaceChainInclusion_mono X A

/-- The second map in `bottomSES X A` is an epimorphism (as a cokernel projection). -/
instance bottomSES_epi_g (X : Type) [TopologicalSpace X] (A : Set X) :
    Epi (bottomSES X A).g := by
  show Epi (cokernel.π (subspaceChainInclusion X A))
  infer_instance

/-- The short complex `bottomSES X A` is short-exact. -/
lemma bottomSES_shortExact (X : Type) [TopologicalSpace X] (A : Set X) :
    (bottomSES X A).ShortExact :=
  { exact := ShortComplex.exact_cokernel _ }

set_option maxHeartbeats 800000 in
/-- **Third isomorphism theorem (short-exact form).** *Given monomorphisms `f : A ↪ B` and
`g : B ↪ C` with `f ≫ g` also mono (which is automatic), the sequence*
`0 → B / A → C / A → C / B → 0` *is short-exact.* -/
theorem thirdIso_shortExact
    {A B C : ChainComplex AddCommGrpCat ℕ}
    (f : A ⟶ B) (g : B ⟶ C) [Mono f] [Mono g] [Mono (f ≫ g)] :
    (ShortComplex.mk
      (cokernel.map f (f ≫ g) (𝟙 A) g (by simp))
      (cokernel.map (f ≫ g) g f (𝟙 C) (by simp))
      (by apply (cancel_epi (cokernel.π f)).mp
          simp only [comp_zero, cokernel.π_desc_assoc, Category.assoc, cokernel.π_desc,
            Category.id_comp, cokernel.condition])).ShortExact where
  exact := (kernelCokernelCompSequence_exact f g).exact 3
  mono_f := by
    have sq : IsPullback f (𝟙 A) g (f ≫ g) :=
      IsPullback.of_vert_isIso_mono ⟨by simp⟩
    exact Abelian.mono_cokernel_map_of_isPullback sq
  epi_g := by
    suffices h : Epi (cokernel.π (f ≫ g) ≫ cokernel.map (f ≫ g) g f (𝟙 C) (by simp)) from
      epi_of_epi (cokernel.π (f ≫ g)) _
    rw [cokernel.π_desc]
    infer_instance

section SecondIsoAbstract

variable {𝒞 : Type*} [Category 𝒞] [Abelian 𝒞]
  {𝒜 ℬ 𝒳 : 𝒞} (φ : 𝒜 ⟶ 𝒳) (ψ : ℬ ⟶ 𝒳)

set_option linter.unusedSectionVars false in
/-- Compatibility condition exhibiting the kernel of `[φ, ψ] : 𝒜 ⊕ ℬ → 𝒳` as a span over `𝒳`
via the negated first projection and the second projection. Auxiliary lemma for the
abstract second isomorphism theorem. -/
lemma secondIso_kernel_pullback_cond :
    (-(kernel.ι (biprod.desc φ ψ) ≫ biprod.fst (X := 𝒜) (Y := ℬ))) ≫ φ =
    (kernel.ι (biprod.desc φ ψ) ≫ biprod.snd (X := 𝒜) (Y := ℬ)) ≫ ψ := by
  have h := kernel.condition (biprod.desc φ ψ)
  rw [show kernel.ι (biprod.desc φ ψ) = biprod.lift
    (kernel.ι (biprod.desc φ ψ) ≫ biprod.fst) (kernel.ι (biprod.desc φ ψ) ≫ biprod.snd) from
    by apply biprod.hom_ext <;> simp, biprod.lift_desc] at h
  rw [Preadditive.neg_comp]; exact neg_eq_of_add_eq_zero_right h

set_option linter.unusedSectionVars false in
/-- Vanishing condition needed to factor the cokernel of `pullback.snd` through the
cokernel of `biprod.inl ∘ factorThruImage`. Used in constructing the forward map of the
abstract second isomorphism theorem. -/
lemma secondIso_fwd_cond :
    pullback.snd φ ψ ≫ (biprod.inr ≫ factorThruImage (biprod.desc φ ψ) ≫
      cokernel.π (biprod.inl ≫ factorThruImage (biprod.desc φ ψ))) = 0 := by
  have h : pullback.fst φ ψ ≫ biprod.inl ≫ factorThruImage (biprod.desc φ ψ) =
    pullback.snd φ ψ ≫ biprod.inr ≫ factorThruImage (biprod.desc φ ψ) := by
    apply (cancel_mono (Limits.image.ι (biprod.desc φ ψ))).mp
    simp only [Category.assoc, image.fac, biprod.inl_desc, biprod.inr_desc]; exact pullback.condition
  have key : (pullback.snd φ ψ ≫ biprod.inr ≫ factorThruImage (biprod.desc φ ψ)) ≫
    cokernel.π (biprod.inl ≫ factorThruImage (biprod.desc φ ψ)) = 0 := by
    rw [← h]; simp only [Category.assoc, cokernel.condition, comp_zero]
  simp only [Category.assoc] at key ⊢; exact key

set_option linter.unusedSectionVars false in
/-- Vanishing condition: the kernel of `[φ, ψ]` projected to the `ℬ` factor lands in the
image of `pullback.snd`, hence its image in `coker(pullback.snd)` vanishes. -/
lemma secondIso_kernel_kills_snd_cokernel :
    kernel.ι (biprod.desc φ ψ) ≫ biprod.snd (X := 𝒜) (Y := ℬ) ≫
    cokernel.π (pullback.snd (f := φ) (g := ψ)) = 0 := by
  rw [reassoc_of% (show kernel.ι (biprod.desc φ ψ) ≫ biprod.snd (X := 𝒜) (Y := ℬ) =
    (pullback.lift (-(kernel.ι (biprod.desc φ ψ) ≫ biprod.fst))
      (kernel.ι (biprod.desc φ ψ) ≫ biprod.snd)
      (secondIso_kernel_pullback_cond φ ψ)) ≫ pullback.snd φ ψ from by simp [pullback.lift_snd]),
    cokernel.condition, comp_zero]

/-- The induced map `coim([φ, ψ]) → coker(pullback.snd)` from the coimage of the biproduct
map to the cokernel of the pullback projection. -/
def secondIso_coimToCokerPS :
    Abelian.coimage (biprod.desc φ ψ) ⟶ cokernel (pullback.snd (f := φ) (g := ψ)) :=
  cokernel.desc _ (biprod.snd ≫ cokernel.π (pullback.snd (f := φ) (g := ψ)))
    (secondIso_kernel_kills_snd_cokernel φ ψ)

/-- The induced map `image([φ, ψ]) → coker(pullback.snd)`, obtained from
`secondIso_coimToCokerPS` via the canonical iso `image ≅ coimage` in an abelian category. -/
def secondIso_imgToCokerPS :
    Limits.image (biprod.desc φ ψ) ⟶ cokernel (pullback.snd (f := φ) (g := ψ)) :=
  (Abelian.coimageIsoImage' (biprod.desc φ ψ)).inv ≫ secondIso_coimToCokerPS φ ψ

/-- Vanishing condition needed to descend `secondIso_imgToCokerPS` to a map out of the
cokernel `coker(biprod.inl ∘ factorThruImage)`. -/
lemma secondIso_inv_kills_inclA :
    (biprod.inl ≫ factorThruImage (biprod.desc φ ψ)) ≫ secondIso_imgToCokerPS φ ψ = 0 := by
  simp only [secondIso_imgToCokerPS, secondIso_coimToCokerPS, Category.assoc,
    ← Category.assoc (factorThruImage _), Abelian.factorThruImage_comp_coimageIsoImage'_inv,
    cokernel.π_desc, biprod.inl_snd_assoc, zero_comp]

/-- Forward direction of the abstract second isomorphism: a map from `coker(pullback.snd)`
to `coker(biprod.inl ∘ factorThruImage)`, induced by the inclusion of `ℬ` into the
biproduct. -/
def secondIso_fwd :
    cokernel (pullback.snd (f := φ) (g := ψ)) ⟶
    cokernel (biprod.inl ≫ factorThruImage (biprod.desc φ ψ)) :=
  cokernel.desc _ (biprod.inr ≫ factorThruImage (biprod.desc φ ψ) ≫
    cokernel.π (biprod.inl ≫ factorThruImage (biprod.desc φ ψ))) (secondIso_fwd_cond φ ψ)

/-- Inverse direction of the abstract second isomorphism: the descent of
`secondIso_imgToCokerPS` from the image to `coker(biprod.inl ∘ factorThruImage)`. -/
def secondIso_inv :
    cokernel (biprod.inl ≫ factorThruImage (biprod.desc φ ψ)) ⟶
    cokernel (pullback.snd (f := φ) (g := ψ)) :=
  cokernel.desc _ (secondIso_imgToCokerPS φ ψ) (secondIso_inv_kills_inclA φ ψ)

set_option linter.unusedSectionVars false in
/-- The composition `secondIso_fwd ≫ secondIso_inv` is the identity. One half of the
isomorphism claim. -/
lemma secondIso_fwd_inv_id :
    secondIso_fwd φ ψ ≫ secondIso_inv φ ψ = 𝟙 _ := by
  apply (cancel_epi (cokernel.π (pullback.snd (f := φ) (g := ψ)))).mp
  simp only [secondIso_fwd, secondIso_inv, cokernel.π_desc_assoc, Category.comp_id]
  simp only [secondIso_imgToCokerPS, secondIso_coimToCokerPS, Category.assoc,
    ← Category.assoc (factorThruImage _), Abelian.factorThruImage_comp_coimageIsoImage'_inv,
    cokernel.π_desc]
  simp

set_option linter.unusedSectionVars false in
/-- The composition `secondIso_inv ≫ secondIso_fwd` is the identity. The other half of the
isomorphism claim. -/
lemma secondIso_inv_fwd_id :
    secondIso_inv φ ψ ≫ secondIso_fwd φ ψ = 𝟙 _ := by
  apply (cancel_epi (cokernel.π (biprod.inl ≫ factorThruImage (biprod.desc φ ψ)))).mp
  simp only [secondIso_inv, secondIso_fwd, cokernel.π_desc_assoc, Category.comp_id]
  apply (cancel_epi (factorThruImage (biprod.desc φ ψ))).mp
  simp only [secondIso_imgToCokerPS, secondIso_coimToCokerPS, Category.assoc,
    ← Category.assoc (factorThruImage _), Abelian.factorThruImage_comp_coimageIsoImage'_inv,
    cokernel.π_desc_assoc, cokernel.π_desc]


  have h_fst_zero : biprod.fst (X := 𝒜) (Y := ℬ) ≫ biprod.inl ≫ factorThruImage (biprod.desc φ ψ) ≫
    cokernel.π (biprod.inl ≫ factorThruImage (biprod.desc φ ψ)) = 0 := by
    have h : biprod.inl (X := 𝒜) (Y := ℬ) ≫ factorThruImage (biprod.desc φ ψ) ≫
      cokernel.π (biprod.inl ≫ factorThruImage (biprod.desc φ ψ)) = 0 := by
      rw [← Category.assoc]; exact cokernel.condition _
    simp only [h, comp_zero]
  have h_total := congr_arg (· ≫ factorThruImage (biprod.desc φ ψ) ≫
    cokernel.π (biprod.inl ≫ factorThruImage (biprod.desc φ ψ))) (biprod.total (X := 𝒜) (Y := ℬ))
  simp only [Preadditive.add_comp, Category.assoc, Category.id_comp] at h_total
  rw [h_fst_zero, zero_add] at h_total
  exact h_total

/-- **Abstract second isomorphism theorem.** *For morphisms `φ : 𝒜 → 𝒳` and `ψ : ℬ → 𝒳` in
an abelian category, there is a canonical isomorphism*
$$(\mathcal{A} + \mathcal{B}) / \mathcal{A} \;\cong\; \mathcal{B} / (\mathcal{A} \cap \mathcal{B}),$$
*where `𝒜 + ℬ` is the image of `[φ, ψ] : 𝒜 ⊕ ℬ → 𝒳` and `𝒜 ∩ ℬ` is the pullback of `φ`
along `ψ`.* -/
def secondIsoOfMorphisms :
    cokernel (biprod.inl (X := 𝒜) (Y := ℬ) ≫ factorThruImage (biprod.desc φ ψ)) ≅
    cokernel (pullback.snd (f := φ) (g := ψ)) where
  hom := secondIso_inv φ ψ
  inv := secondIso_fwd φ ψ
  hom_inv_id := secondIso_inv_fwd_id φ ψ
  inv_hom_id := secondIso_fwd_inv_id φ ψ

end SecondIsoAbstract


/-- The concrete forward map for the second isomorphism applied to chain complexes:
`C^{\{A, B\}}_*(X) → C_*(B, A ∩ B)`. -/
noncomputable def secondIsomorphismIso_fwdMap (X : Type) [TopologicalSpace X] (A B : Set X) :
    smallChainComplex X A B ⟶ relativeSingularChainComplex (↥B) (Subtype.val ⁻¹' A) := by sorry


/-- The forward map vanishes on `C_*(A)`, so it descends to a map from the cokernel
`C^{\{A, B\}}_*(X) / C_*(A)`. -/
theorem secondIsomorphismIso_fwdMap_comp (X : Type) [TopologicalSpace X] (A B : Set X) :
    smallChainInclusionA X A B ≫ secondIsomorphismIso_fwdMap X A B = 0 := by sorry


/-- The concrete inverse map for the second isomorphism:
`C_*(B, A ∩ B) → C^{\{A, B\}}_*(X) / C_*(A)`. -/
noncomputable def secondIsomorphismIso_invMap (X : Type) [TopologicalSpace X] (A B : Set X) :
    relativeSingularChainComplex (↥B) (Subtype.val ⁻¹' A) ⟶ cokernel (smallChainInclusionA X A B) := by sorry


/-- Hom-inv identity for the second isomorphism isomorphism of chain complexes. -/
theorem secondIsomorphismIso_hom_inv (X : Type) [TopologicalSpace X] (A B : Set X) :
    cokernel.desc _ (secondIsomorphismIso_fwdMap X A B) (secondIsomorphismIso_fwdMap_comp X A B) ≫
      secondIsomorphismIso_invMap X A B = 𝟙 _ := by sorry


/-- Inv-hom identity for the second isomorphism isomorphism of chain complexes. -/
theorem secondIsomorphismIso_inv_hom (X : Type) [TopologicalSpace X] (A B : Set X) :
    secondIsomorphismIso_invMap X A B ≫
      cokernel.desc _ (secondIsomorphismIso_fwdMap X A B) (secondIsomorphismIso_fwdMap_comp X A B) = 𝟙 _ := by sorry

/-- **Second isomorphism (concrete form for singular chains).**
*The cokernel `C^{\{A, B\}}_*(X) / C_*(A)` is canonically isomorphic to the relative chain
complex `C_*(B, A ∩ B)`.* -/
def secondIsomorphismIso (X : Type) [TopologicalSpace X] (A : Set X) (B : Set X) :
    cokernel (smallChainInclusionA X A B) ≅
      relativeSingularChainComplex (B : Set X) (Subtype.val ⁻¹' A) where
  hom := cokernel.desc _ (secondIsomorphismIso_fwdMap X A B) (secondIsomorphismIso_fwdMap_comp X A B)
  inv := secondIsomorphismIso_invMap X A B
  hom_inv_id := secondIsomorphismIso_hom_inv X A B
  inv_hom_id := secondIsomorphismIso_inv_hom X A B


/-- Compatibility between the second-isomorphism forward map and the excision chain map:
both factor a chain in the small complex through the relative complex `C_*(X, A)`. -/
theorem secondIsomorphismIso_fwdMap_comp_excision (X : Type) [TopologicalSpace X] (A U : Set X) :
    secondIsomorphismIso_fwdMap X A Uᶜ ≫ excisionRelativeChainMap X A U =
    smallChainInclusion X A Uᶜ ≫ cokernel.π (subspaceChainInclusion X A) := by sorry

/-- Pre-composition of `secondIsomorphismIso_fwdMap_comp_excision` with the cokernel
projection, in the form needed to identify `(excisionSESMorphism).τ₃` with the excision
chain map. -/
theorem secondIsomorphismIso_hom_comp (X : Type) [TopologicalSpace X] (A U : Set X) :
    cokernel.π (smallChainInclusionA X A Uᶜ) ≫
      (secondIsomorphismIso X A Uᶜ).hom ≫ excisionRelativeChainMap X A U =
    smallChainInclusion X A Uᶜ ≫ cokernel.π (subspaceChainInclusion X A) := by
  simp only [secondIsomorphismIso, cokernel.π_desc_assoc]
  exact secondIsomorphismIso_fwdMap_comp_excision X A U

/-- The right-most map `τ₃` in the morphism of short exact sequences `excisionSESMorphism`
agrees, up to the second-isomorphism identification, with the excision chain map. -/
theorem excisionSESMorphism_τ₃_comm (X : Type) [TopologicalSpace X] (A U : Set X) :
    (excisionSESMorphism X A Uᶜ).τ₃ =
    (secondIsomorphismIso X A Uᶜ).hom ≫ excisionRelativeChainMap X A U ≫
    (Iso.refl _).inv := by
  simp only [Iso.refl_inv, Category.comp_id]
  have h1 : cokernel.π (smallChainInclusionA X A Uᶜ) ≫
      (secondIsomorphismIso X A Uᶜ).hom ≫ excisionRelativeChainMap X A U =
    smallChainInclusion X A Uᶜ ≫ cokernel.π (subspaceChainInclusion X A) :=
    secondIsomorphismIso_hom_comp X A U
  have h2 : cokernel.π (smallChainInclusionA X A Uᶜ) ≫
      (excisionSESMorphism X A Uᶜ).τ₃ =
    smallChainInclusion X A Uᶜ ≫ cokernel.π (subspaceChainInclusion X A) :=
    cokernel.π_desc _ _ _
  exact (cancel_epi (cokernel.π (smallChainInclusionA X A Uᶜ))).mp (h2.trans h1.symm)

/-- Pointwise version of the excision theorem at the chain level: for an excisive triple
`(X, A, U)`, the excision chain map is a quasi-isomorphism in every degree `n`. -/
theorem excisionRelativeChainMap_quasiIsoAt {X : Type} [TopologicalSpace X] {A U : Set X}
    (hexc : IsExcisive X A U) (n : ℕ) :
    QuasiIsoAt (excisionRelativeChainMap X A U) n := by

  have hcover := cover_of_excisive hexc
  have hqi_middle : QuasiIso (smallChainInclusion X A Uᶜ) :=
    localityPrinciple X A Uᶜ hcover

  have hqi_cokernel : QuasiIso (excisionSESMorphism X A Uᶜ).τ₃ := by
    apply HomologicalComplex.HomologySequence.quasiIso_τ₃
      (excisionSESMorphism X A Uᶜ)
      (topSES_shortExact X A Uᶜ)
      (bottomSES_shortExact X A)
    · show QuasiIso (𝟙 _); infer_instance
    · show QuasiIso (smallChainInclusion X A Uᶜ); exact hqi_middle

  rw [quasiIsoAt_iff_isIso_homologyMap]

  have hτ₃_eq := excisionSESMorphism_τ₃_comm X A U

  have h_iso_τ₃ : IsIso (HomologicalComplex.homologyMap (excisionSESMorphism X A Uᶜ).τ₃ n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mp (hqi_cokernel.quasiIsoAt n)

  rw [hτ₃_eq] at h_iso_τ₃
  simp only [HomologicalComplex.homologyMap_comp, Iso.refl_inv,
    HomologicalComplex.homologyMap_id] at h_iso_τ₃

  simp only [Category.comp_id] at h_iso_τ₃

  haveI : IsIso (HomologicalComplex.homologyMap (secondIsomorphismIso X A Uᶜ).hom n) := by
    exact (quasiIsoAt_iff_isIso_homologyMap _ _).mp
      ((quasiIso_of_isIso (secondIsomorphismIso X A Uᶜ).hom).quasiIsoAt n)


  haveI : IsIso (HomologicalComplex.homologyMap (secondIsomorphismIso X A Uᶜ).hom n ≫
      HomologicalComplex.homologyMap (excisionRelativeChainMap X A U) n) := by
    rwa [← HomologicalComplex.homologyMap_comp]
  exact IsIso.of_isIso_comp_left
    (HomologicalComplex.homologyMap (secondIsomorphismIso X A Uᶜ).hom n)
    (HomologicalComplex.homologyMap (excisionRelativeChainMap X A U) n)

end

end Excision

/-- **Theorem 10.2 (Excision).** *Let `(X, A, U)` be an excisive triple, meaning
`closure U ⊆ interior A`. Then for every `n`, the pair inclusion*
$$(X \setminus U,\; A \setminus U) \hookrightarrow (X, A)$$
*induces an isomorphism on relative singular homology*
$$H_n(X \setminus U,\; A \setminus U;\, \mathbb{Z}) \;\xrightarrow{\sim}\; H_n(X, A;\, \mathbb{Z}).$$

Proved by passing to small chains via the locality principle and the second isomorphism. -/
theorem excision_theorem {X : Type} [TopologicalSpace X] {A U : Set X}
    (hexc : IsExcisive X A U) (n : ℕ) :
    IsIso (Excision.excisionHomologyMap X A U n) := by
  have hqi := Excision.excisionRelativeChainMap_quasiIsoAt hexc n
  rwa [quasiIsoAt_iff_isIso_homologyMap] at hqi

namespace SphereHomology

/-- The `n`-sphere `S^n = \{x \in \mathbb{R}^{n+1} : \|x\| = 1\}`. -/
def Sphere (n : ℕ) : Type :=
  ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/-- The subspace topology on `Sphere n`. -/
instance Sphere.instTopologicalSpace (n : ℕ) : TopologicalSpace (Sphere n) :=
  instTopologicalSpaceSubtype

/-- The closed `n`-disk `D^n = \{x \in \mathbb{R}^n : \|x\| \le 1\}`. -/
def Disk (n : ℕ) : Type :=
  ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)

/-- The subspace topology on `Disk n`. -/
instance Disk.instTopologicalSpace (n : ℕ) : TopologicalSpace (Disk n) :=
  instTopologicalSpaceSubtype

/-- The boundary `∂D^n = S^{n-1}` of the `n`-disk, as a stand-alone type. -/
def DiskBoundary (n : ℕ) : Type :=
  ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)

/-- The boundary `∂D^n ⊆ D^n` as a subset of the `n`-disk. -/
def diskBoundarySubset (n : ℕ) : Set (Disk n) :=
  {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1}

open AlgebraicTopology

noncomputable section


/-- Local copy of `singularChainZ` in the `SphereHomology` namespace: the integer singular
chain complex functor `X ↦ C_*(X; ℤ)`. -/
abbrev singularChainZF : TopCat.{0} ⥤ ChainComplex AddCommGrpCat ℕ :=
  (singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)


/-- Local copy of `sigmaConst_map_mono_of_injective` in the `SphereHomology` namespace. -/
lemma sigmaConst_map_mono_of_injective'
    (J K : Type) (f : J → K) (hf : Function.Injective f) (R : AddCommGrpCat) :
    Mono ((sigmaConst.obj R).map (show J ⟶ K from f)) := by
  by_cases hJ : Nonempty J
  · exact (⟨Function.invFun f, Function.invFun_comp hf⟩ :
      SplitMono (show J ⟶ K from f)).map (sigmaConst.obj R) |>.mono
  · rw [not_nonempty_iff] at hJ
    exact (show IsZero ((sigmaConst.obj R).obj J) by
      rw [IsZero.iff_id_eq_zero]; apply Sigma.hom_ext
      intro j; exact (hJ.false j).elim).mono _

/-- Local copy of `toSSet_preservesMono` in the `SphereHomology` namespace. -/
instance toSSet_preservesMono' : TopCat.toSSet.{0}.PreservesMonomorphisms where
  preserves {X Y} f hf := by
    rw [NatTrans.mono_iff_mono_app]
    intro n; rw [mono_iff_injective]
    intro σ₁ σ₂ h
    simp only [TopCat.toSSet, Presheaf.restrictedULiftYoneda, Functor.comp_map,
      Functor.whiskeringLeft, uliftYoneda] at h
    dsimp [Functor.whiskerLeft, yoneda, uliftFunctor] at h
    have h' : σ₁.down ≫ f = σ₂.down ≫ f := by
      have := congr_arg ULift.down h; simp at this; exact this
    exact ULift.ext _ _ ((cancel_mono f).mp h')

/-- The `singularChainZF` functor preserves monomorphisms. -/
instance singularChainZ_preserves_mono : singularChainZF.PreservesMonomorphisms where
  preserves {X Y} f hf := by
    apply HomologicalComplex.mono_of_mono_f
    intro i
    change Mono ((sigmaConst.obj (AddCommGrpCat.of ℤ)).map
      ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk i))))
    apply sigmaConst_map_mono_of_injective'
    haveI : Mono (TopCat.toSSet.map f) := Functor.map_mono TopCat.toSSet f
    have hmono_app : Mono ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk i))) :=
      (NatTrans.mono_iff_mono_app (TopCat.toSSet.map f)).mp this _
    exact (mono_iff_injective _).mp hmono_app


/-- The chain-level inclusion `C_*(A) → C_*(X)` for a subspace `A ⊆ X` (local copy of
`subspaceChainInclusion` in the `SphereHomology` namespace). -/
def inclChain (X : Type) [TopologicalSpace X] (A : Set X) :
    singularChainZF.obj (TopCat.of A) ⟶ singularChainZF.obj (TopCat.of X) :=
  singularChainZF.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)


/-- The topological inclusion `A ↪ X` is a monomorphism in `TopCat`. -/
instance inclTopMono {X : Type} [TopologicalSpace X] (A : Set X) :
    Mono (TopCat.ofHom (⟨(Subtype.val : A → X), continuous_subtype_val⟩ : C(A, X))) := by
  rw [TopCat.mono_iff_injective]; exact Subtype.val_injective


/-- The chain-level inclusion `inclChain` is a monomorphism. -/
instance inclChainMono (X : Type) [TopologicalSpace X] (A : Set X) :
    Mono (inclChain X A) := by
  haveI := singularChainZ_preserves_mono
  exact Functor.PreservesMonomorphisms.preserves _


/-- The pair short exact sequence `0 → C_*(A) → C_*(X) → C_*(X)/C_*(A) → 0`. -/
def pairSES (X : Type) [TopologicalSpace X] (A : Set X) :
    ShortComplex (ChainComplex AddCommGrpCat ℕ) :=
  ShortComplex.mk (inclChain X A) (cokernel.π (inclChain X A)) (cokernel.condition _)

/-- The left map of the pair short exact sequence is a monomorphism. -/
instance pairSES_f_mono (X : Type) [TopologicalSpace X] (A : Set X) :
    Mono (pairSES X A).f := inclChainMono X A

/-- The right map of the pair short exact sequence is an epimorphism. -/
instance pairSES_g_epi (X : Type) [TopologicalSpace X] (A : Set X) :
    Epi (pairSES X A).g := by
  change Epi (cokernel.π (inclChain X A))
  infer_instance

/-- The pair sequence is short exact. -/
def pairSES_shortExact (X : Type) [TopologicalSpace X] (A : Set X) :
    (pairSES X A).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)


/-- The boundary-map isomorphism in the pair long exact sequence under vanishing of the
homology of `C_*(X)` in two adjacent degrees: `H_{q+1}(X, A) ≅ H_q(A)`. -/
noncomputable def pairδIso (X : Type) [TopologicalSpace X] (A : Set X)
    (q : ℕ)
    (hi : IsZero ((pairSES X A).X₂.homology (q + 1)))
    (hj : IsZero ((pairSES X A).X₂.homology q)) :
    (pairSES X A).X₃.homology (q + 1) ≅ (pairSES X A).X₁.homology q :=
  (pairSES_shortExact X A).δIso (q + 1) q (by rw [ComplexShape.down_Rel]) hi hj


/-- The homology `H_k(X; ℤ)` of a contractible space `X` vanishes for `k ≠ 0`. -/
lemma isZero_SHG_contractible (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] (k : ℕ) (hk : k ≠ 0) :
    IsZero ((singularChainZF.obj (TopCat.of X)).homology k) := by
  obtain ⟨x₀, ⟨Hx⟩⟩ := (contractible_iff_id_nullhomotopic X).mp ‹_›
  let F := singularChainZF ⋙ HomologicalComplex.homologyFunctor _ _ k
  have hmap : F.map (𝟙 (TopCat.of X)) = F.map (TopCat.ofHom (ContinuousMap.const X x₀)) := by
    show F.map (TopCat.ofHom (ContinuousMap.id X)) = _
    exact (show TopCat.Homotopy _ _ from Hx).congr_homologyMap_singularChainComplexFunctor
      (AddCommGrpCat.of ℤ) k
  rw [F.map_id] at hmap
  let p : TopCat.of X ⟶ TopCat.of PUnit := TopCat.ofHom ⟨fun _ => .unit, continuous_const⟩
  let q' : TopCat.of PUnit ⟶ TopCat.of X := TopCat.ofHom ⟨fun _ => x₀, continuous_const⟩
  have hfact : TopCat.ofHom (ContinuousMap.const X x₀) = p ≫ q' := by
    apply TopCat.hom_ext; apply ContinuousMap.ext; intro _; rfl
  rw [hfact, F.map_comp] at hmap
  have hpz : IsZero (F.obj (TopCat.of PUnit)) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ _ _ _ hk
  have : F.map p ≫ F.map q' = 0 := by
    rw [hpz.eq_of_src (F.map q') 0, comp_zero]
  rw [this] at hmap
  exact (IsZero.iff_id_eq_zero _).mpr hmap


/-- The natural identification `∂D^{n+2} ≅ S^{n+1}` between the boundary subspace and the
sphere of the appropriate dimension, as objects of `TopCat`. -/
noncomputable def bdryToSphereIso (n : ℕ) :
    TopCat.of ↥(diskBoundarySubset (n + 2)) ≅ TopCat.of (Sphere (n + 1)) where
  hom := TopCat.ofHom ⟨fun ⟨⟨x, _⟩, hsp⟩ => ⟨x, hsp⟩,
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _⟩
  inv := TopCat.ofHom ⟨fun ⟨x, hsp⟩ => ⟨⟨x, Metric.sphere_subset_closedBall hsp⟩, hsp⟩,
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _⟩
  hom_inv_id := by apply TopCat.hom_ext; apply ContinuousMap.ext; intro ⟨⟨_, _⟩, _⟩; rfl
  inv_hom_id := by apply TopCat.hom_ext; apply ContinuousMap.ext; intro ⟨_, _⟩; rfl

end


/-- Auxiliary form of `sphere_homology_top`: the top homology of `S^n` is `ℤ`, expressed in
terms of the `singularChainZF` complex. -/
theorem sphere_homology_top_aux (n : ℕ) (hn : n > 0) :
    Nonempty ((singularChainZF.obj (TopCat.of (Sphere n))).homology n ≅
      AddCommGrpCat.of ℤ) := by sorry


/-- **Base case** for the relative homology of the disk pair: `H_1(D^1, S^0) ≅ ℤ`. -/
theorem relative_homology_base :
    Nonempty (Excision.RelativeSingularHomologyGroup 1 (Disk 1) (diskBoundarySubset 1) ≅
      AddCommGrpCat.of ℤ) := by sorry

open Excision in
/-- **Top relative homology of the disk pair** (part of Proposition 10.4):
`H_n(D^n, S^{n-1}) ≅ ℤ` for `n > 0`. -/
theorem relative_homology_top (n : ℕ) (hn : n > 0) :
    Nonempty (RelativeSingularHomologyGroup n (Disk n) (diskBoundarySubset n) ≅
      AddCommGrpCat.of ℤ) := by


  obtain _ | _ | m := n
  · omega
  ·
    exact relative_homology_base
  ·
    haveI : ContractibleSpace (Disk (m + 2)) :=
      (convex_closedBall (0 : EuclideanSpace ℝ (Fin (m + 2))) 1).contractibleSpace ⟨0, by simp⟩
    have hD_hi : IsZero ((pairSES (Disk (m + 2)) (diskBoundarySubset (m + 2))).X₂.homology (m + 2)) :=
      isZero_SHG_contractible _ _ (by omega)
    have hD_lo : IsZero ((pairSES (Disk (m + 2)) (diskBoundarySubset (m + 2))).X₂.homology (m + 1)) :=
      isZero_SHG_contractible _ _ (by omega)
    have δiso := pairδIso (Disk (m + 2)) (diskBoundarySubset (m + 2)) (m + 1) hD_hi hD_lo
    have homIso := (HomologicalComplex.homologyFunctor _ _ (m + 1)).mapIso
      (singularChainZF.mapIso (bdryToSphereIso m))
    obtain ⟨sphIso⟩ := sphere_homology_top_aux (m + 1) (by omega)
    have hRelX3 : (pairSES (Disk (m + 2)) (diskBoundarySubset (m + 2))).X₃.homology (m + 2) =
        Excision.RelativeSingularHomologyGroup (m + 2) (Disk (m + 2)) (diskBoundarySubset (m + 2)) := rfl
    exact ⟨(eqToIso hRelX3).symm ≪≫ δiso ≪≫ homIso ≪≫ sphIso⟩

open Excision in
/-- **Vanishing of off-degree relative homology** (part of Proposition 10.4):
`H_q(D^n, S^{n-1}) = 0` for `q ≠ n`. -/
theorem relative_homology_vanishing (q n : ℕ) (hn : n > 0) (hqn : q ≠ n) :
    IsZero (Excision.RelativeSingularHomologyGroup q (Disk n) (diskBoundarySubset n)) := by sorry


open AlgebraicTopology in
/-- The singular chain functor used in the suspension-isomorphism proof preserves
monomorphisms. -/
noncomputable instance suspSingularChainZ_preserves_mono :
    ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ) :
      TopCat.{0} ⥤ ChainComplex AddCommGrpCat ℕ).PreservesMonomorphisms :=
  singularChainZ_preserves_mono

section SuspensionIsoProof

open AlgebraicTopology

noncomputable section


/-- Local copy of `singularChainZF` in the suspension-isomorphism proof. -/
abbrev suspSingularChainZF : TopCat.{0} ⥤ ChainComplex AddCommGrpCat ℕ :=
  (singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)

/-- Local copy of `inclChain` for the suspension-isomorphism proof. -/
noncomputable def suspInclChain (X : Type) [TopologicalSpace X] (A : Set X) :
    suspSingularChainZF.obj (TopCat.of A) ⟶ suspSingularChainZF.obj (TopCat.of X) :=
  suspSingularChainZF.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)

/-- Local copy of `inclTopMono` for the suspension-isomorphism proof. -/
instance suspInclTopMono {X : Type} [TopologicalSpace X] (A : Set X) :
    Mono (TopCat.ofHom (⟨(Subtype.val : A → X), continuous_subtype_val⟩ : C(A, X))) := by
  rw [TopCat.mono_iff_injective]; exact Subtype.val_injective

/-- Local copy of `inclChainMono` for the suspension-isomorphism proof. -/
instance suspInclChainMono (X : Type) [TopologicalSpace X] (A : Set X) :
    Mono (suspInclChain X A) := by
  haveI := suspSingularChainZ_preserves_mono
  exact Functor.PreservesMonomorphisms.preserves _

/-- Local copy of `pairSES` for the suspension-isomorphism proof. -/
def suspPairSES (X : Type) [TopologicalSpace X] (A : Set X) :
    ShortComplex (ChainComplex AddCommGrpCat ℕ) :=
  ShortComplex.mk (suspInclChain X A) (cokernel.π (suspInclChain X A)) (cokernel.condition _)

/-- Local copy of `pairSES_f_mono` for the suspension-isomorphism proof. -/
instance suspPairSES_f_mono (X : Type) [TopologicalSpace X] (A : Set X) :
    Mono (suspPairSES X A).f := suspInclChainMono X A

/-- Local copy of `pairSES_g_epi` for the suspension-isomorphism proof. -/
instance suspPairSES_g_epi (X : Type) [TopologicalSpace X] (A : Set X) :
    Epi (suspPairSES X A).g := by
  change Epi (cokernel.π (suspInclChain X A))
  infer_instance

/-- Local copy of `pairSES_shortExact` for the suspension-isomorphism proof. -/
def suspPairSES_shortExact (X : Type) [TopologicalSpace X] (A : Set X) :
    (suspPairSES X A).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)

/-- Local copy of `pairδIso` for the suspension-isomorphism proof. -/
noncomputable def suspPairδIso (X : Type) [TopologicalSpace X] (A : Set X)
    (q : ℕ)
    (hi : IsZero ((suspPairSES X A).X₂.homology (q + 1)))
    (hj : IsZero ((suspPairSES X A).X₂.homology q)) :
    (suspPairSES X A).X₃.homology (q + 1) ≅ (suspPairSES X A).X₁.homology q :=
  (suspPairSES_shortExact X A).δIso (q + 1) q (by rw [ComplexShape.down_Rel]) hi hj


/-- Local copy of `isZero_SHG_contractible` for the suspension-isomorphism proof. -/
lemma suspIsZero_SHG_contractible (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] (k : ℕ) (hk : k ≠ 0) :
    IsZero ((suspSingularChainZF.obj (TopCat.of X)).homology k) := by
  obtain ⟨x₀, ⟨Hx⟩⟩ := (contractible_iff_id_nullhomotopic X).mp ‹_›
  let F := suspSingularChainZF ⋙ HomologicalComplex.homologyFunctor _ _ k
  have hmap : F.map (𝟙 (TopCat.of X)) = F.map (TopCat.ofHom (ContinuousMap.const X x₀)) := by
    show F.map (TopCat.ofHom (ContinuousMap.id X)) = _
    exact (show TopCat.Homotopy _ _ from Hx).congr_homologyMap_singularChainComplexFunctor
      (AddCommGrpCat.of ℤ) k
  rw [F.map_id] at hmap
  let p : TopCat.of X ⟶ TopCat.of PUnit := TopCat.ofHom ⟨fun _ => .unit, continuous_const⟩
  let q' : TopCat.of PUnit ⟶ TopCat.of X := TopCat.ofHom ⟨fun _ => x₀, continuous_const⟩
  have hfact : TopCat.ofHom (ContinuousMap.const X x₀) = p ≫ q' := by
    apply TopCat.hom_ext; apply ContinuousMap.ext; intro _; rfl
  rw [hfact, F.map_comp] at hmap
  have hpz : IsZero (F.obj (TopCat.of PUnit)) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ _ _ _ hk
  have : F.map p ≫ F.map q' = 0 := by
    rw [hpz.eq_of_src (F.map q') 0, comp_zero]
  rw [this] at hmap
  exact (IsZero.iff_id_eq_zero _).mpr hmap


/-- Local copy of `bdryToSphereIso`: the identification `∂D^{n+1} ≅ S^n`. -/
noncomputable def suspBdryToSphereIso (n : ℕ) :
    TopCat.of ↥(diskBoundarySubset (n + 1)) ≅ TopCat.of (Sphere n) where
  hom := TopCat.ofHom ⟨fun ⟨⟨x, _⟩, hsp⟩ => ⟨x, hsp⟩,
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _⟩
  inv := TopCat.ofHom ⟨fun ⟨x, hsp⟩ => ⟨⟨x, Metric.sphere_subset_closedBall hsp⟩, hsp⟩,
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _⟩
  hom_inv_id := by apply TopCat.hom_ext; apply ContinuousMap.ext; intro ⟨⟨_, _⟩, _⟩; rfl
  inv_hom_id := by apply TopCat.hom_ext; apply ContinuousMap.ext; intro ⟨_, _⟩; rfl

end

/-- **Suspension isomorphism for sphere homology.** For `q ≥ 1`, there is an isomorphism
`H_q(S^n) ≅ H_{q+1}(S^{n+1})`, obtained by chasing the pair long exact sequences of
`(D^{n+1}, S^n)` and `(D^{n+2}, S^{n+1})` together with the known relative homology of
the disk pair. -/
theorem suspension_homology_iso (n q : ℕ) (hq : q ≥ 1) :
    Nonempty (SingularHomologyGroup q (Sphere n) ≅
             SingularHomologyGroup (q + 1) (Sphere (n + 1))) := by

  haveI hContr1 : ContractibleSpace (Disk (n + 1)) :=
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1).contractibleSpace ⟨0, by simp⟩
  haveI hContr2 : ContractibleSpace (Disk (n + 2)) :=
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin (n + 2))) 1).contractibleSpace ⟨0, by simp⟩


  have hD1_hi : IsZero ((suspPairSES (Disk (n + 1)) (diskBoundarySubset (n + 1))).X₂.homology (q + 1)) :=
    suspIsZero_SHG_contractible _ _ (by omega)
  have hD1_lo : IsZero ((suspPairSES (Disk (n + 1)) (diskBoundarySubset (n + 1))).X₂.homology q) :=
    suspIsZero_SHG_contractible _ _ (by omega)

  have δ1 := suspPairδIso (Disk (n + 1)) (diskBoundarySubset (n + 1)) q hD1_hi hD1_lo

  have homIso1 := (HomologicalComplex.homologyFunctor _ _ q).mapIso
    (suspSingularChainZF.mapIso (suspBdryToSphereIso n))


  have hD2_hi : IsZero ((suspPairSES (Disk (n + 2)) (diskBoundarySubset (n + 2))).X₂.homology (q + 2)) :=
    suspIsZero_SHG_contractible _ _ (by omega)
  have hD2_lo : IsZero ((suspPairSES (Disk (n + 2)) (diskBoundarySubset (n + 2))).X₂.homology (q + 1)) :=
    suspIsZero_SHG_contractible _ _ (by omega)

  have δ2 := suspPairδIso (Disk (n + 2)) (diskBoundarySubset (n + 2)) (q + 1) hD2_hi hD2_lo

  have homIso2 := (HomologicalComplex.homologyFunctor _ _ (q + 1)).mapIso
    (suspSingularChainZF.mapIso (suspBdryToSphereIso (n + 1)))

  by_cases hqn : q = n
  ·
    subst hqn

    obtain ⟨relIso1⟩ := relative_homology_top (q + 1) (by omega)

    obtain ⟨relIso2⟩ := relative_homology_top (q + 2) (by omega)


    have hRelX3_1 : (suspPairSES (Disk (q + 1)) (diskBoundarySubset (q + 1))).X₃.homology (q + 1) =
        Excision.RelativeSingularHomologyGroup (q + 1) (Disk (q + 1)) (diskBoundarySubset (q + 1)) := by
      rfl
    have hRelX3_2 : (suspPairSES (Disk (q + 2)) (diskBoundarySubset (q + 2))).X₃.homology (q + 2) =
        Excision.RelativeSingularHomologyGroup (q + 2) (Disk (q + 2)) (diskBoundarySubset (q + 2)) := by
      rfl

    exact ⟨homIso1.symm ≪≫ δ1.symm ≪≫ eqToIso hRelX3_1 ≪≫ relIso1 ≪≫
           relIso2.symm ≪≫ (eqToIso hRelX3_2).symm ≪≫ δ2 ≪≫ homIso2⟩
  ·

    have hRel1 : IsZero (Excision.RelativeSingularHomologyGroup (q + 1) (Disk (n + 1))
        (diskBoundarySubset (n + 1))) :=
      relative_homology_vanishing (q + 1) (n + 1) (by omega) (by omega)
    have hRelX3_1 : IsZero ((suspPairSES (Disk (n + 1)) (diskBoundarySubset (n + 1))).X₃.homology (q + 1)) := by
      convert hRel1 using 2

    have hSn : IsZero (SingularHomologyGroup q (Sphere n)) := by
      have hBdry := hRelX3_1.of_iso δ1.symm
      exact hBdry.of_iso homIso1.symm


    have hRel2 : IsZero (Excision.RelativeSingularHomologyGroup (q + 2) (Disk (n + 2))
        (diskBoundarySubset (n + 2))) :=
      relative_homology_vanishing (q + 2) (n + 2) (by omega) (by omega)
    have hRelX3_2 : IsZero ((suspPairSES (Disk (n + 2)) (diskBoundarySubset (n + 2))).X₃.homology (q + 2)) := by
      convert hRel2 using 2

    have hSn1 : IsZero (SingularHomologyGroup (q + 1) (Sphere (n + 1))) := by
      have hBdry := hRelX3_2.of_iso δ2.symm
      exact hBdry.of_iso homIso2.symm

    exact ⟨hSn.iso hSn1⟩

end SuspensionIsoProof

/-- `S^0` is finite (it is just the two-point set `{-1, +1}`). -/
instance sphere_zero_finite : Finite (Sphere 0) := by
  show Finite ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)
  rw [Set.finite_coe_iff]
  let p1 : EuclideanSpace ℝ (Fin 1) := (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => (1 : ℝ))
  let p2 : EuclideanSpace ℝ (Fin 1) := (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => (-1 : ℝ))
  apply Set.Finite.subset (Set.Finite.insert p1 (Set.finite_singleton p2))
  intro x hx
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hn := EuclideanSpace.norm_eq x
  rw [hx] at hn
  simp only [Fin.sum_univ_one] at hn
  rw [Real.sqrt_sq (norm_nonneg _)] at hn
  have habsx : x.ofLp 0 = 1 ∨ x.ofLp 0 = -1 := by
    rw [Real.norm_eq_abs] at hn
    exact abs_eq (by norm_num : (1 : ℝ) ≥ 0) |>.mp hn.symm
  rcases habsx with h | h
  · left; ext i; fin_cases i; show x.ofLp 0 = _; rw [h]; simp [p1]
  · right; ext i; fin_cases i; show x.ofLp 0 = _; rw [h]; simp [p2]

/-- `S^0` is totally disconnected (discrete two-point space). -/
instance sphere_zero_totallyDisconnected : TotallyDisconnectedSpace (Sphere 0) := by
  haveI : T1Space (Sphere 0) := by
    show T1Space ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)
    infer_instance
  haveI : DiscreteTopology (Sphere 0) := Finite.instDiscreteTopology
  infer_instance

/-- For `q > 0`, the singular homology of `S^0` vanishes: `H_q(S^0) = 0`. -/
theorem sphere_zero_homology_vanishing (q : ℕ) (hq : q > 0) :
    IsZero (SingularHomologyGroup q (Sphere 0)) := by
  open AlgebraicTopology in
  exact isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ q _ _ (by omega)

open AlgebraicTopology CategoryTheory.Limits in
/-- **Zeroth homology of `S^0`.** Since `S^0` has two path components, `H_0(S^0) ≅ ℤ ⊕ ℤ`. -/
theorem sphere_zero_homology_zero :
    Nonempty (SingularHomologyGroup 0 (Sphere 0) ≅ AddCommGrpCat.of (ℤ × ℤ)) := by
  classical

  let step1 := singularHomologyFunctorZeroOfTotallyDisconnectedSpace
    AddCommGrpCat (AddCommGrpCat.of ℤ) (TopCat.of (Sphere 0))

  let f : Sphere 0 → AddCommGrpCat.{0} := fun _ => AddCommGrpCat.of ℤ
  let step2 := (biproduct.isoCoproduct f).symm

  let step3 := AddCommGrpCat.biproductIsoPi f


  have hp1 : (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => (1 : ℝ)) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, EuclideanSpace.norm_eq,
        Fin.sum_univ_one]
    simp [Real.sqrt_sq_eq_abs]
  have hp2 : (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => (-1 : ℝ)) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, EuclideanSpace.norm_eq,
        Fin.sum_univ_one]
    simp [Real.sqrt_sq_eq_abs]
  let p1 : Sphere 0 := ⟨(EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => (1 : ℝ)), hp1⟩
  let p2 : Sphere 0 := ⟨(EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => (-1 : ℝ)), hp2⟩
  have hp1_ne_p2 : p1 ≠ p2 := by
    intro h
    have h' := Subtype.ext_iff.mp h
    have h'' := congr_arg (fun x : EuclideanSpace ℝ (Fin 1) => x 0) h'
    dsimp [p1, p2] at h''
    linarith
  have hcard : ∀ x : Sphere 0, x = p1 ∨ x = p2 := by
    intro ⟨x, hx⟩
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hx
    have hn := EuclideanSpace.norm_eq x
    rw [hx] at hn
    rw [Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _)] at hn
    have habsx : x.ofLp 0 = 1 ∨ x.ofLp 0 = -1 := by
      rw [Real.norm_eq_abs] at hn
      exact abs_eq (by norm_num : (1 : ℝ) ≥ 0) |>.mp hn.symm
    rcases habsx with h | h
    · left; apply Subtype.ext; ext i; fin_cases i; show x.ofLp 0 = _; rw [h]; simp [p1]
    · right; apply Subtype.ext; ext i; fin_cases i; show x.ofLp 0 = _; rw [h]; simp [p2]
  let piEquiv : (∀ _ : Sphere 0, ℤ) ≃+ ℤ × ℤ :=
    { toFun := fun g => (g p1, g p2)
      invFun := fun p x => if x = p1 then p.1 else p.2
      left_inv := by
        intro g; ext x
        rcases hcard x with rfl | rfl
        · simp
        · have : p2 ≠ p1 := Ne.symm hp1_ne_p2
          simp [this]
      right_inv := by
        intro ⟨a, b⟩
        have : p2 ≠ p1 := Ne.symm hp1_ne_p2
        simp [this]
      map_add' := fun _ _ => rfl }
  let step4 : AddCommGrpCat.of (∀ _ : Sphere 0, ℤ) ≅ AddCommGrpCat.of (ℤ × ℤ) :=
    piEquiv.toAddCommGrpIso
  exact ⟨step1 ≪≫ step2 ≪≫ step3 ≪≫ step4⟩

/-- **Proposition 10.4 (packaged).** The singular homology of spheres and the relative
homology of disk pairs: `H_n(S^n) = ℤ`, `H_0(S^n) = ℤ` for `n > 0`,
`H_0(S^0) = ℤ ⊕ ℤ`, otherwise zero; and `H_n(D^n, S^{n-1}) = ℤ`, otherwise zero. -/
structure SphereAndDiskHomology : Prop where
  sphere_top : ∀ (n : ℕ), n > 0 →
    Nonempty (SingularHomologyGroup n (Sphere n) ≅ AddCommGrpCat.of ℤ)
  sphere_zero : ∀ (n : ℕ), n > 0 →
    Nonempty (SingularHomologyGroup 0 (Sphere n) ≅ AddCommGrpCat.of ℤ)
  sphere_zero_zero :
    Nonempty (SingularHomologyGroup 0 (Sphere 0) ≅ AddCommGrpCat.of (ℤ × ℤ))
  sphere_vanishing : ∀ (q n : ℕ), n > 0 → q ≠ 0 → q ≠ n →
    IsZero (SingularHomologyGroup q (Sphere n))
  sphere_zero_vanishing : ∀ (q : ℕ), q > 0 →
    IsZero (SingularHomologyGroup q (Sphere 0))
  relative_top : ∀ (n : ℕ), n > 0 →
    Nonempty (Excision.RelativeSingularHomologyGroup n (Disk n) (diskBoundarySubset n) ≅
      AddCommGrpCat.of ℤ)
  relative_vanishing : ∀ (q n : ℕ), n > 0 → q ≠ n →
    IsZero (Excision.RelativeSingularHomologyGroup q (Disk n) (diskBoundarySubset n))


open AlgebraicTopology

section SuspensionVanishing

noncomputable section

/-- **Top homology of the sphere.** `H_n(S^n) ≅ ℤ` for `n > 0`. -/
theorem sphere_homology_top (n : ℕ) (hn : n > 0) :
    Nonempty (SingularHomologyGroup n (Sphere n) ≅ AddCommGrpCat.of ℤ) := by

  haveI : ContractibleSpace (Disk (n + 1)) :=
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1).contractibleSpace ⟨0, by simp⟩

  have hD_n1 : IsZero ((pairSES (Disk (n + 1)) (diskBoundarySubset (n + 1))).X₂.homology (n + 1)) :=
    isZero_SHG_contractible _ _ (by omega)
  have hD_n : IsZero ((pairSES (Disk (n + 1)) (diskBoundarySubset (n + 1))).X₂.homology n) :=
    isZero_SHG_contractible _ _ (by omega)

  have δiso := pairδIso (Disk (n + 1)) (diskBoundarySubset (n + 1)) n hD_n1 hD_n

  obtain ⟨relIso⟩ := relative_homology_top (n + 1) (by omega)

  have hRelMatch : (pairSES (Disk (n + 1)) (diskBoundarySubset (n + 1))).X₃.homology (n + 1) =
      Excision.RelativeSingularHomologyGroup (n + 1) (Disk (n + 1)) (diskBoundarySubset (n + 1)) := by
    rfl

  have bdryIso : (pairSES (Disk (n + 1)) (diskBoundarySubset (n + 1))).X₁.homology n ≅
      AddCommGrpCat.of ℤ :=
    δiso.symm ≪≫ (hRelMatch ▸ relIso)


  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have homIso := (HomologicalComplex.homologyFunctor _ _ (m + 1)).mapIso
    (singularChainZF.mapIso (bdryToSphereIso m))
  exact ⟨homIso.symm ≪≫ bdryIso⟩

end

/-- Inductive step for sphere-homology vanishing: if `H_q(S^n) = 0` for `q ≥ 1`, then
`H_{q+1}(S^{n+1}) = 0`. -/
theorem suspension_vanishing_step (q n : ℕ) (hq : q ≥ 1)
    (h : IsZero (SingularHomologyGroup q (Sphere n))) :
    IsZero (SingularHomologyGroup (q + 1) (Sphere (n + 1))) := by

  by_cases hqn : q = n
  ·

    subst hqn
    exfalso
    obtain ⟨iso⟩ := sphere_homology_top q (by omega)
    have : ¬ IsZero (AddCommGrpCat.of ℤ) := by
      intro hz
      have := hz.eq_of_src (𝟙 (AddCommGrpCat.of ℤ)) 0
      have := congrArg (fun f => (CategoryTheory.ConcreteCategory.hom f) (1 : ℤ)) this
      simp at this
    exact this (h.of_iso iso.symm)
  ·
    haveI : ContractibleSpace (Disk (n + 2)) :=
      (convex_closedBall (0 : EuclideanSpace ℝ (Fin (n + 2))) 1).contractibleSpace ⟨0, by simp⟩

    have hDq2 : IsZero ((pairSES (Disk (n + 2)) (diskBoundarySubset (n + 2))).X₂.homology (q + 2)) :=
      isZero_SHG_contractible _ _ (by omega)
    have hDq1 : IsZero ((pairSES (Disk (n + 2)) (diskBoundarySubset (n + 2))).X₂.homology (q + 1)) :=
      isZero_SHG_contractible _ _ (by omega)

    have δiso := pairδIso (Disk (n + 2)) (diskBoundarySubset (n + 2)) (q + 1) hDq2 hDq1

    have hRel : IsZero (Excision.RelativeSingularHomologyGroup (q + 2) (Disk (n + 2))
        (diskBoundarySubset (n + 2))) :=
      relative_homology_vanishing (q + 2) (n + 2) (by omega) (by omega)

    have hRelX3 : IsZero ((pairSES (Disk (n + 2)) (diskBoundarySubset (n + 2))).X₃.homology (q + 2)) := by
      convert hRel using 2

    have hBdry : IsZero ((pairSES (Disk (n + 2)) (diskBoundarySubset (n + 2))).X₁.homology (q + 1)) :=
      hRelX3.of_iso δiso.symm

    have homIso := (HomologicalComplex.homologyFunctor _ _ (q + 1)).mapIso
      (singularChainZF.mapIso (bdryToSphereIso n))
    exact hBdry.of_iso homIso.symm

/-- For `n ≥ 2`, the first homology of the sphere vanishes: `H_1(S^n) = 0`. -/
theorem sphere_h1_vanishing (n : ℕ) (hn : n ≥ 2) :
    IsZero (SingularHomologyGroup 1 (Sphere n)) := by

  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩

  haveI : ContractibleSpace (Disk (m + 2)) :=
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin (m + 2))) 1).contractibleSpace ⟨0, by simp⟩

  have hD2 : IsZero ((pairSES (Disk (m + 2)) (diskBoundarySubset (m + 2))).X₂.homology 2) :=
    isZero_SHG_contractible _ _ (by omega)
  have hD1 : IsZero ((pairSES (Disk (m + 2)) (diskBoundarySubset (m + 2))).X₂.homology 1) :=
    isZero_SHG_contractible _ _ (by omega)

  have δiso := pairδIso (Disk (m + 2)) (diskBoundarySubset (m + 2)) 1 hD2 hD1

  have hRel : IsZero (Excision.RelativeSingularHomologyGroup 2 (Disk (m + 2))
      (diskBoundarySubset (m + 2))) :=
    relative_homology_vanishing 2 (m + 2) (by omega) (by omega)
  have hRelX3 : IsZero ((pairSES (Disk (m + 2)) (diskBoundarySubset (m + 2))).X₃.homology 2) := by
    convert hRel using 2

  have hBdry : IsZero ((pairSES (Disk (m + 2)) (diskBoundarySubset (m + 2))).X₁.homology 1) :=
    hRelX3.of_iso δiso.symm

  have homIso := (HomologicalComplex.homologyFunctor _ _ 1).mapIso
    (singularChainZF.mapIso (bdryToSphereIso m))
  exact hBdry.of_iso homIso.symm

end SuspensionVanishing

/-- **Off-degree vanishing of sphere homology.** For `n > 0`, `0 < q ≠ n`, we have
`H_q(S^n) = 0`. The proof is a two-variable induction on `q + n`, combining
`sphere_h1_vanishing`, `sphere_zero_homology_vanishing`, and `suspension_vanishing_step`. -/
theorem sphere_homology_vanishing (q n : ℕ) (hn : n > 0)
    (hq0 : q ≠ 0) (hqn : q ≠ n) :
    IsZero (SingularHomologyGroup q (Sphere n)) := by


  suffices aux : ∀ (k q n : ℕ), q + n ≤ k → n > 0 → q ≠ 0 → q ≠ n →
      IsZero (SingularHomologyGroup q (Sphere n)) from
    aux (q + n) q n (le_refl _) hn hq0 hqn
  intro k
  induction k with
  | zero => intro q n hk; omega
  | succ k ih =>
    intro q n hk hn hq0 hqn

    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    by_cases hm : m = 0
    ·
      subst hm

      obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
      apply suspension_vanishing_step p 0 (by omega)
      exact sphere_zero_homology_vanishing p (by omega)
    ·
      by_cases hq1 : q = 1
      ·
        subst hq1
        exact sphere_h1_vanishing (m + 1) (by omega)
      ·
        obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
        apply suspension_vanishing_step p m (by omega)

        exact ih p m (by omega) (by omega) (by omega) (by omega)

/-- **Zeroth homology of `S^n` for `n > 0`:** `H_0(S^n) ≅ ℤ` (the sphere is path connected). -/
theorem sphere_homology_zero (n : ℕ) (hn : n > 0) :
    Nonempty (SingularHomologyGroup 0 (Sphere n) ≅ AddCommGrpCat.of ℤ) := by

  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩

  haveI hContr : ContractibleSpace (Disk (m + 2)) :=
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin (m + 2))) 1).contractibleSpace ⟨0, by simp⟩

  let S := pairSES (Disk (m + 2)) (diskBoundarySubset (m + 2))
  have hSE := pairSES_shortExact (Disk (m + 2)) (diskBoundarySubset (m + 2))

  have hD_1 : IsZero (S.X₂.homology 1) := isZero_SHG_contractible _ _ (by omega)

  have hD_0_iso := (ContractibleHomology.singularHomologyOfContractible (Disk (m + 2))).isoZero


  have hR_0 : IsZero (Excision.RelativeSingularHomologyGroup 0 (Disk (m + 2))
      (diskBoundarySubset (m + 2))) :=
    relative_homology_vanishing 0 (m + 2) (by omega) (by omega)
  have hR_1 : IsZero (Excision.RelativeSingularHomologyGroup 1 (Disk (m + 2))
      (diskBoundarySubset (m + 2))) :=
    relative_homology_vanishing 1 (m + 2) (by omega) (by omega)

  have hS3_0 : IsZero (S.X₃.homology 0) := hR_0
  have hS3_1 : IsZero (S.X₃.homology 1) := hR_1


  have hmono_f : Mono (HomologicalComplex.homologyMap S.f 0) := by
    have hexact := hSE.homology_exact₁ 1 0 (by rw [ComplexShape.down_Rel]; omega)
    exact hexact.mono_g (hS3_1.eq_of_src _ 0)


  have hepi_f : Epi (HomologicalComplex.homologyMap S.f 0) := by
    have hexact := hSE.homology_exact₂ 0
    exact hexact.epi_f (hS3_0.eq_of_tgt _ 0)

  haveI : IsIso (HomologicalComplex.homologyMap S.f 0) :=
    isIso_of_mono_of_epi _

  let iso1 : S.X₁.homology 0 ≅ S.X₂.homology 0 :=
    asIso (HomologicalComplex.homologyMap S.f 0)


  let topIso := bdryToSphereIso m
  let chainIso := singularChainZF.mapIso topIso
  let homIso := (HomologicalComplex.homologyFunctor _ _ 0).mapIso chainIso


  exact ⟨homIso.symm ≪≫ iso1 ≪≫ hD_0_iso⟩

/-- **Proposition 10.4 (final form).** All the sphere/disk-pair homology computations
packaged into a single `SphereAndDiskHomology` record. -/
theorem sphereAndDiskHomology : SphereAndDiskHomology :=
  ⟨sphere_homology_top, sphere_homology_zero, sphere_zero_homology_zero,
   sphere_homology_vanishing, sphere_zero_homology_vanishing,
   relative_homology_top, relative_homology_vanishing⟩

open scoped ContinuousMap

/-- A homotopy equivalence `X ≃ₕ Y` induces an isomorphism `H_q(X; ℤ) ≅ H_q(Y; ℤ)` on
singular homology for every `q`. -/
noncomputable def homotopyEquiv_singularHomologyIso {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₕ Y) (q : ℕ) :
    SingularHomologyGroup q X ≅ SingularHomologyGroup q Y := by
  open AlgebraicTopology CategoryTheory in

  let F := ((singularHomologyFunctor AddCommGrpCat q).obj (AddCommGrpCat.of ℤ))
  let fwd : (TopCat.of X) ⟶ (TopCat.of Y) := TopCat.ofHom e.toFun
  let bwd : (TopCat.of Y) ⟶ (TopCat.of X) := TopCat.ofHom e.invFun


  let Hl := e.left_inv.some
  let Hr := e.right_inv.some
  change F.obj (TopCat.of X) ≅ F.obj (TopCat.of Y)

  have hfwd_bwd : F.map (fwd ≫ bwd) = F.map (𝟙 _) :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      (show TopCat.Homotopy (fwd ≫ bwd) (𝟙 _) from Hl)
      (AddCommGrpCat.of ℤ) q
  have hbwd_fwd : F.map (bwd ≫ fwd) = F.map (𝟙 _) :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      (show TopCat.Homotopy (bwd ≫ fwd) (𝟙 _) from Hr)
      (AddCommGrpCat.of ℤ) q
  have h1 : F.map fwd ≫ F.map bwd = 𝟙 _ := by
    rw [← F.map_comp, hfwd_bwd, F.map_id]
  have h2 : F.map bwd ≫ F.map fwd = 𝟙 _ := by
    rw [← F.map_comp, hbwd_fwd, F.map_id]
  exact ⟨F.map fwd, F.map bwd, h1, h2⟩

/-- The group `ℤ` is not a zero object in `AddCommGrpCat`. -/
lemma addCommGrpCat_int_not_isZero : ¬ IsZero (AddCommGrpCat.of ℤ) := by
  intro h

  have heq := h.eq_of_src (𝟙 (AddCommGrpCat.of ℤ)) 0

  have h1 := congrArg (fun f => (CategoryTheory.ConcreteCategory.hom f) (1 : ℤ)) heq
  simp at h1

/-- **Corollary 10.5.** If `m ≠ n`, then `S^m` and `S^n` are not homotopy equivalent. -/
theorem sphere_not_homotopy_equiv (m n : ℕ) (hmn : m ≠ n)
  : IsEmpty (Sphere m ≃ₕ Sphere n) := by
  rw [isEmpty_iff]
  intro e

  suffices aux : ∀ a b : ℕ, a < b → (Sphere a ≃ₕ Sphere b) → False by
    rcases Nat.lt_or_lt_of_ne hmn with hlt | hlt
    · exact aux m n hlt e
    · exact aux n m hlt e.symm
  intro a b hab e'
  have hb : b > 0 := Nat.pos_of_ne_zero (by omega)

  have iso := homotopyEquiv_singularHomologyIso e' b

  have hzero : IsZero (SingularHomologyGroup b (Sphere a)) := by
    by_cases ha : a = 0
    · subst ha
      exact sphere_zero_homology_vanishing b hb
    · exact sphere_homology_vanishing b a (Nat.pos_of_ne_zero ha)
        (by omega) (by omega)

  have hnonzero : ¬ IsZero (SingularHomologyGroup b (Sphere b)) := by
    intro h
    obtain ⟨i⟩ := sphere_homology_top b hb
    exact addCommGrpCat_int_not_isZero (IsZero.of_iso h i.symm)

  exact hnonzero (IsZero.of_iso hzero iso.symm)


/-- The punctured Euclidean space `ℝ^{n+1} ∖ {0}` is homotopy equivalent to the unit sphere
`S^n ⊆ ℝ^{n+1}`, via the radial deformation retraction `x ↦ x/‖x‖`. -/
theorem punctured_euclidean_homotopyEquiv_sphere (n : ℕ)
    : Nonempty ({x : EuclideanSpace ℝ (Fin (n + 1)) | x ≠ 0} ≃ₕ
                Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  open unitInterval ContinuousMap in

  let E := EuclideanSpace ℝ (Fin (n + 1))

  have coeff_pos : ∀ (t : I) (x : E), x ≠ 0 →
      0 < (1 - (t : ℝ)) * ‖x‖⁻¹ + (t : ℝ) := by
    intro t x hx
    have ht0 := unitInterval.nonneg t
    have hnp : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
    rcases eq_or_lt_of_le ht0 with heq | htpos
    · rw [← heq]; simp [inv_pos.mpr hnp]
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (by linarith [unitInterval.le_one t]) (inv_nonneg.mpr hnp.le)) htpos
  have coeff_ne : ∀ (t : I) (x : E), x ≠ 0 →
      (1 - (t : ℝ)) * ‖x‖⁻¹ + (t : ℝ) ≠ 0 :=
    fun t x hx => ne_of_gt (coeff_pos t x hx)

  let r : C({x : E | x ≠ 0}, Metric.sphere (0 : E) 1) :=
    ⟨fun ⟨x, hx⟩ => ⟨(‖x‖⁻¹ : ℝ) • x, by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
      exact norm_smul_inv_norm (𝕜 := ℝ) hx⟩,
    Continuous.subtype_mk
      (((continuous_norm.comp continuous_subtype_val).inv₀
        (fun ⟨_, hx⟩ => norm_ne_zero_iff.mpr hx)).smul continuous_subtype_val) _⟩

  let i : C(Metric.sphere (0 : E) 1, {x : E | x ≠ 0}) :=
    ⟨fun ⟨y, hy⟩ => ⟨y, by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hy
      intro h0; simp [h0] at hy⟩,
    continuous_subtype_val.subtype_mk _⟩

  have ri_eq_id : r.comp i = ContinuousMap.id _ := by
    ext1 ⟨y, hy⟩
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, ContinuousMap.id_apply, r, i]
    ext1
    have hny : ‖y‖ = 1 := by rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at hy
    simp [hny]

  have ir_htpy_id : (i.comp r).Homotopic (ContinuousMap.id _) := by
    refine ⟨⟨⟨fun ⟨t, ⟨x, hx⟩⟩ =>
      ⟨((1 - (t : ℝ)) * ‖x‖⁻¹ + (t : ℝ)) • x, ?nonzero⟩, ?cont⟩, ?zero, ?one⟩⟩
    case nonzero =>
      intro h
      rcases eq_zero_or_eq_zero_of_smul_eq_zero h with h1 | h2
      · exact absurd h1 (coeff_ne t x hx)
      · exact hx h2
    case cont =>
      apply Continuous.subtype_mk
      exact (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
            ((continuous_norm.comp (continuous_subtype_val.comp continuous_snd)).inv₀
              (fun ⟨_, ⟨_, hx⟩⟩ => norm_ne_zero_iff.mpr hx))).add
          (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp continuous_snd)
    case zero =>
      intro ⟨x, hx⟩
      ext1
      simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, r, i]
      have h0 : (↑(0 : I) : ℝ) = 0 := rfl
      rw [h0]
      simp
    case one =>
      intro ⟨x, hx⟩
      ext1
      simp only [ContinuousMap.id_apply]
      have h1 : (↑(1 : I) : ℝ) = 1 := rfl
      rw [h1]
      simp
  exact ⟨⟨r, i, ir_htpy_id, ri_eq_id ▸ Homotopic.refl _⟩⟩

/-- A homeomorphism `f : X ≃ₜ Y` restricts to a homeomorphism
`{x | x ≠ p} ≃ₜ {y | y ≠ f p}` between punctured spaces. -/
def homeomorphSubtypeNe {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X ≃ₜ Y) (x : X) :
    {y : X | y ≠ x} ≃ₜ {z : Y | z ≠ f x} where
  toEquiv := f.toEquiv.subtypeEquiv fun _ =>
    ⟨fun h => f.injective.ne h, fun h e => h (congrArg f e)⟩
  continuous_toFun :=
    Continuous.subtype_mk ((map_continuous f).comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk ((map_continuous f.symm).comp continuous_subtype_val) _

/-- Translation by `-p` gives a homeomorphism `{x | x ≠ p} ≃ₜ {y | y ≠ 0}`. -/
def puncturedTranslateHomeomorph {G : Type*} [TopologicalSpace G] [AddGroup G]
    [IsTopologicalAddGroup G] (p : G) :
    {x : G | x ≠ p} ≃ₜ {y : G | y ≠ 0} := by
  refine (homeomorphSubtypeNe (Homeomorph.addRight (-p)) p).trans
    (Homeomorph.ofEqSubtypes ?_)
  ext x
  simp [add_neg_cancel]

/-- **Corollary 10.6 (Invariance of dimension).** If `m ≠ n`, then `ℝ^m` and `ℝ^n` are not
homeomorphic. The proof punctures the spaces, applies the homotopy equivalence
`ℝ^{n+1} ∖ {0} ≃ₕ S^n`, and uses that spheres of different dimensions are not
homotopy equivalent. -/
theorem euclidean_not_homeomorph (m n : ℕ) (hmn : m ≠ n) :
    IsEmpty (EuclideanSpace ℝ (Fin m) ≃ₜ EuclideanSpace ℝ (Fin n)) := by
  rw [isEmpty_iff]
  intro f
  by_cases hm : m = 0
  · subst hm
    have hn : n ≠ 0 := fun h => hmn (by rw [h])
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    haveI : Subsingleton (EuclideanSpace ℝ (Fin 0)) := Unique.instSubsingleton
    have hsub : Subsingleton (EuclideanSpace ℝ (Fin (k + 1))) :=
      f.surjective.subsingleton
    exact absurd hsub (not_subsingleton _)
  · by_cases hn : n = 0
    · subst hn
      haveI : Subsingleton (EuclideanSpace ℝ (Fin 0)) := Unique.instSubsingleton
      have hsub : Subsingleton (EuclideanSpace ℝ (Fin m)) :=
        f.symm.surjective.subsingleton
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
      exact absurd hsub (not_subsingleton _)
    · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
      obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      have hm'n' : m' ≠ n' := fun h => hmn (congrArg (· + 1) h)
      let g := homeomorphSubtypeNe f 0
      let t : {z : EuclideanSpace ℝ (Fin (n' + 1)) | z ≠ f 0} ≃ₜ
              {y : EuclideanSpace ℝ (Fin (n' + 1)) | y ≠ 0} :=
        puncturedTranslateHomeomorph (f 0)
      obtain ⟨heq_m⟩ := punctured_euclidean_homotopyEquiv_sphere m'
      obtain ⟨heq_n⟩ := punctured_euclidean_homotopyEquiv_sphere n'
      have hequiv : Nonempty (Sphere m' ≃ₕ Sphere n') :=
        ⟨heq_m.symm.trans (g.toHomotopyEquiv.trans (t.toHomotopyEquiv.trans heq_n))⟩
      haveI := sphere_not_homotopy_equiv m' n' hm'n'
      exact IsEmpty.false hequiv.some

end SphereHomology

namespace BrouwerFixedPoint

open Metric Set Inner

/-- Local abbreviation for the closed unit disk `D^n ⊆ ℝ^n` in the Brouwer fixed-point
section. -/
abbrev Disk (n : ℕ) := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1

/-- Local abbreviation for the unit sphere `S^{n-1} ⊆ ℝ^n` in the Brouwer fixed-point
section. -/
abbrev Sphere (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1

/-- A *retraction* of `D^n` onto `S^{n-1}`: a continuous map `r : ℝ^n → ℝ^n` sending the
disk to the sphere and fixing the boundary. Brouwer's theorem amounts to ruling out such
retractions. -/
structure IsRetraction (n : ℕ) (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop where
  continuous_r : Continuous r
  maps_to : ∀ x, x ∈ Disk n → r x ∈ Sphere n
  fixes_boundary : ∀ x, x ∈ Sphere n → r x = x


/-- The functor `H_k(−; ℤ) : TopCat → AddCommGrpCat`, packaged for use in the Brouwer proof. -/
noncomputable abbrev homFunctorZ (k : ℕ) : TopCat.{0} ⥤ AddCommGrpCat :=
  (AlgebraicTopology.singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)


/-- The singular homology of a contractible space vanishes in positive degree. -/
lemma isZero_homology_of_contractible (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] (k : ℕ) (hk : k ≠ 0) :
    IsZero ((homFunctorZ k).obj (TopCat.of X)) := by
  obtain ⟨x₀, ⟨Hx⟩⟩ := (contractible_iff_id_nullhomotopic X).mp ‹_›
  have hmap : (homFunctorZ k).map (𝟙 (TopCat.of X)) =
      (homFunctorZ k).map (TopCat.ofHom (ContinuousMap.const X x₀)) := by
    show (homFunctorZ k).map (TopCat.ofHom (ContinuousMap.id X)) = _
    exact (Hx : TopCat.Homotopy _ _).congr_homologyMap_singularChainComplexFunctor _ _
  rw [(homFunctorZ k).map_id] at hmap
  let p : TopCat.of X ⟶ TopCat.of PUnit := TopCat.ofHom ⟨fun _ => .unit, continuous_const⟩
  let q : TopCat.of PUnit ⟶ TopCat.of X := TopCat.ofHom ⟨fun _ => x₀, continuous_const⟩
  have hfact : TopCat.ofHom (ContinuousMap.const X x₀) = p ≫ q := by
    apply TopCat.hom_ext; apply ContinuousMap.ext; intro _; rfl
  rw [hfact, (homFunctorZ k).map_comp] at hmap
  have : (homFunctorZ k).map p ≫ (homFunctorZ k).map q = 0 := by
    rw [(AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      _ _ _ _ hk).eq_of_src ((homFunctorZ k).map q) 0, comp_zero]
  rw [this] at hmap
  exact (IsZero.iff_id_eq_zero _).mpr hmap


/-- The inclusion `S^{n-1} ↪ D^n` of the boundary sphere into the disk, as a morphism of
`TopCat`. -/
noncomputable def sphereInclusion (n : ℕ) :
    TopCat.of ↥(Sphere n) ⟶ TopCat.of ↥(Disk n) :=
  TopCat.ofHom ⟨Set.inclusion Metric.sphere_subset_closedBall,
    continuous_inclusion _⟩


/-- A retraction `r : ℝ^n → ℝ^n` of `D^n` onto `S^{n-1}` packaged as a `TopCat` morphism
`D^n ⟶ S^{n-1}`. -/
noncomputable def diskRetraction (n : ℕ)
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hr : IsRetraction n r) :
    TopCat.of ↥(Disk n) ⟶ TopCat.of ↥(Sphere n) :=
  TopCat.ofHom ⟨fun ⟨x, hx⟩ => ⟨r x, hr.maps_to x hx⟩,
    Continuous.subtype_mk (hr.continuous_r.comp continuous_subtype_val) _⟩


/-- A retraction satisfies `(sphereInclusion) ≫ (diskRetraction r) = id`, the categorical
definition of `r` being a retraction. -/
lemma sphereInclusion_diskRetraction (n : ℕ)
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hr : IsRetraction n r) :
    sphereInclusion n ≫ diskRetraction n r hr = 𝟙 _ := by
  apply TopCat.hom_ext; apply ContinuousMap.ext
  intro ⟨x, hx⟩
  show (⟨r x, _⟩ : ↥(Sphere n)) = ⟨x, hx⟩
  exact Subtype.ext (hr.fixes_boundary x hx)


/-- A nontrivial abelian group is not zero in `AddCommGrpCat`. -/
lemma not_isZero_of_nontrivial (G : Type*) [AddCommGroup G] [Nontrivial G] :
    ¬ IsZero (AddCommGrpCat.of G) := by
  intro h
  obtain ⟨a, b, hab⟩ := exists_pair_ne (α := G)
  have ha : a = (0 : G) := by
    have := congrArg (fun f => AddCommGrpCat.Hom.hom f a) ((IsZero.iff_id_eq_zero _).mp h)
    simpa using this
  have hb : b = (0 : G) := by
    have := congrArg (fun f => AddCommGrpCat.Hom.hom f b) ((IsZero.iff_id_eq_zero _).mp h)
    simpa using this
  exact hab (by rw [ha, hb])


/-- The projection `ℝ^1 → ℝ` onto the (only) coordinate, as a continuous linear map. -/
noncomputable def coordProj : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ :=
  EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)


/-- In `ℝ^1`, the Euclidean norm equals the absolute value of the unique coordinate. -/
lemma norm_fin1_eq_abs_coord (x : EuclideanSpace ℝ (Fin 1)) :
    ‖x‖ = |coordProj x| := by
  simp [EuclideanSpace.norm_eq, coordProj, EuclideanSpace.proj,
    Finset.sum_singleton, Real.sqrt_sq_eq_abs, sq_abs]


/-- **No retraction `D^1 → S^0`** (base case for Brouwer). The interval `[-1, 1]` is
connected but `S^0 = {-1, +1}` is not, so the intermediate-value theorem rules out a
continuous retraction. -/
lemma no_retraction_dim_one
    (r : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1))
    (hr : IsRetraction 1 r) : False := by

  set g := (coordProj ·) ∘ r
  have hg_cont : Continuous g := coordProj.continuous.comp hr.continuous_r
  have hg_pm : ∀ x ∈ Disk 1, g x = 1 ∨ g x = -1 := by
    intro x hx
    have hmem := hr.maps_to x hx
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_fin1_eq_abs_coord] at hmem

    change coordProj (r x) = 1 ∨ coordProj (r x) = -1
    cases abs_cases (coordProj (r x)) with
    | inl h => left; linarith [h.1]
    | inr h => right; linarith [h.1]
  set epos : EuclideanSpace ℝ (Fin 1) := (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => (1 : ℝ))
  set eneg : EuclideanSpace ℝ (Fin 1) := (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => (-1 : ℝ))
  have hepos_sph : epos ∈ Sphere 1 := by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_fin1_eq_abs_coord]
    simp [coordProj, EuclideanSpace.proj, epos]
  have heneg_sph : eneg ∈ Sphere 1 := by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_fin1_eq_abs_coord]
    simp [coordProj, EuclideanSpace.proj, eneg]
  have hg_epos : g epos = 1 := by
    show coordProj (r epos) = 1
    rw [hr.fixes_boundary epos hepos_sph]
    simp [coordProj, EuclideanSpace.proj, epos]
  have hg_eneg : g eneg = -1 := by
    show coordProj (r eneg) = -1
    rw [hr.fixes_boundary eneg heneg_sph]
    simp [coordProj, EuclideanSpace.proj, eneg]

  obtain ⟨x, hx, hgx⟩ := (convex_closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1).isPreconnected
    |>.intermediate_value₂
    (Metric.sphere_subset_closedBall heneg_sph) (Metric.sphere_subset_closedBall hepos_sph)
    hg_cont.continuousOn continuousOn_const
    (by rw [hg_eneg]; norm_num : g eneg ≤ 0) (by rw [hg_epos]; norm_num : (0 : ℝ) ≤ g epos)

  rcases hg_pm x hx with h | h <;> linarith


/-- **No retraction `D^{m+1} → S^m`** for `m ≥ 1` (inductive step for Brouwer). If such a
retraction existed, then `H_m(S^m) ≅ ℤ` would be a retract of `H_m(D^{m+1}) = 0`,
contradiction. -/
lemma no_retraction_higher (m : ℕ) (hm : 0 < m)
    (r : EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin (m + 1)))
    (hr : IsRetraction (m + 1) r) : False := by

  have hret := sphereInclusion_diskRetraction (m + 1) r hr
  have hfunctor : (homFunctorZ m).map (sphereInclusion (m + 1)) ≫
      (homFunctorZ m).map (diskRetraction (m + 1) r hr) =
      𝟙 ((homFunctorZ m).obj (TopCat.of ↥(Sphere (m + 1)))) := by
    rw [← (homFunctorZ m).map_comp, hret, (homFunctorZ m).map_id]

  haveI : ContractibleSpace ↥(Disk (m + 1)) :=
    contractibleSpace_closedBall (by norm_num)
  have hDisk : IsZero ((homFunctorZ m).obj (TopCat.of ↥(Disk (m + 1)))) :=
    isZero_homology_of_contractible _ _ (by omega)

  have : 𝟙 ((homFunctorZ m).obj (TopCat.of ↥(Sphere (m + 1)))) = 0 := by
    rw [← hfunctor, hDisk.eq_of_tgt ((homFunctorZ m).map (sphereInclusion (m + 1))) 0, zero_comp]

  have hSphereZero : IsZero ((homFunctorZ m).obj (TopCat.of ↥(Sphere (m + 1)))) :=
    (IsZero.iff_id_eq_zero _).mpr this


  obtain ⟨e⟩ := SphereHomology.sphere_homology_top m hm
  have : ¬ IsZero (SingularHomologyGroup m (SphereHomology.Sphere m)) :=
    fun h => not_isZero_of_nontrivial ℤ (h.of_iso e.symm)
  exact this (by convert hSphereZero using 2)

/-- **No retraction `D^n → S^{n-1}`** for any `n ≥ 1`. Combines `no_retraction_dim_one`
(for `n = 1`) and `no_retraction_higher` (for `n ≥ 2`). This is the key topological input
to Brouwer's fixed-point theorem. -/
theorem no_retraction_disk_to_sphere (n : ℕ) (hn : 0 < n)
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hr : IsRetraction n r) : False := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact no_retraction_dim_one r hr
  · exact no_retraction_higher m hm r hr

/-- Discriminant of the quadratic equation `‖a + t v‖ = 1` in `t`, used in the geometric
construction of a retraction from a fixed-point-free self-map of `D^n`. -/
noncomputable def rayDiscrim {n : ℕ} (a v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  inner (𝕜 := ℝ) a v ^ 2 + ‖v‖ ^ 2 * (1 - ‖a‖ ^ 2)

/-- The positive root `t = (−⟨a,v⟩ + √Δ) / ‖v‖²` of the equation `‖a + t v‖ = 1`, where
`Δ = rayDiscrim a v`. Geometrically: the parameter at which the ray `t ↦ a + t v`
(with `t ≥ 0`) hits the unit sphere. -/
noncomputable def rayParam {n : ℕ} (a v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (-inner (𝕜 := ℝ) a v + Real.sqrt (rayDiscrim a v)) / ‖v‖ ^ 2

/-- Geometric retraction associated to a fixed-point-free self-map `f` of `D^n`: from each
point `x`, follow the ray from `f x` through `x` until it hits the boundary sphere. -/
noncomputable def retractionMap {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  f x + rayParam (f x) (x - f x) • (x - f x)

/-- Radial projection of `ℝ^n` onto the closed unit ball: `x ↦ x / max(1, ‖x‖)`. -/
noncomputable def projBall {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  (max 1 ‖x‖)⁻¹ • x

/-- The radial projection `projBall` is continuous. -/
lemma projBall_continuous (n : ℕ) :
    Continuous (projBall : EuclideanSpace ℝ (Fin n) → _) :=
  (((continuous_const.max continuous_norm).inv₀
    (fun x => ne_of_gt (lt_of_lt_of_le one_pos (le_max_left 1 ‖x‖)))).smul continuous_id)

/-- `projBall x` lies in the closed unit disk. -/
lemma projBall_mem_disk (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    projBall x ∈ Disk n := by
  simp only [Disk, mem_closedBall, dist_zero_right, projBall, norm_smul]
  have hmax : (0 : ℝ) < max 1 ‖x‖ := lt_of_lt_of_le one_pos (le_max_left 1 ‖x‖)
  rw [Real.norm_of_nonneg (inv_nonneg.mpr hmax.le), inv_mul_le_iff₀ hmax]
  linarith [le_max_right 1 ‖x‖]

/-- For `x` already in the unit disk, `projBall x = x`. -/
lemma projBall_eq_of_mem_disk (n : ℕ) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Disk n) : projBall x = x := by
  simp only [Disk, mem_closedBall, dist_zero_right] at hx
  simp only [projBall, max_eq_left hx, inv_one, one_smul]

/-- Algebraic identity: the positive root of the quadratic `c t² + 2 β t + (α - 1) = 0`
yields `c t² + 2 β t + α = 1`. Used to verify that `rayParam` solves `‖a + t v‖ = 1`. -/
lemma quadratic_ray_root (c β s α : ℝ) (hc : c ≠ 0)
    (hs : s ^ 2 = β ^ 2 + c * (1 - α)) :
    c * ((-β + s) / c) ^ 2 + 2 * β * ((-β + s) / c) + α = 1 := by
  field_simp
  nlinarith [sq_nonneg (c * α), sq_nonneg s, sq_nonneg β, sq_nonneg c]

/-- For `‖a‖ ≤ 1` and `v ≠ 0`, the point `a + rayParam a v • v` has unit norm: the ray from
`a` in direction `v` hits the unit sphere exactly at this parameter. -/
lemma retractionMap_norm_eq_one {n : ℕ}
    {a v : EuclideanSpace ℝ (Fin n)} (ha : ‖a‖ ≤ 1) (hv : v ≠ 0) :
    ‖a + rayParam a v • v‖ = 1 := by
  show ‖a + ((-inner (𝕜 := ℝ) a v + Real.sqrt (rayDiscrim a v)) / ‖v‖ ^ 2) • v‖ = 1
  show ‖a + ((-inner (𝕜 := ℝ) a v +
    Real.sqrt (inner (𝕜 := ℝ) a v ^ 2 + ‖v‖ ^ 2 * (1 - ‖a‖ ^ 2))) / ‖v‖ ^ 2) • v‖ = 1
  have hv_norm : ‖v‖ ≠ 0 := by simp [hv]
  have hv2 : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 hv_norm
  have hΔ : 0 ≤ inner (𝕜 := ℝ) a v ^ 2 + ‖v‖ ^ 2 * (1 - ‖a‖ ^ 2) := by
    apply add_nonneg (sq_nonneg _)
    exact mul_nonneg (sq_nonneg _) (by linarith [(sq_le_one_iff₀ (norm_nonneg a)).mpr ha])
  have key := quadratic_ray_root (‖v‖ ^ 2) (inner (𝕜 := ℝ) a v)
    (Real.sqrt (inner (𝕜 := ℝ) a v ^ 2 + ‖v‖ ^ 2 * (1 - ‖a‖ ^ 2)))
    (‖a‖ ^ 2) hv2 (Real.sq_sqrt hΔ)
  have norm_sq : ‖a + ((-inner (𝕜 := ℝ) a v +
    Real.sqrt (inner (𝕜 := ℝ) a v ^ 2 + ‖v‖ ^ 2 * (1 - ‖a‖ ^ 2))) /
    ‖v‖ ^ 2) • v‖ ^ 2 = 1 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs]; linarith
  nlinarith [sq_nonneg (‖a + ((-inner (𝕜 := ℝ) a v +
    Real.sqrt (inner (𝕜 := ℝ) a v ^ 2 + ‖v‖ ^ 2 * (1 - ‖a‖ ^ 2))) /
    ‖v‖ ^ 2) • v‖ - 1),
    norm_nonneg (a + ((-inner (𝕜 := ℝ) a v +
    Real.sqrt (inner (𝕜 := ℝ) a v ^ 2 + ‖v‖ ^ 2 * (1 - ‖a‖ ^ 2))) /
    ‖v‖ ^ 2) • v)]

/-- If `x` is already on the unit sphere (and `a ≠ x` with `‖a‖ ≤ 1`), then the ray from
`a` through `x` hits the sphere exactly at `x`, i.e. `rayParam a (x - a) = 1`. -/
lemma rayParam_eq_one_of_norm_one {n : ℕ} {a x : EuclideanSpace ℝ (Fin n)}
    (ha : ‖a‖ ≤ 1) (hx : ‖x‖ = 1) (hne : a ≠ x) :
    rayParam a (x - a) = 1 := by
  unfold rayParam rayDiscrim
  have hv : x - a ≠ 0 := sub_ne_zero.mpr hne.symm
  have hv2_pos : 0 < ‖x - a‖ ^ 2 := by
    have : 0 < ‖x - a‖ := norm_pos_iff.mpr hv; positivity
  suffices h : -inner (𝕜 := ℝ) a (x - a) +
      Real.sqrt (inner (𝕜 := ℝ) a (x - a) ^ 2 +
        ‖x - a‖ ^ 2 * (1 - ‖a‖ ^ 2)) = ‖x - a‖ ^ 2 by
    rw [h, div_self (ne_of_gt hv2_pos)]
  have hinner : (inner (𝕜 := ℝ) a (x - a) : ℝ) = inner (𝕜 := ℝ) a x - ‖a‖ ^ 2 := by
    simp only [inner_sub_right, real_inner_self_eq_norm_sq]
  have hnorm_v : ‖x - a‖ ^ 2 = 1 - 2 * (inner (𝕜 := ℝ) a x : ℝ) + ‖a‖ ^ 2 := by
    rw [norm_sub_sq_real, hx, one_pow, real_inner_comm]
  have hDiscrim : (inner (𝕜 := ℝ) a (x - a)) ^ 2 + ‖x - a‖ ^ 2 * (1 - ‖a‖ ^ 2) =
      (1 - (inner (𝕜 := ℝ) a x : ℝ)) ^ 2 := by
    rw [hinner, hnorm_v]; ring
  have hβ_le : (inner (𝕜 := ℝ) a x : ℝ) ≤ 1 := by
    calc _ ≤ ‖a‖ * ‖x‖ := real_inner_le_norm a x
    _ = ‖a‖ := by rw [hx, mul_one]
    _ ≤ 1 := ha
  rw [hDiscrim, Real.sqrt_sq (by linarith), hinner, hnorm_v]; ring

/-- **From a fixed-point-free self-map to a retraction.** Given a continuous self-map of
the disk with no fixed point, the geometric construction `retractionMap` produces a
continuous retraction of the disk onto its boundary sphere. This is the standard reduction
of Brouwer's theorem to the non-existence of such a retraction. -/
theorem retraction_of_fixed_point_free (n : ℕ) (_hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf_cont : Continuous f)
    (hf_maps : ∀ x, x ∈ Disk n → f x ∈ Disk n)
    (hf_no_fp : ∀ x, x ∈ Disk n → f x ≠ x) :
    ∃ r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n), IsRetraction n r := by


  let r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun x => retractionMap f (projBall x)
  have hp_disk : ∀ x, projBall (n := n) x ∈ Disk n := projBall_mem_disk n
  have hv_ne : ∀ x, projBall (n := n) x - f (projBall x) ≠ 0 :=
    fun x => sub_ne_zero.mpr (Ne.symm (hf_no_fp _ (hp_disk x)))
  refine ⟨r, ⟨?_, ?_, ?_⟩⟩
  ·
    show Continuous r
    simp only [r, retractionMap, rayParam, rayDiscrim]
    have hp : Continuous (projBall : EuclideanSpace ℝ (Fin n) → _) := projBall_continuous n
    have ha : Continuous (fun x => f (projBall (n := n) x)) := hf_cont.comp hp
    have hv : Continuous (fun x => projBall (n := n) x - f (projBall x)) := hp.sub ha
    have hinner : Continuous (fun x =>
        (inner (𝕜 := ℝ) (f (projBall (n := n) x))
          (projBall x - f (projBall x)) : ℝ)) :=
      continuous_inner.comp (ha.prodMk hv)
    have hnv2 : Continuous (fun x => ‖projBall (n := n) x - f (projBall x)‖ ^ 2) :=
      (continuous_norm.comp hv).pow 2
    have hna2 : Continuous (fun x => ‖f (projBall (n := n) x)‖ ^ 2) :=
      (continuous_norm.comp ha).pow 2
    have hdisc : Continuous (fun x =>
        (inner (𝕜 := ℝ) (f (projBall (n := n) x))
          (projBall x - f (projBall x))) ^ 2 +
        ‖projBall (n := n) x - f (projBall x)‖ ^ 2 *
          (1 - ‖f (projBall (n := n) x)‖ ^ 2)) :=
      (hinner.pow 2).add (hnv2.mul (continuous_const.sub hna2))
    have hsqrt : Continuous (fun x => Real.sqrt (
        (inner (𝕜 := ℝ) (f (projBall (n := n) x))
          (projBall x - f (projBall x))) ^ 2 +
        ‖projBall (n := n) x - f (projBall x)‖ ^ 2 *
          (1 - ‖f (projBall (n := n) x)‖ ^ 2))) :=
      Real.continuous_sqrt.comp hdisc
    have hnum : Continuous (fun x =>
        -(inner (𝕜 := ℝ) (f (projBall (n := n) x))
          (projBall x - f (projBall x))) +
        Real.sqrt ((inner (𝕜 := ℝ) (f (projBall (n := n) x))
          (projBall x - f (projBall x))) ^ 2 +
        ‖projBall (n := n) x - f (projBall x)‖ ^ 2 *
          (1 - ‖f (projBall (n := n) x)‖ ^ 2))) :=
      hinner.neg.add hsqrt
    have ht : Continuous (fun x =>
        (-(inner (𝕜 := ℝ) (f (projBall (n := n) x))
          (projBall x - f (projBall x))) +
        Real.sqrt ((inner (𝕜 := ℝ) (f (projBall (n := n) x))
          (projBall x - f (projBall x))) ^ 2 +
        ‖projBall (n := n) x - f (projBall x)‖ ^ 2 *
          (1 - ‖f (projBall (n := n) x)‖ ^ 2))) /
        ‖projBall (n := n) x - f (projBall x)‖ ^ 2) :=
      hnum.div hnv2 (fun x => pow_ne_zero 2 (by
        have := hv_ne x
        simp only [ne_eq, norm_eq_zero] at this ⊢; exact this))
    exact ha.add (ht.smul hv)
  ·
    intro x hx
    show retractionMap f (projBall x) ∈ Sphere n
    rw [projBall_eq_of_mem_disk n hx]
    simp only [retractionMap, Sphere, mem_sphere, dist_zero_right]
    exact retractionMap_norm_eq_one
      (by have := hf_maps x hx; simp only [Disk, mem_closedBall, dist_zero_right] at this; exact this)
      (sub_ne_zero.mpr (Ne.symm (hf_no_fp x hx)))
  ·
    intro x hx
    show retractionMap f (projBall x) = x
    rw [projBall_eq_of_mem_disk n (sphere_subset_closedBall hx)]
    simp only [retractionMap]
    rw [rayParam_eq_one_of_norm_one
      (by have := hf_maps x (sphere_subset_closedBall hx)
          simp only [Disk, mem_closedBall, dist_zero_right] at this; exact this)
      (by simp only [Sphere, mem_sphere, dist_zero_right] at hx; exact hx)
      (hf_no_fp x (sphere_subset_closedBall hx)),
      one_smul]
    abel

/-- **Theorem 10.7 (Brouwer fixed-point theorem).** Every continuous self-map
`f : D^n → D^n` of the closed unit disk in `ℝ^n` (for `n ≥ 1`) has a fixed point. The
proof: a fixed-point-free `f` would yield a retraction `D^n → S^{n-1}`, contradicting
`no_retraction_disk_to_sphere`. -/
theorem brouwer_fixed_point (n : ℕ) (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf_cont : Continuous f)
    (hf_maps : ∀ x, x ∈ Disk n → f x ∈ Disk n) :
    ∃ x ∈ Disk n, f x = x := by
  by_contra h
  push Not at h

  obtain ⟨r, hr⟩ := retraction_of_fixed_point_free n hn f hf_cont hf_maps h

  exact no_retraction_disk_to_sphere n hn r hr

end BrouwerFixedPoint

namespace ExcisionApplications

open Set Topology EilenbergSteenrod DeformationRetract

universe u

/-- A subset `A ⊆ B` is a *deformation retract within `B`* if `A ⊆ B` and there exists a
deformation retraction of `B` onto `A` (viewed as a subset of `B`). Hypothesis of
Corollary 10.3. -/
def IsSubspaceDeformationRetract {X : Type u} [TopologicalSpace X] (A B : Set X) : Prop :=
  A ⊆ B ∧ Nonempty (DeformationRetract.IsDeformationRetract (Subtype.val ⁻¹' A : Set ↥B))

/-- The equivalence relation on `X` that collapses the subset `A` to a single point: two points
are related iff they are equal, or both lie in `A`. Used to form the quotient `X / A`. -/
def collapseSetoid {X : Type u} [TopologicalSpace X] (A : Set X) : Setoid X where
  r x y := x = y ∨ (x ∈ A ∧ y ∈ A)
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := fun h => h.elim (fun heq => Or.inl heq.symm) (fun ⟨hx, hy⟩ => Or.inr ⟨hy, hx⟩)
    trans := fun h1 h2 => by
      rcases h1 with rfl | ⟨hx, _⟩
      · exact h2
      · rcases h2 with rfl | ⟨_, hz⟩ <;> exact Or.inr ⟨hx, ‹_›⟩
  }

/-- The quotient space `X / A`: the set of equivalence classes of `collapseSetoid A`, with the
quotient topology. -/
def QuotientSpace (X : Type u) [TopologicalSpace X] (A : Set X) :=
  Quotient (collapseSetoid A)

/-- The quotient topology on `QuotientSpace X A`. -/
instance {X : Type u} [TopologicalSpace X] (A : Set X) :
    TopologicalSpace (QuotientSpace X A) :=
  instTopologicalSpaceQuotient

/-- The basepoint of `X / A`: the image in `QuotientSpace X A` of any point `a ∈ A`. -/
def quotientBasepoint {X : Type u} [TopologicalSpace X] (A : Set X)
    {a : X} (_ : a ∈ A) : QuotientSpace X A :=
  Quotient.mk (collapseSetoid A) a

/-- The pointed pair `(X / A, [a])` where `[a]` is the collapsed image of `A`. -/
def quotientPair {X : Type u} [TopologicalSpace X] (A : Set X)
    {a : X} (ha : a ∈ A) : TopPair where
  space := QuotientSpace X A
  instTop := inferInstance
  sub := {quotientBasepoint A ha}

/-- The quotient map of pairs `(X, A) → (X/A, *)` sending each point to its equivalence class. -/
def collapseMapOfPairs {X : Type u} [TopologicalSpace X] (A : Set X)
    {a : X} (ha : a ∈ A) :
    MapOfPairs ⟨X, inferInstance, A⟩ (quotientPair A ha) where
  toFun := Quotient.mk (collapseSetoid A)
  continuous_toFun := continuous_quotient_mk'
  mapsTo := fun _ hx => Quotient.sound (Or.inr ⟨hx, ha⟩)

/-- The pair `(B, A ∩ B)` viewed inside `B` via the subtype inclusion `↥B ↪ X`. -/
def subspacePair {X : Type u} [TopologicalSpace X] (A B : Set X) : TopPair where
  space := ↥B
  instTop := inferInstance
  sub := Subtype.val ⁻¹' A

/-- The pair map `(B, A ∩ B) → (X, A)` given by the subtype inclusion `↥B ↪ X`. -/
def pairInclusion {X : Type u} [TopologicalSpace X] (A B : Set X) :
    MapOfPairs (subspacePair A B) ⟨X, inferInstance, A⟩ where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val
  mapsTo := fun _ hx => hx

variable {X : Type u} [TopologicalSpace X]

/-- Two maps of pairs are equal iff their underlying continuous maps are equal. -/
theorem mapOfPairs_ext {P Q : TopPair} {f g : MapOfPairs P Q}
    (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; congr

/-- Identification of `(B, A ∩ B)` with the excised pair `(X ∖ Bᶜ, A ∖ Bᶜ)` in the forward
direction. -/
def subspacePairToExcisePair (A B : Set X) :
    MapOfPairs (subspacePair A B)
      ((⟨X, inferInstance, A⟩ : TopPair).excisePair Bᶜ) where
  toFun := fun ⟨x, hx⟩ => ⟨x, by rw [compl_compl]; exact hx⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  mapsTo := fun ⟨_, _⟩ hxA => hxA

/-- Identification of the excised pair `(X ∖ Bᶜ, A ∖ Bᶜ)` with `(B, A ∩ B)` in the reverse
direction. Inverse to `subspacePairToExcisePair`. -/
def excisePairToSubspacePair (A B : Set X) :
    MapOfPairs ((⟨X, inferInstance, A⟩ : TopPair).excisePair Bᶜ)
      (subspacePair A B) where
  toFun := fun ⟨x, hx⟩ => ⟨x, by rwa [compl_compl] at hx⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  mapsTo := fun ⟨_, _⟩ hxA => hxA

/-- The excision inclusion composed with the identification `(B, A ∩ B) ≅ (X ∖ Bᶜ, A ∖ Bᶜ)`
recovers the pair inclusion `(B, A ∩ B) → (X, A)`. -/
theorem excisionInclusion_comp_subspacePairToExcisePair (A B : Set X) :
    (excisionInclusion ⟨X, inferInstance, A⟩ Bᶜ).comp (subspacePairToExcisePair A B) =
      pairInclusion A B :=
  mapOfPairs_ext (funext fun ⟨_, _⟩ => rfl)

/-- One direction of the inverse pair: `excisePairToSubspacePair ∘ subspacePairToExcisePair = id`. -/
theorem roundTrip_subspacePair (A B : Set X) :
    (excisePairToSubspacePair A B).comp (subspacePairToExcisePair A B) =
      MapOfPairs.id (subspacePair A B) :=
  mapOfPairs_ext (funext fun ⟨_, _⟩ => rfl)

/-- The other direction of the inverse pair:
`subspacePairToExcisePair ∘ excisePairToSubspacePair = id`. -/
theorem roundTrip_excisePair (A B : Set X) :
    (subspacePairToExcisePair A B).comp (excisePairToSubspacePair A B) =
      MapOfPairs.id ((⟨X, inferInstance, A⟩ : TopPair).excisePair Bᶜ) :=
  mapOfPairs_ext (funext fun ⟨_, _⟩ => rfl)

/-- The homology map `H_n(B, A ∩ B) → H_n(X/A, *)` induced by the composition
"include into `(X, A)` then collapse `A`". This is the factorization used to deduce
that the collapse map induces an isomorphism on homology (Corollary 10.3). -/
def collapseFactorization
    (h : HomologyTheory.{u}) (n : ℤ) (A B : Set X)
    {a : X} (ha : a ∈ A)
    (_hClosure : closure A ⊆ interior B) (_hDR : IsSubspaceDeformationRetract A B) :
    h.H n (subspacePair A B) →+ h.H n (quotientPair A ha) :=
  h.map n ((collapseMapOfPairs A ha).comp (pairInclusion A B))


/-- If the inclusion `A ↪ X` of a pair `P = (X, A)` induces a bijection on `H_m` for every `m`,
then the relative homology `H_{n+1}(X, A)` is trivial. Used to deduce relative-homology
vanishing from absolute-homology equivalence via the long exact sequence. -/
lemma subsingleton_relative_of_inclusionBijective
    (h : HomologyTheory.{u}) (P : TopPair)
    (hbij : ∀ m : ℤ, Function.Bijective (h.map m (inclusionSubToSpace P)))
    (n : ℤ) : Subsingleton (h.H (n + 1) P) := by

  have h_i_surj : Function.Surjective (h.map (n + 1) (inclusionSubToSpace P)) :=
    (hbij (n + 1)).2
  have hexact_space := h.exact_at_space (n + 1) P
  have hj_zero : ∀ x, h.map (n + 1) (inclusionSpaceToPair P) x = 0 := fun x =>
    (hexact_space x).mpr (h_i_surj.range_eq ▸ Set.mem_univ x)

  have h_i_inj : Function.Injective (h.map n (inclusionSubToSpace P)) := (hbij n).1
  have hexact_sub := h.exact_at_sub n P

  have h_bnd_zero : ∀ (y : h.H (n + 1) P), h.boundary n P y = 0 := by
    intro y
    have h_in_im : h.boundary n P y ∈ Set.range (h.boundary n P) := ⟨y, rfl⟩
    have h_ker : (h.map n (inclusionSubToSpace P)) (h.boundary n P y) = 0 :=
      (hexact_sub (h.boundary n P y)).mpr h_in_im
    exact h_i_inj (h_ker.trans (map_zero _).symm)


  have hexact_pair := h.exact_at_pair n P
  constructor
  intro x y
  have hx_range : x ∈ Set.range (h.map (n + 1) (inclusionSpaceToPair P)) :=
    (hexact_pair x).mp (h_bnd_zero x)
  have hy_range : y ∈ Set.range (h.map (n + 1) (inclusionSpaceToPair P)) :=
    (hexact_pair y).mp (h_bnd_zero y)

  obtain ⟨x', hx'⟩ := hx_range
  obtain ⟨y', hy'⟩ := hy_range
  rw [← hx', ← hy', hj_zero x', hj_zero y']

/-- Reindexed version of `subsingleton_relative_of_inclusionBijective`: the relative homology
`H_m(X, A)` vanishes in *every* degree `m` when the inclusion `A ↪ X` is a homology equivalence. -/
lemma subsingleton_relative_of_inclusionBijective'
    (h : HomologyTheory.{u}) (P : TopPair)
    (hbij : ∀ m : ℤ, Function.Bijective (h.map m (inclusionSubToSpace P)))
    (m : ℤ) : Subsingleton (h.H m P) := by
  have hm : m = (m - 1) + 1 := (Int.sub_add_cancel m 1).symm
  rw [hm]
  exact subsingleton_relative_of_inclusionBijective h P hbij (m - 1)


/-- If `S ⊆ Y` is a deformation retract of `Y`, then the inclusion `S ↪ Y` induces an
isomorphism on homology in every degree (homotopy invariance applied to the retraction). -/
theorem inclusionSubToSpace_bijective_of_DR
    (h : HomologyTheory.{u}) (m : ℤ)
    {Y : Type u} [TopologicalSpace Y] (S : Set Y)
    (hdr : Nonempty (IsDeformationRetract S)) :
    Function.Bijective (h.map m (inclusionSubToSpace (⟨Y, inferInstance, S⟩ : TopPair))) := by sorry


/-- The image `[S]` of a deformation retract `S ⊆ Y` becomes a single point in the quotient
`Y / S`, and the inclusion `{[S]} ↪ Y / S` is a homology equivalence. -/
theorem quotientSpace_inclusionBijective_of_DR
    (h : HomologyTheory.{u}) (m : ℤ)
    {Y : Type u} [TopologicalSpace Y] (S : Set Y)
    (hdr : Nonempty (IsDeformationRetract S))
    {s : Y} (hs : s ∈ S) :
    Function.Bijective (h.map m (inclusionSubToSpace (@quotientPair Y _ S s hs))) := by sorry

/-- Bijectivity of the collapse map on relative homology *inside `B`*: when `A` is a
deformation retract of `B`, the map of pairs `(B, A) → (B/A, *)` induces an isomorphism on
homology (a key ingredient in the proof of Corollary 10.3). -/
theorem collapseSubspaceMap_bijective
    (h : HomologyTheory.{u}) (n : ℤ) (A B : Set X) {a : X} (ha : a ∈ A)
    (hAB : A ⊆ B) (hDR : IsSubspaceDeformationRetract A B) :
    Function.Bijective (h.map n (@collapseMapOfPairs ↥B _ (Subtype.val ⁻¹' A) ⟨a, hAB ha⟩ ha)) := by
  set P : TopPair := ⟨↥B, inferInstance, Subtype.val ⁻¹' A⟩
  set Q := @quotientPair ↥B _ (Subtype.val ⁻¹' A) ⟨a, hAB ha⟩ ha

  have h_source_triv : Subsingleton (h.H n P) :=
    subsingleton_relative_of_inclusionBijective' h P
      (fun m => inclusionSubToSpace_bijective_of_DR h m (Subtype.val ⁻¹' A) hDR.2) n

  have h_target_triv : Subsingleton (h.H n Q) :=
    subsingleton_relative_of_inclusionBijective' h Q
      (fun m => quotientSpace_inclusionBijective_of_DR h m (Subtype.val ⁻¹' A) hDR.2 ha) n

  exact ⟨fun x y _ => @Subsingleton.elim _ h_source_triv x y,
    fun y => ⟨0, @Subsingleton.elim _ h_target_triv _ _⟩⟩


/-- Under the excision hypothesis `closure A ⊆ interior B`, the inclusion `B/A ↪ X/A`
between quotient spaces is induced by a well-defined map of pairs, and this map is a
homology isomorphism. -/
theorem quotientInclusionMap_bijective
    (h : HomologyTheory.{u}) (n : ℤ) (A B : Set X) {a : X} (ha : a ∈ A)
    (hAB : A ⊆ B) (hClosure : closure A ⊆ interior B) :
    ∃ (f : MapOfPairs (@quotientPair ↥B _ (Subtype.val ⁻¹' A) ⟨a, hAB ha⟩ ha)
        (quotientPair A ha)),
      (∀ (b : ↥B), f.toFun (Quotient.mk (collapseSetoid (Subtype.val ⁻¹' A)) b) =
        Quotient.mk (collapseSetoid A) b.val) ∧
      Function.Bijective (h.map n f) := by sorry


/-- The composite map `H_n(B, A ∩ B) → H_n(X/A, *)` (collapse map composed with pair inclusion)
is bijective under the excision and deformation-retract hypotheses. Combines
`quotientInclusionMap_bijective` with `collapseSubspaceMap_bijective`. -/
theorem collapseFactorization_bijective
    (h : HomologyTheory.{u}) (n : ℤ) (A B : Set X)
    {a : X} (ha : a ∈ A)
    (hClosure : closure A ⊆ interior B) (hDR : IsSubspaceDeformationRetract A B) :
    Function.Bijective (collapseFactorization h n A B ha hClosure hDR) := by
  have hAB : A ⊆ B := fun x hx => interior_subset (hClosure (subset_closure hx))
  obtain ⟨jbar, hjbar_eq, hjbar_bij⟩ := quotientInclusionMap_bijective h n A B ha hAB hClosure
  have hq_bij := collapseSubspaceMap_bijective h n A B ha hAB hDR
  have hfact_eq : (collapseMapOfPairs A ha).comp (pairInclusion A B) =
      jbar.comp (@collapseMapOfPairs ↥B _ (Subtype.val ⁻¹' A) ⟨a, hAB ha⟩ ha) := by
    apply mapOfPairs_ext
    funext ⟨x, hx⟩
    simp only [MapOfPairs.comp, Function.comp, collapseMapOfPairs, pairInclusion]
    exact (hjbar_eq ⟨x, hx⟩).symm
  show Function.Bijective (h.map n ((collapseMapOfPairs A ha).comp (pairInclusion A B)))
  rw [hfact_eq]
  have key : h.map n (jbar.comp (@collapseMapOfPairs ↥B _ (Subtype.val ⁻¹' A) ⟨a, hAB ha⟩ ha)) =
      (h.map n jbar).comp (h.map n (@collapseMapOfPairs ↥B _ (Subtype.val ⁻¹' A) ⟨a, hAB ha⟩ ha)) :=
    h.map_comp n _ jbar
  exact key ▸ hjbar_bij.comp hq_bij


/-- Excision in subspace form: when `closure A ⊆ interior B`, the pair inclusion
`(B, A ∩ B) → (X, A)` induces an isomorphism on homology in every degree. Obtained by
transporting the excision theorem along the identification `(B, A ∩ B) ≅ (X ∖ Bᶜ, A ∖ Bᶜ)`. -/
theorem pairInclusion_homologyMap_bijective_of_closure
    (h : HomologyTheory.{u}) (n : ℤ) (A B : Set X)
    (hClosure : closure A ⊆ interior B) (hAB : A ⊆ B) :
    Function.Bijective (h.map n (pairInclusion A B)) := by sorry


/-- The collapse map of pairs `(X, A) → (X/A, *)` is a homology isomorphism whenever `A` is
contained in a larger subset `B` such that `closure A ⊆ interior B` and `A` is a deformation
retract of `B`. This is the technical heart of Corollary 10.3. -/
theorem collapseMapOfPairs_homologyMap_bijective_of_DR
    (h : HomologyTheory.{u}) (n : ℤ) (A B : Set X)
    {a : X} (ha : a ∈ A)
    (hClosure : closure A ⊆ interior B) (hDR : IsSubspaceDeformationRetract A B) :
    Function.Bijective (h.map n (collapseMapOfPairs A ha)) := by
  have hAB : A ⊆ B := hDR.1
  have hpair_bij := pairInclusion_homologyMap_bijective_of_closure h n A B hClosure hAB
  have hfact_bij := collapseFactorization_bijective h n A B ha hClosure hDR
  have hcomm : Function.Bijective
      (⇑((h.map n (collapseMapOfPairs A ha)).comp (h.map n (pairInclusion A B)))) := by
    have : (h.map n (collapseMapOfPairs A ha)).comp (h.map n (pairInclusion A B)) =
        collapseFactorization h n A B ha hClosure hDR :=
      (h.map_comp n (pairInclusion A B) (collapseMapOfPairs A ha)).symm
    rw [this]; exact hfact_bij
  exact (Function.Bijective.of_comp_iff (⇑(h.map n (collapseMapOfPairs A ha))) hpair_bij).mp hcomm

/-- **Corollary 10.3 (Quotient–pair excision).** *If `A ⊆ X` admits a neighbourhood `B`
such that `closure A ⊆ interior B` and `A` is a deformation retract of `B`, then the
quotient map of pairs `(X, A) → (X/A, *)` induces an isomorphism on homology in every degree.*

Concretely, this lets one compute the homology of a quotient `X / A` (with `*` the
collapsed point) in terms of the relative homology `H_n(X, A)`. -/
theorem collapseMapOfPairs_homologyMap_bijective
    (h : HomologyTheory.{u}) (n : ℤ) (A B : Set X)
    {a : X} (ha : a ∈ A)
    (hClosure : closure A ⊆ interior B)
    (hDR : IsSubspaceDeformationRetract A B) :
    Function.Bijective (h.map n (collapseMapOfPairs A ha)) :=
  collapseMapOfPairs_homologyMap_bijective_of_DR h n A B ha hClosure hDR

end ExcisionApplications

noncomputable section

open AlgebraicTopology CategoryTheory

namespace DegreeTheory

/-- The functor `Top ⥤ AddCommGrp` sending a space `X` to its `n`-th singular homology group
$H_n(X; \mathbb{Z})$ with integer coefficients. -/
abbrev homologyFunctorZ (n : ℕ) : TopCat.{0} ⥤ AddCommGrpCat :=
  (singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)

/-- Any endomorphism `f : ℤ ⟶ ℤ` in `AddCommGrp` is multiplication by `f 1`. -/
lemma addCommGrpCat_endZ_apply
    (f : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ) (x : ℤ) :
    f x = f 1 * x := by
  change (ConcreteCategory.hom f) x = (ConcreteCategory.hom f) 1 * x
  have h := (ConcreteCategory.hom f).map_zsmul 1 x
  simp only [smul_eq_mul, mul_one] at h
  rw [h, mul_comm]

/-- The *degree* of an endomorphism `e : G ⟶ G` of an abelian group `G ≅ ℤ`: transport `e`
along the chosen isomorphism `φ : G ≅ ℤ` and evaluate at `1`. -/
def degreeOfEndo {G : AddCommGrpCat} (φ : G ≅ AddCommGrpCat.of ℤ)
    (e : G ⟶ G) : ℤ :=
  (φ.inv ≫ e ≫ φ.hom) (1 : ℤ)

/-- Multiplicativity of degree: `deg(e₁ ∘ e₂) = deg(e₁) · deg(e₂)`. -/
lemma degreeOfEndo_comp {G : AddCommGrpCat} (φ : G ≅ AddCommGrpCat.of ℤ)
    (e₁ e₂ : G ⟶ G) :
    degreeOfEndo φ (e₁ ≫ e₂) = degreeOfEndo φ e₁ * degreeOfEndo φ e₂ := by
  simp only [degreeOfEndo]
  have hfact : (φ.inv ≫ (e₁ ≫ e₂) ≫ φ.hom : AddCommGrpCat.of ℤ ⟶ _) =
      (φ.inv ≫ e₁ ≫ φ.hom) ≫ (φ.inv ≫ e₂ ≫ φ.hom) := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have h1 : ((φ.inv ≫ (e₁ ≫ e₂) ≫ φ.hom : AddCommGrpCat.of ℤ ⟶ _) (1 : ℤ)) =
      ((φ.inv ≫ e₂ ≫ φ.hom) ((φ.inv ≫ e₁ ≫ φ.hom) (1 : ℤ))) := by
    rw [hfact]; rfl
  rw [h1, addCommGrpCat_endZ_apply (φ.inv ≫ e₂ ≫ φ.hom)]
  ring

/-- The degree of the identity endomorphism is `1`. -/
lemma degreeOfEndo_id {G : AddCommGrpCat} (φ : G ≅ AddCommGrpCat.of ℤ) :
    degreeOfEndo φ (𝟙 G) = 1 := by
  simp only [degreeOfEndo, Category.id_comp, Iso.inv_hom_id]; rfl

/-- Under the identification `G ≅ ℤ`, the transported endomorphism acts as multiplication by
the degree of `e`. -/
lemma degreeOfEndo_eq_smul {G : AddCommGrpCat} (φ : G ≅ AddCommGrpCat.of ℤ)
    (e : G ⟶ G) (x : ℤ) :
    (φ.inv ≫ e ≫ φ.hom) x = degreeOfEndo φ e * x :=
  addCommGrpCat_endZ_apply (φ.inv ≫ e ≫ φ.hom) x

/-- The homotopy equivalence relation on self-maps of `S`: two continuous maps `f, g : S → S`
are related iff there is a homotopy from `f` to `g`. -/
def selfMapSetoid (S : TopCat.{0}) : Setoid (S ⟶ S) where
  r f g := Nonempty (TopCat.Homotopy f g)
  iseqv := {
    refl := fun _ => ⟨ContinuousMap.Homotopy.refl _⟩
    symm := fun ⟨H⟩ => ⟨H.symm⟩
    trans := fun ⟨H₁⟩ ⟨H₂⟩ => ⟨H₁.trans H₂⟩
  }

/-- Homotopy classes of self-maps of `S`, denoted `[S, S]`. -/
def SelfMapHomotopyClass (S : TopCat.{0}) := Quotient (selfMapSetoid S)

/-- The monoid structure on `[S, S]` induced by composition of representatives. -/
instance (S : TopCat.{0}) : Monoid (SelfMapHomotopyClass S) where
  mul := Quotient.lift₂ (fun f g => @Quotient.mk _ (selfMapSetoid S) (f ≫ g))
    (fun _ _ _ _ hf hg => Quotient.sound (ContinuousMap.Homotopic.comp hg hf))
  one := @Quotient.mk _ (selfMapSetoid S) (𝟙 S)
  mul_assoc := by
    intro a b c
    induction a using Quotient.inductionOn
    induction b using Quotient.inductionOn
    induction c using Quotient.inductionOn
    apply Quotient.sound; show Nonempty _
    rw [Category.assoc]; exact ⟨ContinuousMap.Homotopy.refl _⟩
  one_mul := by
    intro a; induction a using Quotient.inductionOn
    apply Quotient.sound; show Nonempty _
    rw [Category.id_comp]; exact ⟨ContinuousMap.Homotopy.refl _⟩
  mul_one := by
    intro a; induction a using Quotient.inductionOn
    apply Quotient.sound; show Nonempty _
    rw [Category.comp_id]; exact ⟨ContinuousMap.Homotopy.refl _⟩

/-- The *degree homomorphism* `deg : [S, S] → ℤ` for a space `S` with `H_n(S) ≅ ℤ`: assigns
to each homotopy class of self-maps `[f]` the degree of the induced endomorphism of
`H_n(S)`. Multiplicative under composition. -/
def degreeHom (n : ℕ) (S : TopCat.{0})
    (φ : (homologyFunctorZ n).obj S ≅ AddCommGrpCat.of ℤ) :
    SelfMapHomotopyClass S →* ℤ where
  toFun := Quotient.lift (fun f => degreeOfEndo φ ((homologyFunctorZ n).map f))
    (fun _ _ ⟨H⟩ => by
      show degreeOfEndo φ _ = degreeOfEndo φ _
      congr 1
      exact H.congr_homologyMap_singularChainComplexFunctor (AddCommGrpCat.of ℤ) n)
  map_one' := by
    show degreeOfEndo φ ((homologyFunctorZ n).map (𝟙 S)) = 1
    rw [(homologyFunctorZ n).map_id S]; exact degreeOfEndo_id φ
  map_mul' := by
    intro a b
    induction a using Quotient.inductionOn
    induction b using Quotient.inductionOn
    show degreeOfEndo φ ((homologyFunctorZ n).map (_ ≫ _)) = _
    rw [(homologyFunctorZ n).map_comp]
    exact degreeOfEndo_comp φ _ _

/-- The `n`-sphere `S^n ⊆ ℝ^{n+1}` packaged as an object of `TopCat`. -/
def sphereTopCat (n : ℕ) : TopCat.{0} :=
  TopCat.of (SphereHomology.Sphere n)


/-- Base case for the surjectivity of degree on `S^1`: for every integer `k`, the
self-map `z ↦ z^k` of `S^1` has degree `k`. -/
theorem exists_selfmap_of_degree_one
    (φ : (homologyFunctorZ 1).obj (sphereTopCat 1) ≅ AddCommGrpCat.of ℤ)
    (k : ℤ) : ∃ f : sphereTopCat 1 ⟶ sphereTopCat 1,
    degreeOfEndo φ ((homologyFunctorZ 1).map f) = k := by sorry


/-- The degree of an endomorphism is independent of the chosen isomorphism `G ≅ ℤ`: any two
isomorphisms differ by an automorphism of `ℤ` (i.e. `±1`), and the conjugation cancels. -/
lemma degreeOfEndo_iso_independent {G : AddCommGrpCat}
    (φ φ' : G ≅ AddCommGrpCat.of ℤ) (e : G ⟶ G) :
    degreeOfEndo φ e = degreeOfEndo φ' e := by
  simp only [degreeOfEndo]
  set σ := φ.symm ≪≫ φ'
  have hφ'_hom : φ'.hom = φ.hom ≫ σ.hom := by
    simp [σ, Iso.trans, Iso.symm]
  have hφ'_inv : φ'.inv = σ.inv ≫ φ.inv := by
    simp [σ, Iso.trans, Iso.symm]
  rw [hφ'_inv, hφ'_hom]
  simp only [Category.assoc]


  change (ConcreteCategory.hom (φ.inv ≫ e ≫ φ.hom)) 1 =
    (ConcreteCategory.hom σ.hom)
      ((ConcreteCategory.hom (φ.inv ≫ e ≫ φ.hom))
        ((ConcreteCategory.hom σ.inv) 1))
  rw [addCommGrpCat_endZ_apply (φ.inv ≫ e ≫ φ.hom) ((ConcreteCategory.hom σ.inv) 1)]
  rw [show (ConcreteCategory.hom (φ.inv ≫ e ≫ φ.hom)) 1 *
      (ConcreteCategory.hom σ.inv) 1 =
      ((ConcreteCategory.hom (φ.inv ≫ e ≫ φ.hom)) 1) •
      ((ConcreteCategory.hom σ.inv) 1) from by ring]
  rw [(ConcreteCategory.hom σ.hom).map_zsmul]
  have hσ : (ConcreteCategory.hom σ.hom) ((ConcreteCategory.hom σ.inv) 1) = (1 : ℤ) := by
    change (ConcreteCategory.hom (σ.inv ≫ σ.hom)) 1 = 1
    simp [Iso.inv_hom_id]
  rw [hσ]; simp [mul_one]


/-- Conjugation invariance of degree: transporting `e` across an isomorphism `α : G ≅ H`
preserves its degree (with respect to compatible identifications of `G` and `H` with `ℤ`). -/
lemma degreeOfEndo_conj {G H : AddCommGrpCat}
    (φ : G ≅ AddCommGrpCat.of ℤ) (ψ : H ≅ AddCommGrpCat.of ℤ)
    (α : G ≅ H) (e : G ⟶ G) :
    degreeOfEndo ψ (α.inv ≫ e ≫ α.hom) = degreeOfEndo φ e := by


  have h : degreeOfEndo ψ (α.inv ≫ e ≫ α.hom) = degreeOfEndo (α ≪≫ ψ) e := by
    simp only [degreeOfEndo, Iso.trans_hom, Iso.trans_inv, Category.assoc]
  rw [h]
  exact degreeOfEndo_iso_independent (α ≪≫ ψ) φ e


/-- Safe normalization map `ℝ^{n+1} → S^n`: sends a non-zero vector `w` to `w / ‖w‖` and
maps `0` to the basepoint `e_0`, so as to be defined everywhere. -/
noncomputable def suspSafeNorm (n : ℕ) (w : EuclideanSpace ℝ (Fin (n + 1))) :
    SphereHomology.Sphere n :=
  if hw : w = 0 then ⟨EuclideanSpace.single 0 1, by simp [mem_sphere_iff_norm]⟩
  else ⟨‖w‖⁻¹ • w, by
    simp [mem_sphere_iff_norm, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]⟩

/-- Project an element of `ℝ^{n+2}` onto its first `n+1` coordinates, viewed as an element
of `ℝ^{n+1}`. -/
noncomputable def suspInitProj (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 2))) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  (EuclideanSpace.equiv _ _).symm (fun i => v (Fin.castSucc i))

/-- Append a real scalar `t` as the last coordinate to a vector in `ℝ^{n+1}`, producing a
vector in `ℝ^{n+2}`. -/
noncomputable def suspSnocProj (n : ℕ) (w : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) :
    EuclideanSpace ℝ (Fin (n + 2)) :=
  (EuclideanSpace.equiv _ _).symm (Fin.snoc (EuclideanSpace.equiv _ _ w) t)

/-- The *raw suspension* of a self-map `f : S^n → S^n`: a map `ℝ^{n+2} → ℝ^{n+2}` that scales
the first `n+1` coordinates by `f` (after radial normalization) and leaves the last
coordinate unchanged. Restricted to `S^{n+1}` this defines the topological suspension. -/
noncomputable def suspRaw (n : ℕ) (f : sphereTopCat n ⟶ sphereTopCat n)
    (v : EuclideanSpace ℝ (Fin (n + 2))) : EuclideanSpace ℝ (Fin (n + 2)) :=
  suspSnocProj n
    (‖suspInitProj n v‖ • (f.1 (suspSafeNorm n (suspInitProj n v))).val)
    (v (Fin.last (n + 1)))

/-- The raw suspension `suspRaw n f` preserves the unit sphere: if `‖v‖ = 1` then
`‖suspRaw n f v‖ = 1`. This is what makes `suspRaw` descend to a well-defined map
`S^{n+1} → S^{n+1}`. -/
lemma suspRaw_norm (n : ℕ) (f : sphereTopCat n ⟶ sphereTopCat n)
    (v : EuclideanSpace ℝ (Fin (n + 2))) (hv : ‖v‖ = 1) :
    ‖suspRaw n f v‖ = 1 := by
  have sph_norm_fact : ‖(f.1 (suspSafeNorm n (suspInitProj n v))).val‖ = 1 := by
    have := (f.1 (suspSafeNorm n (suspInitProj n v))).property
    rwa [Metric.mem_sphere, dist_zero_right] at this
  have snoc_norm : ‖suspRaw n f v‖ ^ 2 =
      ‖(‖suspInitProj n v‖ • (f.1 (suspSafeNorm n (suspInitProj n v))).val)‖ ^ 2 +
      (v (Fin.last (n + 1))) ^ 2 := by
    simp [suspRaw, EuclideanSpace.real_norm_sq_eq, suspSnocProj, Fin.sum_univ_castSucc,
          Fin.snoc_castSucc, Fin.snoc_last]
  rw [norm_smul, Real.norm_of_nonneg (norm_nonneg _), sph_norm_fact, mul_one] at snoc_norm
  have norm_decomp : 1 = ‖suspInitProj n v‖ ^ 2 + (v (Fin.last (n + 1))) ^ 2 := by
    have := congr_arg (· ^ 2) hv; simp only [one_pow] at this; rw [← this]
    simp [EuclideanSpace.real_norm_sq_eq, suspInitProj, Fin.sum_univ_castSucc]
  nlinarith [norm_nonneg (suspRaw n f v), sq_nonneg (‖suspRaw n f v‖ - 1),
             snoc_norm.trans norm_decomp.symm]

/-- Away from zero, the safe normalization map is given by the expected formula
`w ↦ w / ‖w‖`. -/
lemma suspSafeNorm_val_of_ne_zero (n : ℕ) (w : EuclideanSpace ℝ (Fin (n + 1)))
    (hw : w ≠ 0) : (suspSafeNorm n w).val = ‖w‖⁻¹ • w := by
  simp [suspSafeNorm, hw]

/-- Continuity of the raw suspension `suspRaw n f`. The only non-trivial point is `w = 0`
in the first `n+1` coordinates, where the radial normalization is squeezed to `0` by the
boundedness `‖f(·)‖ = 1`. -/
lemma continuous_suspRaw (n : ℕ) (f : sphereTopCat n ⟶ sphereTopCat n) :
    Continuous (suspRaw n f) := by
  unfold suspRaw suspSnocProj
  apply (EuclideanSpace.equiv _ _).symm.continuous.comp
  apply continuous_pi; intro i
  refine Fin.lastCases ?_ ?_ i
  · simp only [Fin.snoc_last]
    exact (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last (n + 1))).continuous
  · intro j; simp only [Fin.snoc_castSucc]
    have h_init_cont : Continuous (suspInitProj n) := by
      apply (EuclideanSpace.equiv _ _).symm.continuous.comp
      exact continuous_pi (fun i => (EuclideanSpace.proj (𝕜 := ℝ) (Fin.castSucc i)).continuous)
    have h_core : Continuous (fun w : EuclideanSpace ℝ (Fin (n + 1)) =>
        ‖w‖ • (f.1 (suspSafeNorm n w)).val) := by
      rw [continuous_iff_continuousAt]; intro w; by_cases hw : w = 0
      · subst hw
        change Filter.Tendsto _ (nhds 0)
          (nhds (‖(0 : EuclideanSpace ℝ (Fin (n + 1)))‖ • _))
        simp only [norm_zero, zero_smul]
        apply squeeze_zero_norm
          (f := fun x => ‖x‖ • (f.1 (suspSafeNorm n x)).val)
        · intro x
          have : ‖(f.1 (suspSafeNorm n x)).val‖ = 1 := by
            have := (f.1 (suspSafeNorm n x)).property
            rwa [Metric.mem_sphere, dist_zero_right] at this
          rw [norm_smul, Real.norm_of_nonneg (norm_nonneg _), this, mul_one]
        · simpa [norm_zero] using
            continuous_norm.tendsto (0 : EuclideanSpace ℝ (Fin (n + 1)))
      · apply ContinuousAt.smul continuous_norm.continuousAt
        have h_sNorm_at : ContinuousAt (suspSafeNorm n) w := by
          have hval : ContinuousAt (fun x => (suspSafeNorm n x).val) w :=
            (ContinuousAt.smul
              (ContinuousAt.inv₀ continuous_norm.continuousAt (norm_ne_zero_iff.mpr hw))
              continuousAt_id).congr
              (Filter.eventually_of_mem (isOpen_ne.mem_nhds hw)
                (fun x hx => (suspSafeNorm_val_of_ne_zero n x hx).symm))
          rw [ContinuousAt] at hval ⊢
          change Filter.Tendsto (suspSafeNorm n) (nhds w)
            (@nhds (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) _ _)
          rw [nhds_subtype]
          exact Filter.tendsto_comap_iff.mpr hval

        exact (continuous_subtype_val.comp f.1.continuous).continuousAt.comp h_sNorm_at
    exact ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp (h_core.comp h_init_cont))

/-- The (unreduced) **suspension** `Σf : S^{n+1} → S^{n+1}` of a self-map `f : S^n → S^n`,
obtained by restricting `suspRaw n f` to the unit sphere. -/
noncomputable def suspensionOfSphereMap (n : ℕ) (_hn : n ≥ 1)
    (f : sphereTopCat n ⟶ sphereTopCat n) :
    sphereTopCat (n + 1) ⟶ sphereTopCat (n + 1) :=
  ⟨⟨fun v => ⟨suspRaw n f v.val, by
      rw [Metric.mem_sphere, dist_zero_right]
      exact suspRaw_norm n f v.val
        (by have := v.property; rwa [Metric.mem_sphere, dist_zero_right] at this)⟩,
    Continuous.subtype_mk ((continuous_suspRaw n f).comp continuous_subtype_val) _⟩⟩


/-- Suspension preserves degree: `deg(Σf) = deg(f)` for any self-map `f : S^n → S^n`.
This is the inductive step used to extend `exists_selfmap_of_degree_one` from `S^1` to all
spheres `S^n`, `n ≥ 1`. -/
theorem suspensionMap_degree_eq (n : ℕ) (hn : n ≥ 1)
    (f : sphereTopCat n ⟶ sphereTopCat n)
    (φ : (homologyFunctorZ n).obj (sphereTopCat n) ≅ AddCommGrpCat.of ℤ)
    (ψ : (homologyFunctorZ (n + 1)).obj (sphereTopCat (n + 1)) ≅ AddCommGrpCat.of ℤ) :
    degreeOfEndo ψ ((homologyFunctorZ (n + 1)).map (suspensionOfSphereMap n hn f)) =
    degreeOfEndo φ ((homologyFunctorZ n).map f) := by sorry


/-- Two endomorphisms of `ℤ` (in `AddCommGrp`) agree iff they agree on `1`. -/
lemma addCommGrpCat_endZ_eq_of_apply_one
    (e₁ e₂ : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ)
    (h : (ConcreteCategory.hom e₁) (1 : ℤ) = (ConcreteCategory.hom e₂) (1 : ℤ)) :
    e₁ = e₂ := by
  apply ConcreteCategory.hom_ext
  intro x
  have h1 := (ConcreteCategory.hom e₁).map_zsmul 1 x
  have h2 := (ConcreteCategory.hom e₂).map_zsmul 1 x
  simp only [smul_eq_mul, mul_one] at h1 h2
  rw [h1, h2, h]


/-- Two endomorphisms of `G ≅ ℤ` are equal iff they have the same degree. -/
lemma endo_eq_of_same_degree' {G : AddCommGrpCat}
    (φ : G ≅ AddCommGrpCat.of ℤ)
    (e₁ e₂ : G ⟶ G)
    (h : degreeOfEndo φ e₁ = degreeOfEndo φ e₂) :
    e₁ = e₂ := by
  have key : φ.inv ≫ e₁ ≫ φ.hom = φ.inv ≫ e₂ ≫ φ.hom :=
    addCommGrpCat_endZ_eq_of_apply_one _ _ h
  calc e₁ = φ.hom ≫ (φ.inv ≫ e₁ ≫ φ.hom) ≫ φ.inv := by
        simp [Iso.hom_inv_id_assoc]
    _ = φ.hom ≫ (φ.inv ≫ e₂ ≫ φ.hom) ≫ φ.inv := by rw [key]
    _ = e₂ := by simp [Iso.hom_inv_id_assoc]

/-- The homology endomorphism induced by `Σf : S^{n+1} → S^{n+1}` agrees, up to the
suspension isomorphism `α : H_n(S^n) ≅ H_{n+1}(S^{n+1})`, with the endomorphism induced by
`f` on `H_n(S^n)`. -/
theorem suspensionMap_homology_eq (n : ℕ) (hn : n ≥ 1)
    (f : sphereTopCat n ⟶ sphereTopCat n)
    (α : SingularHomologyGroup n (SphereHomology.Sphere n) ≅
         SingularHomologyGroup (n + 1) (SphereHomology.Sphere (n + 1))) :
    (homologyFunctorZ (n + 1)).map (suspensionOfSphereMap n hn f) =
      α.inv ≫ (homologyFunctorZ n).map f ≫ α.hom := by

  obtain ⟨ψ⟩ := SphereHomology.sphere_homology_top (n + 1) (by omega)
  obtain ⟨φ⟩ := SphereHomology.sphere_homology_top n (by omega)
  apply endo_eq_of_same_degree' ψ


  exact (suspensionMap_degree_eq n hn f φ ψ).trans
    (degreeOfEndo_conj φ ψ α ((homologyFunctorZ n).map f)).symm


/-- Inductive step for `exists_selfmap_of_degree`: if every integer is realized as a degree
of a self-map of `S^n`, then the same holds for `S^{n+1}` (take the suspension). -/
theorem exists_selfmap_of_degree_succ (n : ℕ) (hn : n ≥ 1)
    (φ : (homologyFunctorZ n).obj (sphereTopCat n) ≅ AddCommGrpCat.of ℤ)
    (ψ : (homologyFunctorZ (n + 1)).obj (sphereTopCat (n + 1)) ≅ AddCommGrpCat.of ℤ)
    (k : ℤ)
    (hk : ∃ f : sphereTopCat n ⟶ sphereTopCat n,
      degreeOfEndo φ ((homologyFunctorZ n).map f) = k) :
    ∃ g : sphereTopCat (n + 1) ⟶ sphereTopCat (n + 1),
      degreeOfEndo ψ ((homologyFunctorZ (n + 1)).map g) = k := by
  obtain ⟨f, hf⟩ := hk
  obtain ⟨α⟩ := SphereHomology.suspension_homology_iso n n hn
  have hdeg : degreeOfEndo ψ (α.inv ≫ (homologyFunctorZ n).map f ≫ α.hom) = k :=
    (degreeOfEndo_conj φ ψ α ((homologyFunctorZ n).map f)).trans hf
  exact ⟨suspensionOfSphereMap n hn f,
    hdeg ▸ congrArg (degreeOfEndo ψ) (suspensionMap_homology_eq n hn f α)⟩


/-- For every `n ≥ 1` and every integer `k`, there exists a self-map of `S^n` of degree `k`.
Proved by induction on `n`: base case `n = 1` is `exists_selfmap_of_degree_one`, induction
step is `exists_selfmap_of_degree_succ`. -/
lemma exists_selfmap_of_degree (n : ℕ) (hn : n ≥ 1)
    (φ : (homologyFunctorZ n).obj (sphereTopCat n) ≅ AddCommGrpCat.of ℤ)
    (k : ℤ) : ∃ f : sphereTopCat n ⟶ sphereTopCat n,
    degreeOfEndo φ ((homologyFunctorZ n).map f) = k := by
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hm : m = 0
    · subst hm; exact exists_selfmap_of_degree_one φ k
    · have hm1 : m ≥ 1 := Nat.one_le_iff_ne_zero.mpr hm
      obtain ⟨φm⟩ := SphereHomology.sphere_homology_top m (by omega)
      exact exists_selfmap_of_degree_succ m hm1 φm φ k (ih hm1 φm)


/-- **Theorem 10.8 (Surjectivity of degree).** *For every `n ≥ 1`, the degree homomorphism
`deg : [S^n, S^n] → ℤ` is surjective: every integer is realized as the degree of some
continuous self-map of the `n`-sphere.* -/
theorem degree_surjective (n : ℕ) (hn : n ≥ 1)
    (φ : (homologyFunctorZ n).obj (sphereTopCat n) ≅ AddCommGrpCat.of ℤ) :
    Function.Surjective (degreeHom n (sphereTopCat n) φ) := by
  intro k
  obtain ⟨f, hf⟩ := exists_selfmap_of_degree n hn φ k
  exact ⟨@Quotient.mk _ (selfMapSetoid (sphereTopCat n)) f, hf⟩

/-- Negating one coordinate of a point on `S^n` produces another point on `S^n` (the
coordinate-reflected image). -/
lemma update_neg_mem_sphere (n : ℕ) (i : Fin (n + 1))
    (x : SphereHomology.Sphere n) :
    (WithLp.equiv 2 _).symm (Function.update (WithLp.equiv 2 _ x.1) i (-(x.1 i))) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  have hx := x.2
  simp only [Metric.mem_sphere, dist_zero_right] at hx ⊢
  simp only [EuclideanSpace.norm_eq] at hx ⊢
  rw [show (∑ j : Fin (n + 1), ‖((WithLp.equiv 2 _).symm
    (Function.update (WithLp.equiv 2 _ x.1) i (-(x.1 i)))).ofLp j‖ ^ 2) =
    (∑ j : Fin (n + 1), ‖x.1.ofLp j‖ ^ 2) from by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = i
      · subst h; simp [Function.update_self, norm_neg]
      · simp [Function.update_of_ne h]]
  exact hx

/-- The coordinate reflection map on `ℝ^{n+1}` (negating the `i`-th coordinate) is
continuous. -/
lemma continuous_update_neg (n : ℕ) (i : Fin (n + 1)) :
    Continuous (fun v : EuclideanSpace ℝ (Fin (n + 1)) =>
      (WithLp.equiv 2 _).symm (Function.update (WithLp.equiv 2 _ v) i (-(v i)))) :=
  (PiLp.homeomorph 2 (fun _ : Fin (n + 1) => ℝ)).symm.continuous.comp
    (Continuous.update (PiLp.homeomorph 2 (fun _ : Fin (n + 1) => ℝ)).continuous i
      (((continuous_apply i).comp
        (PiLp.homeomorph 2 (fun _ : Fin (n + 1) => ℝ)).continuous).neg))

/-- The *antipodal map* `S^n → S^n`, `x ↦ -x`. Has degree `(-1)^{n+1}`. -/
def antipodalMap (n : ℕ) : sphereTopCat n ⟶ sphereTopCat n :=
  ⟨⟨fun x => ⟨-x.1, by
      have hx := x.2
      simp only [Metric.mem_sphere, dist_zero_right] at hx ⊢
      rw [norm_neg]; exact hx⟩,
    (continuous_neg.comp continuous_subtype_val).subtype_mk _⟩⟩

/-- The *coordinate reflection* `r_i : S^n → S^n` that negates the `i`-th coordinate and
fixes the others. Has degree `-1`. -/
def coordReflection (n : ℕ) (i : Fin (n + 1)) : sphereTopCat n ⟶ sphereTopCat n :=
  ⟨⟨fun x => ⟨(WithLp.equiv 2 _).symm
      (Function.update (WithLp.equiv 2 _ x.1) i (-(x.1 i))),
      update_neg_mem_sphere n i x⟩,
    (continuous_update_neg n i).comp continuous_subtype_val |>.subtype_mk _⟩⟩

/-- The composition of the first `k` coordinate reflections `r_{k-1} ∘ ... ∘ r_0`, a self-map
of `S^n`. Taking `k = n + 1` recovers the antipodal map (up to homotopy). -/
def iteratedReflection (n : ℕ) :
    (k : ℕ) → (hk : k ≤ n + 1) → (sphereTopCat n ⟶ sphereTopCat n)
  | 0, _ => 𝟙 _
  | k + 1, hk => coordReflection n ⟨k, by omega⟩ ≫ iteratedReflection n k (by omega)


/-- Each coordinate reflection `r_i : S^n → S^n` has degree `-1`. -/
theorem degree_coordReflection (n : ℕ) (i : Fin (n + 1))
    (φ : (homologyFunctorZ n).obj (sphereTopCat n) ≅ AddCommGrpCat.of ℤ) :
    degreeOfEndo φ ((homologyFunctorZ n).map (coordReflection n i)) = -1 := by sorry


/-- The antipodal map `x ↦ -x` is homotopic (and hence equal in homology) to the composition
of all `n + 1` coordinate reflections. -/
theorem iteratedReflection_full (n : ℕ)
    (φ : (homologyFunctorZ n).obj (sphereTopCat n) ≅ AddCommGrpCat.of ℤ) :
    degreeOfEndo φ ((homologyFunctorZ n).map (antipodalMap n)) =
    degreeOfEndo φ ((homologyFunctorZ n).map (iteratedReflection n (n + 1) le_rfl)) := by sorry

/-- The degree of `iteratedReflection n k` equals `(-1)^k`, by multiplicativity of degree and
`degree_coordReflection`. In particular, taking `k = n + 1` shows that the antipodal map has
degree `(-1)^{n+1}`. -/
theorem degree_iteratedReflection (n : ℕ)
    (φ : (homologyFunctorZ n).obj (sphereTopCat n) ≅ AddCommGrpCat.of ℤ)
    (k : ℕ) (hk : k ≤ n + 1) :
    degreeOfEndo φ ((homologyFunctorZ n).map (iteratedReflection n k hk)) = (-1) ^ k := by
  induction k with
  | zero =>
    simp only [iteratedReflection]
    rw [(homologyFunctorZ n).map_id]
    exact degreeOfEndo_id φ
  | succ m ih =>
    simp only [iteratedReflection, pow_succ]
    rw [(homologyFunctorZ n).map_comp]
    rw [degreeOfEndo_comp φ]
    rw [degree_coordReflection n ⟨m, by omega⟩ φ]
    rw [ih (by omega)]
    ring

end DegreeTheory
