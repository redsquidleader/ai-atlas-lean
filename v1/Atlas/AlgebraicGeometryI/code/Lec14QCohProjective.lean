/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

/-- A sheaf of `O_X`-modules `ℱ` is quasi-coherent (Def 24, Lec 10) — abbreviation for
the mathlib predicate `SheafOfModules.IsQuasicoherent`. -/
def IsQuasicoherentSheaf {X : Scheme.{u}} (ℱ : X.Modules) : Prop :=
  ℱ.IsQuasicoherent

/-- Predicate for being a coherent sheaf of `O_X`-modules (Lec 10, Def 25 + finite
type). Placeholder — to be specialized to mathlib's coherence notion. -/
noncomputable def IsCoherentSheaf : {X : Scheme.{u}} → X.Modules → Prop := by sorry

/-- A graded module over a graded ring `𝒜 = ⨁ₙ 𝒜ₙ`: an `A`-module `carrier` together
with a `ℤ`-indexed decomposition `carrier = ⨁_d component d` compatible with the grading
in the sense `𝒜ₙ · component d ⊆ component (n + d)`. -/
structure GrMod {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] where
  carrier : Type u
  [instAddCommGroup : AddCommGroup carrier]
  [instModule : Module A carrier]
  component : ℤ → AddSubgroup carrier
  internal : DirectSum.IsInternal component
  graded_smul : ∀ (n : ℕ) (d : ℤ) (a : A) (m : carrier),
    a ∈ (𝒜 n : Set A) → m ∈ component d → a • m ∈ component (↑n + d)

attribute [instance] GrMod.instAddCommGroup GrMod.instModule

namespace GrMod

variable {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- A graded module is finitely generated if its underlying `A`-module is finite. -/
def IsFinitelyGenerated (M : GrMod 𝒜) : Prop :=
  Module.Finite A M.carrier

/-- A graded module is "finite-dimensional" (concentrated in finitely many degrees) if
all but finitely many graded components vanish. -/
def IsFiniteDimensional (M : GrMod 𝒜) : Prop :=
  ∃ (S : Finset ℤ), ∀ d, d ∉ S → M.component d = ⊥

/-- A graded module is locally nilpotent with respect to the irrelevant ideal `𝒜₊` if
every element is annihilated by a power of every element of `𝒜₊`. -/
def IsLocallyNilpotent (M : GrMod 𝒜) : Prop :=
  ∀ (x : M.carrier), ∃ (d : ℕ),
    ∀ (a : A), a ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal → a ^ d • x = 0

/-- A morphism of graded modules: an underlying `A`-linear map (here without graded
constraints — kept as a flexible wrapper). -/
structure Hom (M N : GrMod 𝒜) where
  toLinearMap : M.carrier →ₗ[A] N.carrier

/-- Extensionality for `GrMod.Hom`: two morphisms are equal iff their underlying
linear maps coincide. -/
@[ext]
theorem Hom.ext {M N : GrMod 𝒜} {f g : Hom M N}
    (h : f.toLinearMap = g.toLinearMap) : f = g := by
  cases f; cases g; congr

/-- A short exact sequence of graded modules `0 → M₁ → M₂ → M₃ → 0`, packaged with
injectivity of `f`, surjectivity of `g`, and exactness `ker g = range f`. -/
structure ShortExact (M₁ M₂ M₃ : GrMod 𝒜) where
  f : M₁.carrier →ₗ[A] M₂.carrier
  g : M₂.carrier →ₗ[A] M₃.carrier
  f_injective : Function.Injective f
  g_surjective : Function.Surjective g
  exact : LinearMap.ker g = LinearMap.range f

/-- Shift `A(d)` of the graded ring viewed as a graded module: the module `A` with
grading translated by `d`. -/
noncomputable def shift
    {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℤ) : GrMod 𝒜 := by sorry

/-- Direct sum of `k` copies of a graded module `M`, again a graded module. -/
noncomputable def directSumCopies (M : GrMod 𝒜) (k : ℕ) : GrMod 𝒜 := by sorry

/-- Kernel of an `A`-linear map between graded modules, packaged as a graded module. -/
noncomputable def kernelGrMod (M N : GrMod 𝒜) (f : M.carrier →ₗ[A] N.carrier) : GrMod 𝒜 := by sorry

/-- Any surjection `f : M ↠ N` of graded modules gives rise to a short exact sequence
`0 → ker f → M → N → 0`. -/
noncomputable def shortExactOfSurjection (M N : GrMod 𝒜) (f : M.carrier →ₗ[A] N.carrier)
    (hf : Function.Surjective f) :
    ShortExact (kernelGrMod M N f) M N := by sorry

end GrMod

/-- Category instance on graded modules over `𝒜`: morphisms are `GrMod.Hom`, identity
and composition come from the underlying linear maps. -/
instance grModCategory {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] : Category (GrMod 𝒜) where
  Hom := GrMod.Hom
  id M := ⟨LinearMap.id⟩
  comp f g := ⟨g.toLinearMap.comp f.toLinearMap⟩
  id_comp f := by apply GrMod.Hom.ext; simp
  comp_id f := by apply GrMod.Hom.ext; simp
  assoc f g h := by apply GrMod.Hom.ext; simp [LinearMap.comp_assoc]

/-- The "tilde" construction on `Proj 𝒜`: associates to a graded module `M` a sheaf
of `O_{Proj 𝒜}`-modules `M̃`. -/
noncomputable def tildeProj {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (M : GrMod 𝒜) :
    (Proj 𝒜).Modules := sorry

/-- Functoriality of the tilde construction on `Proj 𝒜`: a graded-module map `f`
induces a morphism of sheaves `M̃ → Ñ`. -/
noncomputable def tildeProj_map {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {M N : GrMod 𝒜} (f : GrMod.Hom M N) :
    (tildeProj 𝒜 M ⟶ tildeProj 𝒜 N) := sorry

/-- On a Noetherian topological space, the sections functor `Γ(U, –)` commutes with
filtered colimits of sheaves: `Γ(U, colim Fⱼ) ≅ colim Γ(U, Fⱼ)`. -/
theorem sections_commute_with_filtered_colimits
    {C : Type (u+1)} [Category.{u} C]
    (X : TopCat.{u}) [NoetherianSpace X]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ TopCat.Sheaf C X)
    [HasColimit F]
    [HasColimitsOfShape J C]
    (U : Opens X) :
    let forget := TopCat.Sheaf.forget C X
    let sectionsF : J ⥤ C :=
      F ⋙ forget ⋙ (evaluation (Opens (X : TopCat))ᵒᵖ C).obj (Opposite.op U)
    Nonempty ((forget.obj (colimit F)).obj (Opposite.op U) ≅
      colimit sectionsF) := by sorry

variable {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The tilde functor on `Proj 𝒜` preserves short exact sequences of graded modules. -/
theorem tildeProj_exact
    (M₁ M₂ M₃ : GrMod 𝒜)
    (ses : GrMod.ShortExact M₁ M₂ M₃) :
    ∃ (w : tildeProj_map 𝒜 ⟨ses.f⟩ ≫ tildeProj_map 𝒜 ⟨ses.g⟩ = 0),
      (ShortComplex.mk (tildeProj_map 𝒜 ⟨ses.f⟩)
        (tildeProj_map 𝒜 ⟨ses.g⟩) w).ShortExact := by sorry

/-- Inverse construction: associates to a sheaf `ℱ` on `Proj 𝒜` an underlying graded
module (the "Γ_*" graded module of global sections of all twists). -/
noncomputable def gradedModuleOfSheaf (ℱ : (Proj 𝒜).Modules) : GrMod 𝒜 := sorry

/-- Proposition 20 (Lec 14): for a quasi-coherent sheaf `ℱ` on `Proj 𝒜`, applying
`tildeProj` to `gradedModuleOfSheaf ℱ` reproduces `ℱ` up to isomorphism. -/
noncomputable def gradedModuleOfSheaf_tildeProj_iso
    {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (ℱ : (Proj 𝒜).Modules)
    (hqc : IsQuasicoherentSheaf ℱ) :
    tildeProj 𝒜 (gradedModuleOfSheaf 𝒜 ℱ) ≅ ℱ := sorry

/-- Proposition 20 (Lec 14): every quasi-coherent sheaf on `Proj 𝒜` is of the form
`M̃` for some graded module `M`; equivalently, `tildeProj` is essentially surjective on
quasi-coherent sheaves. -/
theorem tildeProj_essentiallySurjective
    (ℱ : (Proj 𝒜).Modules)
    (hqc : IsQuasicoherentSheaf ℱ) :
    ∃ (M : GrMod 𝒜), Nonempty (tildeProj 𝒜 M ≅ ℱ) := by
  exact ⟨gradedModuleOfSheaf 𝒜 ℱ, ⟨gradedModuleOfSheaf_tildeProj_iso 𝒜 ℱ hqc⟩⟩

/-- Refinement for coherent sheaves: every coherent sheaf on `Proj 𝒜` is `M̃` for some
finitely generated graded module `M`. -/
theorem tildeProj_essentiallySurjective_fg
    (ℱ : (Proj 𝒜).Modules)
    (hcoh : IsCoherentSheaf ℱ) :
    ∃ (M : GrMod 𝒜), M.IsFinitelyGenerated ∧ Nonempty (tildeProj 𝒜 M ≅ ℱ) := by sorry

/-- A surjection of graded modules `M ↠ N` induces an epimorphism `M̃ ↠ Ñ` on `Proj 𝒜`,
obtained from the short exact sequence and right-exactness of `tildeProj`. -/
theorem tildeProj_epi_of_graded_surjection
    (M N : GrMod 𝒜)
    (f : M.carrier →ₗ[A] N.carrier)
    (hf : Function.Surjective f) :
    ∃ (φ : tildeProj 𝒜 M ⟶ tildeProj 𝒜 N), Epi φ := by

  have ses := GrMod.shortExactOfSurjection M N f hf

  obtain ⟨w, hse⟩ := tildeProj_exact 𝒜 _ M N ses

  exact ⟨tildeProj_map 𝒜 ⟨ses.g⟩, hse.epi_g⟩

/-- Every finitely generated graded module `M` is a quotient of a finite direct sum
of shifted copies of `𝒜`, i.e. of `𝒜(-d)^k` for some `d, k`. -/
theorem fg_graded_module_quotient_of_shifted_free
    (M : GrMod 𝒜)
    (hfg : M.IsFinitelyGenerated) :
    ∃ (d : ℕ) (k : ℕ)
      (f : ((GrMod.shift 𝒜 (-↑d)).directSumCopies k).carrier →ₗ[A] M.carrier),
      Function.Surjective f := by sorry

/-- Corollary 18 (Lec 14) on `Proj`: every coherent sheaf is a quotient of a direct
sum of twists of the structure sheaf, i.e. of `O(-d)^k = (𝒜(-d)^k)~`. -/
theorem coherent_sheaf_quotient_of_twisted_structure_sheaf
    (ℱ : (Proj 𝒜).Modules)
    (hcoh : IsCoherentSheaf ℱ) :
    ∃ (d : ℕ) (k : ℕ),

      ∃ (φ : tildeProj 𝒜 ((GrMod.shift 𝒜 (-↑d)).directSumCopies k) ⟶ ℱ),
        Epi φ := by

  obtain ⟨M, hfg, ⟨iso⟩⟩ := tildeProj_essentiallySurjective_fg 𝒜 ℱ hcoh

  obtain ⟨d, k, f, hf⟩ := fg_graded_module_quotient_of_shifted_free 𝒜 M hfg

  obtain ⟨ψ, hψ⟩ := tildeProj_epi_of_graded_surjection 𝒜 _ M f hf

  exact ⟨d, k, ψ ≫ iso.hom, epi_comp ψ iso.hom⟩

/-- Serre quotient of the category of graded modules by the Serre subcategory of
locally nilpotent graded modules; used to formulate Serre's theorem. -/
noncomputable def SerreQuotGrModLocNilp
    (A : Type u) [CommRing A] (σ : Type u) [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] : Type (u + 1) := by sorry

/-- Category instance on the Serre quotient `GrMod / LocallyNilpotent`. -/
noncomputable instance instCategorySerreQuotGrModLocNilp
    {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] :
    Category.{u} (SerreQuotGrModLocNilp A σ 𝒜) := by sorry

attribute [instance] instCategorySerreQuotGrModLocNilp

/-- The canonical quotient functor `GrMod 𝒜 → GrMod 𝒜 / LocallyNilpotent`. -/
noncomputable def SerreQuotGrModLocNilp.quotientFunctor
    {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] :
    GrMod 𝒜 ⥤ SerreQuotGrModLocNilp A σ 𝒜 := by sorry

/-- Serre quotient of finitely generated graded modules by the subcategory of those
which are concentrated in finitely many degrees. -/
noncomputable def SerreQuotGrModFGFinDim
    (A : Type u) [CommRing A] (σ : Type u) [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] : Type (u + 1) := by sorry

/-- Category instance on the FG Serre quotient. -/
noncomputable instance instCategorySerreQuotGrModFGFinDim
    {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] :
    Category.{u} (SerreQuotGrModFGFinDim A σ 𝒜) := by sorry

attribute [instance] instCategorySerreQuotGrModFGFinDim

/-- Quotient functor on FG graded modules into the corresponding Serre quotient. -/
noncomputable def SerreQuotGrModFGFinDim.quotientFunctor
    {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] :
    (show ObjectProperty (GrMod 𝒜) from fun M => M.IsFinitelyGenerated).FullSubcategory ⥤
      SerreQuotGrModFGFinDim A σ 𝒜 := by sorry

/-- The full subcategory of quasi-coherent sheaves of `O_{Proj 𝒜}`-modules. -/
abbrev QCohCat {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] :=
  (show ObjectProperty ((Proj 𝒜).Modules) from fun ℱ => IsQuasicoherentSheaf ℱ).FullSubcategory

/-- The full subcategory of coherent sheaves of `O_{Proj 𝒜}`-modules. -/
abbrev CohCat {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] :=
  (show ObjectProperty ((Proj 𝒜).Modules) from fun ℱ => IsCoherentSheaf ℱ).FullSubcategory

/-- A graded module `M` gives the zero sheaf on `Proj 𝒜` iff `M` is locally nilpotent
for the irrelevant ideal. -/
theorem tildeProj_zero_iff_locallyNilpotent
    {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (M : GrMod 𝒜) :
    IsZero (tildeProj 𝒜 M) ↔ M.IsLocallyNilpotent := by sorry

/-- For finitely generated `M`, `M̃ = 0` on `Proj 𝒜` iff `M` is concentrated in
finitely many degrees. -/
theorem tildeProj_zero_iff_finiteDimensional
    {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (M : GrMod 𝒜) (hfg : M.IsFinitelyGenerated) :
    IsZero (tildeProj 𝒜 M) ↔ M.IsFiniteDimensional := by sorry

/-- Faithfulness modulo the Serre subcategory: a graded-module map whose tilde image
is zero on `Proj 𝒜` has image annihilated by powers of the irrelevant ideal. -/
theorem tildeProj_faithful_on_quotient
    {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {M N : GrMod 𝒜} (f : GrMod.Hom M N)
    (hzero : tildeProj_map 𝒜 f = 0) :
    ∀ (x : M.carrier), ∃ (d : ℕ),
      ∀ (a : A), a ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal →
        a ^ d • (f.toLinearMap x) = 0 := by sorry

/-- Fullness modulo the Serre subcategory: every sheaf morphism `M̃ → Ñ` on `Proj 𝒜`
comes from a graded-module morphism out of a "large enough" submodule `M' ⊆ M` whose
inclusion becomes an isomorphism after `tildeProj`. -/
theorem tildeProj_full_on_quotient
    {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (M N : GrMod 𝒜)
    (φ : tildeProj 𝒜 M ⟶ tildeProj 𝒜 N) :
    ∃ (M' : GrMod 𝒜) (ι : GrMod.Hom M' M) (f : GrMod.Hom M' N),
      Function.Injective ι.toLinearMap ∧
      (∀ (x : M.carrier), ∃ (d : ℕ),
        ∀ (a : A), a ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal →
          a ^ d • x ∈ LinearMap.range ι.toLinearMap) ∧


      tildeProj_map 𝒜 f = tildeProj_map 𝒜 ι ≫ φ := by sorry

/-- Serre's theorem (quasi-coherent version): the Serre quotient of graded modules by
locally nilpotent modules is equivalent to the category of quasi-coherent sheaves on
`Proj 𝒜`. -/
noncomputable def serre_equivalence_qcoh
    {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] :
    SerreQuotGrModLocNilp A σ 𝒜 ≌ QCohCat 𝒜 := by sorry

/-- Serre's theorem (coherent version): the Serre quotient of finitely generated graded
modules by those concentrated in finitely many degrees is equivalent to the category of
coherent sheaves on `Proj 𝒜`. -/
noncomputable def serre_equivalence_coh
    {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] :
    SerreQuotGrModFGFinDim A σ 𝒜 ≌ CohCat 𝒜 := by sorry

/-- Combined Serre–Grothendieck correspondence on `Proj 𝒜`: essential surjectivity of
`tildeProj` on quasi-coherent sheaves, characterization of the zero objects, faithfulness
and fullness up to the Serre subcategory, and the FG/finite-dimensional refinement. -/
theorem serre_grothendieck_correspondence :

    (∀ (ℱ : (Proj 𝒜).Modules), IsQuasicoherentSheaf ℱ →
      ∃ (M : GrMod 𝒜), Nonempty (tildeProj 𝒜 M ≅ ℱ)) ∧

    (∀ (M : GrMod 𝒜),
      IsZero (tildeProj 𝒜 M) ↔ M.IsLocallyNilpotent) ∧

    (∀ (M N : GrMod 𝒜) (f : GrMod.Hom M N),
      tildeProj_map 𝒜 f = 0 →
      ∀ (x : M.carrier), ∃ (d : ℕ),
        ∀ (a : A), a ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal →
          a ^ d • (f.toLinearMap x) = 0) ∧

    (∀ (M N : GrMod 𝒜) (φ : tildeProj 𝒜 M ⟶ tildeProj 𝒜 N),
      ∃ (M' : GrMod 𝒜) (ι : GrMod.Hom M' M) (f : GrMod.Hom M' N),
        Function.Injective ι.toLinearMap ∧
        (∀ (x : M.carrier), ∃ (d : ℕ),
          ∀ (a : A), a ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal →
            a ^ d • x ∈ LinearMap.range ι.toLinearMap) ∧
        tildeProj_map 𝒜 f = tildeProj_map 𝒜 ι ≫ φ) ∧

    (∀ (M : GrMod 𝒜), M.IsFinitelyGenerated →
      (IsZero (tildeProj 𝒜 M) ↔ M.IsFiniteDimensional)) := by
  exact ⟨fun ℱ hqc => tildeProj_essentiallySurjective 𝒜 ℱ hqc,
         tildeProj_zero_iff_locallyNilpotent 𝒜,
         fun M N f hf => tildeProj_faithful_on_quotient 𝒜 f hf,
         tildeProj_full_on_quotient 𝒜,
         tildeProj_zero_iff_finiteDimensional 𝒜⟩

end
