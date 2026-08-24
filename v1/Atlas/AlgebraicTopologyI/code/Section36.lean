/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section34
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Separation.Regular
import Mathlib.Algebra.Group.Subgroup.Ker

open CategoryTheory AlgebraicTopology Limits TopologicalSpace MonoidalCategory

noncomputable section

namespace FullyRelativeCapProduct

variable (R : Type) [CommRing R]

/-- The singular chain complex `S_*(Y; R)` of a topological space `Y` with
coefficients in the commutative ring `R`, viewed as a chain complex of
`R`-modules indexed by `ℕ`. -/
abbrev singChainCx (Y : TopCat.{0}) : ChainComplex (ModuleCat.{0} R) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj Y

/-- The continuous inclusion `A ↪ X` of a subset `A ⊆ X` as a morphism in `TopCat`,
given by the subtype valuation map. -/
def subtypeIncl (X : TopCat.{0}) (A : Set X) : TopCat.of A ⟶ X :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The chain map `S_*(A; R) → S_*(X; R)` induced by the inclusion of a
subspace `A ⊆ X` into `X`. -/
def inclChainMap (X : TopCat.{0}) (A : Set X) :
    singChainCx R (TopCat.of A) ⟶ singChainCx R X :=
  ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
    (subtypeIncl X A)

/-- The relative singular chain complex `S_*(X, A; R)`, defined as the cokernel
of the inclusion-induced chain map `S_*(A; R) → S_*(X; R)`. -/
def relSingChainCx (X : TopCat.{0}) (A : Set X) :
    ChainComplex (ModuleCat.{0} R) ℕ :=
  cokernel (inclChainMap R X A)

/-- The relative singular homology `H_n(X, A; R)`, defined as the `n`-th homology
of the relative singular chain complex. -/
def relSingularHomology (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    ModuleCat.{0} R :=
  (relSingChainCx R X A).homology n

/-- The absolute singular homology `H_n(X; R)`, the `n`-th homology of the
singular chain complex. -/
def absSingularHomology (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} R :=
  (singChainCx R X).homology n

/-- The Čech cohomology `Ȟ^p(K; R)` of a subset `K ⊆ X`, obtained as the direct
limit of the singular cohomologies of open neighbourhoods of `K`. -/
def cechCohomology
    (X : TopCat.{0}) (K : Set X) (p : ℕ) : ModuleCat.{0} R :=
  CechCohomology.cechCohomology R K p

/-- A pair `(U, V)` of open neighbourhoods with `K ⊆ U`, `L ⊆ V` and `V ⊆ U`,
indexing the directed system used to define relative Čech cohomology
`Ȟ^p(K, L; R)`. -/
structure OpenNbhdPair {X : Type} [TopologicalSpace X] (K L : Set X) where
  U : TopologicalSpace.Opens X
  V : TopologicalSpace.Opens X
  hK : K ⊆ ↑U
  hL : L ⊆ ↑V
  hVU : V ≤ U

/-- The reverse-inclusion preorder on `OpenNbhdPair K L`: a pair `p` is smaller
than `q` when `q.U ⊆ p.U` and `q.V ⊆ p.V`. This makes the family of pairs into
a directed system as the neighbourhoods shrink down to `(K, L)`. -/
instance openNbhdPair_preorder {X : Type} [TopologicalSpace X] {K L : Set X} :
    Preorder (OpenNbhdPair K L) where
  le p q := q.U ≤ p.U ∧ q.V ≤ p.V
  le_refl p := ⟨le_refl _, le_refl _⟩
  le_trans p q r hpq hqr := ⟨le_trans hqr.1 hpq.1, le_trans hqr.2 hpq.2⟩

/-- The inclusion `V ↪ U` of opens `V ≤ U` as a morphism in `TopCat`. -/
def opensInclusion {X : TopCat.{0}} (U V : TopologicalSpace.Opens X) (h : V ≤ U) :
    TopCat.of ↑V.1 ⟶ TopCat.of ↑U.1 :=
  ⟨fun x => ⟨x.1, h x.2⟩, continuous_inclusion h⟩

/-- The relative singular cohomology `H^p(U, V; R)` of an `OpenNbhdPair (U, V)`,
constructed as the `p`-th cohomology of the kernel of the cochain restriction
`S^*(U; R) → S^*(V; R)`. -/
def relCohomOfPair {X : TopCat.{0}} {K L : Set X}
    (pair : OpenNbhdPair K L) (p : ℕ) : ModuleCat.{0} R := by
  classical
  let G := ModuleCat.of R R
  let restrictMap :=
    (HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map
      (((((linearYoneda R (ModuleCat.{0} R)).obj G).rightOp.mapHomologicalComplex
        (ComplexShape.down ℕ)).map
        (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj G).map
          (opensInclusion pair.U pair.V pair.hVU))).op)
  exact (kernel restrictMap).homology p

/-- The underlying type of `relCohomOfPair`, exposed as a `Type` to serve as
the type-theoretic family for the direct-limit construction of relative
Čech cohomology. -/
def relCechFamily {X : TopCat.{0}} {K L : Set X}
    (p : ℕ) (pair : OpenNbhdPair K L) : Type :=
  (relCohomOfPair R pair p : Type _)

/-- Transport the additive commutative group structure from `relCohomOfPair`
to its underlying type `relCechFamily`. -/
instance relCechFamily_addCommGroup {X : TopCat.{0}} {K L : Set X}
    (p : ℕ) (pair : OpenNbhdPair K L) :
    AddCommGroup (relCechFamily R p pair) :=
  (relCohomOfPair R pair p).isAddCommGroup

/-- Transport the `R`-module structure from `relCohomOfPair` to its underlying
type `relCechFamily`. -/
instance relCechFamily_module {X : TopCat.{0}} {K L : Set X}
    (p : ℕ) (pair : OpenNbhdPair K L) :
    Module R (relCechFamily R p pair) :=
  (relCohomOfPair R pair p).isModule

/-- The transition map `relCohomOfPair pair₁ p → relCohomOfPair pair₂ p` in the
directed system of open neighbourhood pairs, induced by restriction of cochains
along the inclusions `pair₂.U ⊆ pair₁.U` and `pair₂.V ⊆ pair₁.V`. -/
def relCechTransition {X : TopCat.{0}} {K L : Set X}
    (p : ℕ) (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    relCechFamily R p pair₁ →ₗ[R] relCechFamily R p pair₂ := by
  classical

  let G := ModuleCat.of R R
  let F := (singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj G
  let L' := ((linearYoneda R (ModuleCat.{0} R)).obj G).rightOp.mapHomologicalComplex
    (ComplexShape.down ℕ)
  let U := HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)


  let restrictMap₁ := U.map ((L'.map (F.map (opensInclusion pair₁.U pair₁.V pair₁.hVU))).op)
  let restrictMap₂ := U.map ((L'.map (F.map (opensInclusion pair₂.U pair₂.V pair₂.hVU))).op)

  let pU := U.map ((L'.map (F.map (opensInclusion pair₁.U pair₂.U h.1))).op)
  let qV := U.map ((L'.map (F.map (opensInclusion pair₁.V pair₂.V h.2))).op)

  have comm : restrictMap₁ ≫ qV = pU ≫ restrictMap₂ := by
    simp only [restrictMap₁, restrictMap₂, pU, qV]
    simp only [← U.map_comp, ← op_comp, ← L'.map_comp, ← F.map_comp]


    have : opensInclusion pair₁.V pair₂.V h.2 ≫ opensInclusion pair₁.U pair₁.V pair₁.hVU =
        opensInclusion pair₂.U pair₂.V pair₂.hVU ≫ opensInclusion pair₁.U pair₂.U h.1 := by
      ext ⟨x, hx⟩; rfl
    rw [this]

  exact (HomologicalComplex.homologyMap
    (kernel.map restrictMap₁ restrictMap₂ pU qV comm) p).hom


/-- The relative Čech cohomology `Ȟ^p(K, L; R)`, defined as the direct limit
of the relative singular cohomologies `H^p(U, V; R)` over the cofinal system
of `OpenNbhdPair`s shrinking down to `(K, L)`. -/
def cechCohomologyRel
    (X : TopCat.{0}) (K L : Set X) (p : ℕ) : ModuleCat.{0} R := by
  classical
  exact ModuleCat.of R (Module.DirectLimit
    (relCechFamily (R := R) (X := X) (K := K) (L := L) p)
    (fun pair₁ pair₂ h => relCechTransition R p pair₁ pair₂ h))

/-- The subset `(X - K) ∩ (X - L) ⊆ X - L`, encoded as the preimage of `Kᶜ`
inside the subspace `Lᶜ`. -/
def complementInComplement (X : TopCat.{0}) (K L : Set X) :
    Set (TopCat.of (Lᶜ : Set X)) :=
  Subtype.val ⁻¹' (Kᶜ : Set X)

/-- Extract the open neighbourhood of `K` from an `OpenNbhdPair K L`. -/
def pairToNbhdK {X : Type} [TopologicalSpace X] {K L : Set X}
    (pair : OpenNbhdPair K L) : CechCohomology.OpenNeighborhoods K :=
  ⟨pair.U, pair.hK⟩

/-- Extract the open neighbourhood of `L` from an `OpenNbhdPair K L`. -/
def pairToNbhdL {X : Type} [TopologicalSpace X] {K L : Set X}
    (pair : OpenNbhdPair K L) : CechCohomology.OpenNeighborhoods L :=
  ⟨pair.V, pair.hL⟩


/-- For a single neighbourhood pair, the map from the relative cohomology
`H^p(U, V; R)` to absolute Čech cohomology `Ȟ^p(K; R)`, obtained by forgetting
the relativity (via the kernel inclusion) and then injecting into the
direct limit. -/
def nbhdRestrictToLimit {X : TopCat.{0}} {K L : Set X}
    (p : ℕ) (pair : OpenNbhdPair K L) :
    relCechFamily R p pair →ₗ[R]
      (CechCohomology.cechCohomology R K p : Type _) := by
  classical
  let G := ModuleCat.of R R

  let rMap := SingularCohomology.restrictionCochainMap R G
    (opensInclusion pair.U pair.V pair.hVU)


  let forgetful : relCechFamily R p pair →ₗ[R]
      CechCohomology.cechFamily R K p (pairToNbhdK pair) :=
    (HomologicalComplex.homologyMap (kernel.ι rMap) p).hom

  let intoLimit := Module.DirectLimit.of R _
    (CechCohomology.cechFamily R K p)
    (fun U V h => CechCohomology.cechTransition R K p U V h)
    (pairToNbhdK pair)
  exact intoLimit.comp forgetful


/-- Compatibility of `nbhdRestrictToLimit` with the transition maps of the
neighbourhood-pair directed system; required for assembling the maps into a
well-defined map on the direct limit. -/
theorem nbhdRestrictToLimit_compat {X : TopCat.{0}} {K L : Set X}
    (p : ℕ) (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂)
    (x : relCechFamily R p pair₁) :
    nbhdRestrictToLimit R p pair₂ (relCechTransition R p pair₁ pair₂ h x) =
    nbhdRestrictToLimit R p pair₁ x := by sorry

/-- The restriction map `Ȟ^p(K, L; R) → Ȟ^p(K; R)` from relative to absolute
Čech cohomology, obtained from the direct-limit description by forgetting
the relativity. -/
def cechCohomRestrict
    (X : TopCat.{0}) (K L : Set X) (p : ℕ) :
    cechCohomologyRel R X K L p ⟶ cechCohomology R X K p := by
  classical
  exact ModuleCat.ofHom (Module.DirectLimit.lift R _
    (relCechFamily (R := R) (X := X) (K := K) (L := L) p)
    (fun pair₁ pair₂ h => relCechTransition R p pair₁ pair₂ h)
    (fun pair => nbhdRestrictToLimit R p pair)
    (fun pair₁ pair₂ h x => nbhdRestrictToLimit_compat R p pair₁ pair₂ h x))


/-- For an open neighbourhood `U` of `K`, the map from the cohomology of `U` to
the Čech cohomology of `L`, defined to be the natural injection into the direct
limit when `L ⊆ K` (so `U` is also a neighbourhood of `L`), and zero otherwise. -/
def nbhdToSubspaceViaLimit {X : TopCat.{0}} {K : Set X} (L : Set X)
    (p : ℕ) (U : CechCohomology.OpenNeighborhoods K) :
    CechCohomology.cechFamily R K p U →ₗ[R]
      (CechCohomology.cechCohomology R L p : Type _) := by
  classical
  by_cases hLK : L ⊆ K
  · have hLU : L ⊆ ↑U.1 := fun x hx => U.2 (hLK hx)
    exact Module.DirectLimit.of R _
      (CechCohomology.cechFamily R L p)
      (fun V₁ V₂ h => CechCohomology.cechTransition R L p V₁ V₂ h)
      ⟨U.1, hLU⟩
  · exact 0


/-- Compatibility of `nbhdToSubspaceViaLimit` with the Čech transition maps,
required to define a map on the direct limit `Ȟ^p(K; R) → Ȟ^p(L; R)`. -/
theorem nbhdToSubspaceViaLimit_compat {X : TopCat.{0}} {K : Set X} (L : Set X)
    (p : ℕ) (U₁ U₂ : CechCohomology.OpenNeighborhoods K) (h : U₁ ≤ U₂)
    (x : CechCohomology.cechFamily R K p U₁) :
    nbhdToSubspaceViaLimit R L p U₂
      (CechCohomology.cechTransition R K p U₁ U₂ h x) =
    nbhdToSubspaceViaLimit R L p U₁ x := by sorry

/-- Restriction in Čech cohomology along a subspace inclusion `L ⊆ K`, giving
the map `Ȟ^p(K; R) → Ȟ^p(L; R)` (taken to be zero if `L ⊄ K`). -/
def cechCohomToSubspace
    (X : TopCat.{0}) (K L : Set X) (p : ℕ) :
    cechCohomology R X K p ⟶ cechCohomology R X L p := by
  classical
  exact ModuleCat.ofHom (Module.DirectLimit.lift R _
    (CechCohomology.cechFamily R K p)
    (fun U V h => CechCohomology.cechTransition R K p U V h)
    (fun U => nbhdToSubspaceViaLimit R L p U)
    (fun U₁ U₂ h x => nbhdToSubspaceViaLimit_compat R L p U₁ U₂ h x))


/-- For an open neighbourhood `V` of `L`, the connecting map from the
cohomology of `V` to the relative Čech cohomology `Ȟ^{p+1}(K, L; R)`, used
to assemble the boundary `Ȟ^p(L; R) → Ȟ^{p+1}(K, L; R)` of the long exact
sequence of the pair `(K, L)`. -/
noncomputable def nbhdCoboundaryToLimit {X : TopCat.{0}} (K : Set X) {L : Set X}
    (p : ℕ) (V : CechCohomology.OpenNeighborhoods L) :
    CechCohomology.cechFamily R L p V →ₗ[R]
      (cechCohomologyRel R X K L (p + 1) : Type _) := by sorry


/-- Compatibility of `nbhdCoboundaryToLimit` with the Čech transition maps,
required to assemble the coboundary `Ȟ^p(L; R) → Ȟ^{p+1}(K, L; R)`. -/
theorem nbhdCoboundaryToLimit_compat {X : TopCat.{0}} (K : Set X) {L : Set X}
    (p : ℕ) (V₁ V₂ : CechCohomology.OpenNeighborhoods L) (h : V₁ ≤ V₂)
    (x : CechCohomology.cechFamily R L p V₁) :
    nbhdCoboundaryToLimit R K p V₂
      (CechCohomology.cechTransition R L p V₁ V₂ h x) =
    nbhdCoboundaryToLimit R K p V₁ x := by sorry

/-- The coboundary `δ : Ȟ^p(L; R) → Ȟ^{p+1}(K, L; R)` in the long exact
sequence of the Čech pair `(K, L)`. -/
def cechCohomCoboundary
    (X : TopCat.{0}) (K L : Set X) (p : ℕ) :
    cechCohomology R X L p ⟶ cechCohomologyRel R X K L (p + 1) := by
  classical
  exact ModuleCat.ofHom (Module.DirectLimit.lift R _
    (CechCohomology.cechFamily R L p)
    (fun V₁ V₂ h => CechCohomology.cechTransition R L p V₁ V₂ h)
    (fun V => nbhdCoboundaryToLimit R K p V)
    (fun V₁ V₂ h x => nbhdCoboundaryToLimit_compat R K p V₁ V₂ h x))


/-- The inclusion `A ↪ B` of one subset into another (with `A ⊆ B`), as a
morphism in `TopCat`. -/
def subsetInclusion (X : TopCat.{0}) (A B : Set X) (h : A ⊆ B) :
    TopCat.of A ⟶ TopCat.of B :=
  ⟨Set.inclusion h, continuous_inclusion h⟩

/-- The inclusion `A ↪ X` factors through `A ↪ B ↪ X` whenever `A ⊆ B`. -/
lemma subtypeIncl_factor (X : TopCat.{0}) (A B : Set X) (h : A ⊆ B) :
    subtypeIncl X A = subsetInclusion X A B h ≫ subtypeIncl X B := by
  apply ConcreteCategory.hom_ext
  intro ⟨x, hx⟩
  rfl

/-- The natural map `(X - L) ∩ (X - K) ↪ X - K` viewed as a morphism in
`TopCat`. -/
def complToComplement (X : TopCat.{0}) (K L : Set X) :
    TopCat.of (complementInComplement X K L) ⟶ TopCat.of (Kᶜ : Set X) :=
  ⟨fun ⟨⟨x, _⟩, hxK⟩ => ⟨x, hxK⟩, by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val⟩

/-- Commutativity of the square of inclusions
`(Lᶜ ∩ Kᶜ) ↪ Lᶜ ↪ X` and `(Lᶜ ∩ Kᶜ) ↪ Kᶜ ↪ X` in `TopCat`. -/
lemma tripleIncl_comm_topcat (X : TopCat.{0}) (K L : Set X) :
    subtypeIncl (TopCat.of (Lᶜ : Set X)) (complementInComplement X K L) ≫
      subtypeIncl X Lᶜ =
    complToComplement X K L ≫ subtypeIncl X Kᶜ := by
  apply ConcreteCategory.hom_ext
  intro ⟨⟨x, _⟩, _⟩
  rfl

/-- The chain-level version of `tripleIncl_comm_topcat`: the corresponding
square of chain maps between singular chain complexes commutes. -/
lemma tripleIncl_comm_chain (X : TopCat.{0}) (K L : Set X) :
    inclChainMap R (TopCat.of (Lᶜ : Set X)) (complementInComplement X K L) ≫
      ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (subtypeIncl X Lᶜ) =
    ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (complToComplement X K L) ≫
      inclChainMap R X Kᶜ := by
  simp only [inclChainMap, ← Functor.map_comp, tripleIncl_comm_topcat X K L]

/-- The induced chain map on relative singular chain complexes,
`S_*(Lᶜ, Lᶜ ∩ Kᶜ; R) → S_*(X, Kᶜ; R)`, coming from the inclusions of the
triple `(Lᶜ ∩ Kᶜ) ⊆ Lᶜ ⊆ X` and `(Lᶜ ∩ Kᶜ) ⊆ Kᶜ ⊆ X`. -/
def tripleInclChainMap (X : TopCat.{0}) (K L : Set X) :
    relSingChainCx R (TopCat.of (Lᶜ : Set X)) (complementInComplement X K L) ⟶
    relSingChainCx R X Kᶜ :=
  cokernel.map _ _
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (complToComplement X K L))
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (subtypeIncl X Lᶜ))
    (tripleIncl_comm_chain R X K L)

/-- The induced map on relative homology,
`H_q(Lᶜ, Lᶜ ∩ Kᶜ; R) → H_q(X, Kᶜ; R)`, coming from the inclusion of pairs
`(Lᶜ, Lᶜ ∩ Kᶜ) → (X, Kᶜ)`. -/
def homolTripleInclusion
    (X : TopCat.{0}) (K L : Set X) (q : ℕ) :
    relSingularHomology R (TopCat.of (Lᶜ : Set X))
      (complementInComplement X K L) q ⟶
      relSingularHomology R X Kᶜ q :=
  HomologicalComplex.homologyMap (tripleInclChainMap R X K L) q

/-- Compatibility square needed to define the restriction chain map
`S_*(X, Kᶜ; R) → S_*(X, Lᶜ; R)` when `Kᶜ ⊆ Lᶜ`. -/
lemma restriction_comm_chain (X : TopCat.{0}) (K L : Set X) (h : (Kᶜ : Set X) ⊆ Lᶜ) :
    inclChainMap R X Kᶜ ≫ 𝟙 _ =
      ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (subsetInclusion X Kᶜ Lᶜ h) ≫ inclChainMap R X Lᶜ := by
  simp only [Category.comp_id, inclChainMap, ← Functor.map_comp,
    subtypeIncl_factor X Kᶜ Lᶜ h]

/-- The chain map between relative singular chain complexes
`S_*(X, Kᶜ; R) → S_*(X, Lᶜ; R)`, induced by enlarging the relative subspace
from `Kᶜ` to `Lᶜ` (assuming `Kᶜ ⊆ Lᶜ`, i.e. `L ⊆ K`). -/
def restrictionChainMap (X : TopCat.{0}) (K L : Set X) (h : (Kᶜ : Set X) ⊆ Lᶜ) :
    relSingChainCx R X Kᶜ ⟶ relSingChainCx R X Lᶜ :=
  cokernel.map _ _
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (subsetInclusion X Kᶜ Lᶜ h))
    (𝟙 _)
    (restriction_comm_chain R X K L h)

/-- The restriction map `H_q(X, Kᶜ; R) → H_q(X, Lᶜ; R)` induced by enlarging
the relative subspace from `Kᶜ` to `Lᶜ` (defined to be zero if `Kᶜ ⊄ Lᶜ`). -/
def homolRestriction
    (X : TopCat.{0}) (K L : Set X) (q : ℕ) :
    relSingularHomology R X Kᶜ q ⟶ relSingularHomology R X Lᶜ q := by
  classical
  exact if h : (Kᶜ : Set X) ⊆ Lᶜ
    then HomologicalComplex.homologyMap (restrictionChainMap R X K L h) q
    else 0

/-- The composition `tripleInclChainMap ≫ restrictionChainMap` vanishes,
expressing the chain-level exactness needed to obtain the short exact
sequence of relative chain complexes for the triple `(X, Lᶜ, Kᶜ)`. -/
lemma tripleInclChainMap_comp_restrictionChainMap_eq_zero
    (X : TopCat.{0}) (K L : Set X) (h : (Kᶜ : Set X) ⊆ Lᶜ) :
    tripleInclChainMap R X K L ≫ restrictionChainMap R X K L h = 0 := by
  simp only [tripleInclChainMap, restrictionChainMap, relSingChainCx]

  apply coequalizer.hom_ext
  simp only [cokernel.π_desc_assoc, comp_zero, Category.assoc]


  rw [cokernel.π_desc]
  simp only [Category.id_comp]


  show inclChainMap R X Lᶜ ≫ cokernel.π (inclChainMap R X Lᶜ) = 0
  exact cokernel.condition _

/-- The short complex of relative singular chain complexes for the triple
`(X, Lᶜ, Kᶜ)`, namely
`S_*(Lᶜ, Lᶜ ∩ Kᶜ; R) → S_*(X, Kᶜ; R) → S_*(X, Lᶜ; R)`. -/
def tripleShortComplex (X : TopCat.{0}) (K L : Set X) (h : (Kᶜ : Set X) ⊆ Lᶜ) :
    ShortComplex (ChainComplex (ModuleCat.{0} R) ℕ) :=
  ShortComplex.mk
    (tripleInclChainMap R X K L)
    (restrictionChainMap R X K L h)
    (tripleInclChainMap_comp_restrictionChainMap_eq_zero R X K L h)

/-- The short complex `tripleShortComplex` is short exact; this is the
chain-level input for the long exact sequence of the triple. -/
theorem tripleShortComplex_shortExact
    (X : TopCat.{0}) (K L : Set X) (h : (Kᶜ : Set X) ⊆ Lᶜ) :
    (tripleShortComplex R X K L h).ShortExact := by sorry


/-- The boundary map `H_{q+1}(X, Lᶜ; R) → H_q(Lᶜ, Lᶜ ∩ Kᶜ; R)` in the long
exact sequence of the triple `(X, Lᶜ, Kᶜ)`, obtained via the connecting
homomorphism of `tripleShortComplex_shortExact`. -/
def homolTripleBoundary
    (X : TopCat.{0}) (K L : Set X) (q : ℕ) :
    relSingularHomology R X Lᶜ (q + 1) ⟶
      relSingularHomology R (TopCat.of (Lᶜ : Set X))
        (complementInComplement X K L) q := by
  classical
  by_cases h : (Kᶜ : Set X) ⊆ Lᶜ
  · exact (tripleShortComplex_shortExact R X K L h).δ (q + 1) q rfl
  · exact 0

/-- The first component `τ₁` of the Alexander–Whitney cap product short-complex
map at a neighbourhood pair, acting on the `(p+q-1)`-degree slot of the
relative chain complex. -/
noncomputable def awCapShortComplexMap_τ₁
    (R : Type) [CommRing R] {X : TopCat.{0}} {K L : Set X}
    (pair : OpenNbhdPair K L) (p q : ℕ) (β : relCechFamily R p pair) :
    ((relSingChainCx R (TopCat.of ↑pair.U.1) (Subtype.val ⁻¹' Kᶜ)).sc (p + q)).X₁ ⟶
    ((relSingChainCx R (TopCat.of ↑(pair.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ)).sc q).X₁ := by sorry
/-- The middle component `τ₂` of the Alexander–Whitney cap product
short-complex map, acting on the `(p+q)`-degree slot of the relative chain
complex. -/
noncomputable def awCapShortComplexMap_τ₂
    (R : Type) [CommRing R] {X : TopCat.{0}} {K L : Set X}
    (pair : OpenNbhdPair K L) (p q : ℕ) (β : relCechFamily R p pair) :
    ((relSingChainCx R (TopCat.of ↑pair.U.1) (Subtype.val ⁻¹' Kᶜ)).sc (p + q)).X₂ ⟶
    ((relSingChainCx R (TopCat.of ↑(pair.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ)).sc q).X₂ := by sorry
/-- The third component `τ₃` of the Alexander–Whitney cap product
short-complex map, acting on the `(p+q+1)`-degree slot of the relative chain
complex. -/
noncomputable def awCapShortComplexMap_τ₃
    (R : Type) [CommRing R] {X : TopCat.{0}} {K L : Set X}
    (pair : OpenNbhdPair K L) (p q : ℕ) (β : relCechFamily R p pair) :
    ((relSingChainCx R (TopCat.of ↑pair.U.1) (Subtype.val ⁻¹' Kᶜ)).sc (p + q)).X₃ ⟶
    ((relSingChainCx R (TopCat.of ↑(pair.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ)).sc q).X₃ := by sorry
/-- First commutativity condition (between `τ₁` and `τ₂`) ensuring that the
Alexander–Whitney cap product respects the differentials of the short complex
of relative chains. -/
theorem awCapShortComplexMap_comm12
    (R : Type) [CommRing R] {X : TopCat.{0}} {K L : Set X}
    (pair : OpenNbhdPair K L) (p q : ℕ) (β : relCechFamily R p pair) :
    awCapShortComplexMap_τ₁ R pair p q β ≫
      ((relSingChainCx R (TopCat.of ↑(pair.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ)).sc q).f =
    ((relSingChainCx R (TopCat.of ↑pair.U.1) (Subtype.val ⁻¹' Kᶜ)).sc (p + q)).f ≫
      awCapShortComplexMap_τ₂ R pair p q β := by sorry
/-- Second commutativity condition (between `τ₂` and `τ₃`) ensuring that the
Alexander–Whitney cap product respects the differentials of the short complex
of relative chains. -/
theorem awCapShortComplexMap_comm23
    (R : Type) [CommRing R] {X : TopCat.{0}} {K L : Set X}
    (pair : OpenNbhdPair K L) (p q : ℕ) (β : relCechFamily R p pair) :
    awCapShortComplexMap_τ₂ R pair p q β ≫
      ((relSingChainCx R (TopCat.of ↑(pair.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ)).sc q).g =
    ((relSingChainCx R (TopCat.of ↑pair.U.1) (Subtype.val ⁻¹' Kᶜ)).sc (p + q)).g ≫
      awCapShortComplexMap_τ₃ R pair p q β := by sorry

/-- The Alexander–Whitney cap product, assembled into a morphism of
short complexes of relative chain complexes, at a neighbourhood pair. The
short complex at degree `n` is the slice of `S_*(U, U ∩ Kᶜ)` around `n`,
and the target is the analogous slice for `(U \ L, U \ L ∩ Kᶜ)` around `q`. -/
def awCapShortComplexMap
    (R : Type) [CommRing R]
    {X : TopCat.{0}} {K L : Set X}
    (pair : OpenNbhdPair K L) (p q : ℕ)
    (β : relCechFamily R p pair) :
    (relSingChainCx R (TopCat.of ↑pair.U.1) (Subtype.val ⁻¹' Kᶜ)).sc (p + q) ⟶
    (relSingChainCx R (TopCat.of ↑(pair.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ)).sc q :=
  ⟨awCapShortComplexMap_τ₁ R pair p q β,
   awCapShortComplexMap_τ₂ R pair p q β,
   awCapShortComplexMap_τ₃ R pair p q β,
   awCapShortComplexMap_comm12 R pair p q β,
   awCapShortComplexMap_comm23 R pair p q β⟩

/-- Projection lemma: the `τ₁` component of `awCapShortComplexMap` is, by
construction, `awCapShortComplexMap_τ₁`. -/
lemma awCapShortComplexMap_τ₁_eq
    (R : Type) [CommRing R] {X : TopCat.{0}} {K L : Set X}
    (pair : OpenNbhdPair K L) (p q : ℕ) (β : relCechFamily R p pair) :
    (awCapShortComplexMap R pair p q β).τ₁ = awCapShortComplexMap_τ₁ R pair p q β := rfl

/-- Projection lemma: the `τ₂` component of `awCapShortComplexMap` is, by
construction, `awCapShortComplexMap_τ₂`. -/
lemma awCapShortComplexMap_τ₂_eq
    (R : Type) [CommRing R] {X : TopCat.{0}} {K L : Set X}
    (pair : OpenNbhdPair K L) (p q : ℕ) (β : relCechFamily R p pair) :
    (awCapShortComplexMap R pair p q β).τ₂ = awCapShortComplexMap_τ₂ R pair p q β := rfl

/-- Projection lemma: the `τ₃` component of `awCapShortComplexMap` is, by
construction, `awCapShortComplexMap_τ₃`. -/
lemma awCapShortComplexMap_τ₃_eq
    (R : Type) [CommRing R] {X : TopCat.{0}} {K L : Set X}
    (pair : OpenNbhdPair K L) (p q : ℕ) (β : relCechFamily R p pair) :
    (awCapShortComplexMap R pair p q β).τ₃ = awCapShortComplexMap_τ₃ R pair p q β := rfl


/-- Additivity of the `τ₁` component of the Alexander–Whitney cap product
short-complex map in the cohomology class `β`. -/
theorem awCapShortComplexMap_τ₁_add
    (R : Type) [CommRing R] {X : TopCat.{0}} {K L : Set X}
    (pair : OpenNbhdPair K L) (p q : ℕ) (β₁ β₂ : relCechFamily R p pair) :
    awCapShortComplexMap_τ₁ R pair p q (β₁ + β₂) =
      awCapShortComplexMap_τ₁ R pair p q β₁ + awCapShortComplexMap_τ₁ R pair p q β₂ := by sorry
/-- Additivity of the `τ₂` component of the Alexander–Whitney cap product
short-complex map in the cohomology class `β`. -/
theorem awCapShortComplexMap_τ₂_add
    (R : Type) [CommRing R] {X : TopCat.{0}} {K L : Set X}
    (pair : OpenNbhdPair K L) (p q : ℕ) (β₁ β₂ : relCechFamily R p pair) :
    awCapShortComplexMap_τ₂ R pair p q (β₁ + β₂) =
      awCapShortComplexMap_τ₂ R pair p q β₁ + awCapShortComplexMap_τ₂ R pair p q β₂ := by sorry
/-- Additivity of the `τ₃` component of the Alexander–Whitney cap product
short-complex map in the cohomology class `β`. -/
theorem awCapShortComplexMap_τ₃_add
    (R : Type) [CommRing R] {X : TopCat.{0}} {K L : Set X}
    (pair : OpenNbhdPair K L) (p q : ℕ) (β₁ β₂ : relCechFamily R p pair) :
    awCapShortComplexMap_τ₃ R pair p q (β₁ + β₂) =
      awCapShortComplexMap_τ₃ R pair p q β₁ + awCapShortComplexMap_τ₃ R pair p q β₂ := by sorry
/-- `R`-linearity in the cohomology class `β` of the `τ₁` component of the
Alexander–Whitney cap product short-complex map. -/
theorem awCapShortComplexMap_τ₁_smul
    (R : Type) [CommRing R] {X : TopCat.{0}} {K L : Set X}
    (pair : OpenNbhdPair K L) (p q : ℕ) (r : R) (β : relCechFamily R p pair) :
    awCapShortComplexMap_τ₁ R pair p q (r • β) =
      r • awCapShortComplexMap_τ₁ R pair p q β := by sorry
/-- `R`-linearity in the cohomology class `β` of the `τ₂` component of the
Alexander–Whitney cap product short-complex map. -/
theorem awCapShortComplexMap_τ₂_smul
    (R : Type) [CommRing R] {X : TopCat.{0}} {K L : Set X}
    (pair : OpenNbhdPair K L) (p q : ℕ) (r : R) (β : relCechFamily R p pair) :
    awCapShortComplexMap_τ₂ R pair p q (r • β) =
      r • awCapShortComplexMap_τ₂ R pair p q β := by sorry
/-- `R`-linearity in the cohomology class `β` of the `τ₃` component of the
Alexander–Whitney cap product short-complex map. -/
theorem awCapShortComplexMap_τ₃_smul
    (R : Type) [CommRing R] {X : TopCat.{0}} {K L : Set X}
    (pair : OpenNbhdPair K L) (p q : ℕ) (r : R) (β : relCechFamily R p pair) :
    awCapShortComplexMap_τ₃ R pair p q (r • β) =
      r • awCapShortComplexMap_τ₃ R pair p q β := by sorry

attribute [irreducible] awCapShortComplexMap

/-- The Alexander–Whitney cap product short-complex map is additive in the
cohomology class `β`. -/
theorem awCapShortComplexMap_add
    (R : Type) [CommRing R]
    {X : TopCat.{0}} {K L : Set X}
    (pair : OpenNbhdPair K L) (p q : ℕ)
    (β₁ β₂ : relCechFamily R p pair) :
    awCapShortComplexMap R pair p q (β₁ + β₂) =
      awCapShortComplexMap R pair p q β₁ + awCapShortComplexMap R pair p q β₂ := by
  apply ShortComplex.hom_ext
  · simp only [awCapShortComplexMap_τ₁_eq, ShortComplex.add_τ₁,
      awCapShortComplexMap_τ₁_add]
  · simp only [awCapShortComplexMap_τ₂_eq, ShortComplex.add_τ₂,
      awCapShortComplexMap_τ₂_add]
  · simp only [awCapShortComplexMap_τ₃_eq, ShortComplex.add_τ₃,
      awCapShortComplexMap_τ₃_add]

/-- The Alexander–Whitney cap product short-complex map is `R`-linear in the
cohomology class `β`. -/
theorem awCapShortComplexMap_smul
    (R : Type) [CommRing R]
    {X : TopCat.{0}} {K L : Set X}
    (pair : OpenNbhdPair K L) (p q : ℕ)
    (r : R) (β : relCechFamily R p pair) :
    awCapShortComplexMap R pair p q (r • β) =
      r • awCapShortComplexMap R pair p q β := by
  apply ShortComplex.hom_ext
  · rw [awCapShortComplexMap_τ₁_eq, ShortComplex.smul_τ₁, awCapShortComplexMap_τ₁_eq,
      awCapShortComplexMap_τ₁_smul]; rfl
  · rw [awCapShortComplexMap_τ₂_eq, ShortComplex.smul_τ₂, awCapShortComplexMap_τ₂_eq,
      awCapShortComplexMap_τ₂_smul]; rfl
  · rw [awCapShortComplexMap_τ₃_eq, ShortComplex.smul_τ₃, awCapShortComplexMap_τ₃_eq,
      awCapShortComplexMap_τ₃_smul]; rfl

/-- The map on relative homology obtained by passing the Alexander–Whitney
cap product short-complex map to homology, giving a linear map
`H_{p+q}(U, U ∩ Kᶜ) → H_q(U \ L, (U \ L) ∩ Kᶜ)` depending on a cohomology
class `β` of the neighbourhood pair. -/
def awCapDescendsToHomology
    (R : Type) [CommRing R]
    {X : TopCat.{0}} {K L : Set X}
    (pair : OpenNbhdPair K L) (p q : ℕ)
    (β : relCechFamily R p pair) :
    (relSingularHomology R (TopCat.of ↑pair.U.1)
      (Subtype.val ⁻¹' Kᶜ) (p + q) : Type _) →ₗ[R]
    (relSingularHomology R (TopCat.of ↑(pair.U.1 \ L))
      (Subtype.val ⁻¹' Kᶜ) q : Type _) :=
  (ShortComplex.homologyMap (awCapShortComplexMap R pair p q β)).hom

/-- Additivity of `awCapDescendsToHomology` in the cohomology class `β`. -/
theorem awCapDescendsToHomology_add
    (R : Type) [CommRing R]
    {X : TopCat.{0}} {K L : Set X}
    (pair : OpenNbhdPair K L) (p q : ℕ)
    (β₁ β₂ : relCechFamily R p pair)
    (c : (relSingularHomology R (TopCat.of ↑pair.U.1)
      (Subtype.val ⁻¹' Kᶜ) (p + q) : Type _)) :
    awCapDescendsToHomology R pair p q (β₁ + β₂) c =
      awCapDescendsToHomology R pair p q β₁ c +
      awCapDescendsToHomology R pair p q β₂ c := by
  show (ShortComplex.homologyMap (awCapShortComplexMap R pair p q (β₁ + β₂))).hom c =
    (ShortComplex.homologyMap (awCapShortComplexMap R pair p q β₁)).hom c +
    (ShortComplex.homologyMap (awCapShortComplexMap R pair p q β₂)).hom c
  rw [awCapShortComplexMap_add, ShortComplex.homologyMap_add]; rfl

/-- `R`-linearity of `awCapDescendsToHomology` in the cohomology class `β`. -/
theorem awCapDescendsToHomology_smul
    (R : Type) [CommRing R]
    {X : TopCat.{0}} {K L : Set X}
    (pair : OpenNbhdPair K L) (p q : ℕ)
    (r : R) (β : relCechFamily R p pair)
    (c : (relSingularHomology R (TopCat.of ↑pair.U.1)
      (Subtype.val ⁻¹' Kᶜ) (p + q) : Type _)) :
    awCapDescendsToHomology R pair p q (r • β) c =
      r • awCapDescendsToHomology R pair p q β c := by
  show (ShortComplex.homologyMap (awCapShortComplexMap R pair p q (r • β))).hom c =
    r • (ShortComplex.homologyMap (awCapShortComplexMap R pair p q β)).hom c
  rw [awCapShortComplexMap_smul, ShortComplex.homologyMap_smul]; rfl

/-- The fully relative cap product at a single neighbourhood pair, packaged as
an `R`-linear map sending a cohomology class `β` in `H^p(U, V; R)` to the
linear map `H_{p+q}(U, U ∩ Kᶜ) → H_q(U \ L, (U \ L) ∩ Kᶜ)` given by
`awCapDescendsToHomology`. -/
def relCapProductOnNbhd
    {X : TopCat.{0}} {K L : Set X}
    (pair : OpenNbhdPair K L) (p q : ℕ) :
    relCechFamily R p pair →ₗ[R]
      ((relSingularHomology R (TopCat.of ↑pair.U.1)
        (Subtype.val ⁻¹' Kᶜ) (p + q) : Type _) →ₗ[R]
        (relSingularHomology R (TopCat.of ↑(pair.U.1 \ L))
          (Subtype.val ⁻¹' Kᶜ) q : Type _)) where
  toFun β := awCapDescendsToHomology R pair p q β
  map_add' β₁ β₂ := LinearMap.ext fun c =>
    awCapDescendsToHomology_add R pair p q β₁ β₂ c
  map_smul' r β := LinearMap.ext fun c =>
    awCapDescendsToHomology_smul R pair p q r β c

/-- The inclusion `U ↪ X` of an open subspace into `X`, in `TopCat`. -/
def excisionOpenIncl (X : TopCat.{0}) (U : TopologicalSpace.Opens X) :
    TopCat.of ↑U.1 ⟶ X :=
  subtypeIncl X U.1

/-- The inclusion `U ∩ Kᶜ ↪ Kᶜ` of subspaces of `X`, used to set up the
excision map for the pair `(X, Kᶜ)` relative to an open neighbourhood of `K`. -/
def excisionSubspaceIncl (X : TopCat.{0}) (K : Set X) (U : TopologicalSpace.Opens X) :
    TopCat.of (Subtype.val ⁻¹' Kᶜ : Set (TopCat.of ↑U.1)) ⟶ TopCat.of (Kᶜ : Set X) :=
  ⟨fun ⟨⟨x, _⟩, hxK⟩ => ⟨x, hxK⟩, by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val⟩

/-- Commutativity of the chain-level square used to build the excision map
of pairs `(U, U ∩ Kᶜ) → (X, Kᶜ)`. -/
lemma excisionPairIncl_comm (X : TopCat.{0}) (K : Set X) (U : TopologicalSpace.Opens X) :
    inclChainMap R (TopCat.of ↑U.1) (Subtype.val ⁻¹' Kᶜ) ≫
      ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (excisionOpenIncl X U) =
    ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (excisionSubspaceIncl X K U) ≫
      inclChainMap R X Kᶜ := by
  simp only [inclChainMap, ← Functor.map_comp]
  congr 1 <;> { apply ConcreteCategory.hom_ext; intro ⟨⟨x, _⟩, hxK⟩; rfl }

/-- The relative chain map `S_*(U, U ∩ Kᶜ; R) → S_*(X, Kᶜ; R)` induced by the
inclusion of pairs `(U, U ∩ Kᶜ) → (X, Kᶜ)`; this is the chain-level excision
map. -/
def excisionPairChainMap (X : TopCat.{0}) (K : Set X) (U : TopologicalSpace.Opens X) :
    relSingChainCx R (TopCat.of ↑U.1) (Subtype.val ⁻¹' Kᶜ) ⟶
    relSingChainCx R X Kᶜ :=
  cokernel.map _ _
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (excisionSubspaceIncl X K U))
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (excisionOpenIncl X U))
    (excisionPairIncl_comm R X K U)

/-- The induced map on relative homology
`H_n(U, U ∩ Kᶜ; R) → H_n(X, Kᶜ; R)` coming from the excision inclusion of
pairs. -/
def excisionForwardHomol (X : TopCat.{0}) (K : Set X)
    (U : TopologicalSpace.Opens X) (n : ℕ) :
    relSingularHomology R (TopCat.of ↑U.1) (Subtype.val ⁻¹' Kᶜ) n ⟶
    relSingularHomology R X Kᶜ n :=
  HomologicalComplex.homologyMap (excisionPairChainMap R X K U) n

/-- Excision at the level of abelian groups: after forgetting the
`R`-module structure, the chain map `excisionPairChainMap` is a quasi-iso at
degree `n`. -/
theorem excisionPairChainMap_quasiIsoAt_forget₂ (X : TopCat.{0}) (K : Set X)
    (U : TopologicalSpace.Opens X) (hK : K ⊆ ↑U) (n : ℕ) :
    QuasiIsoAt (((forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (excisionPairChainMap R X K U)) n := by sorry


/-- Excision in `R`-modules: the chain map `excisionPairChainMap` is a
quasi-iso at degree `n`, obtained from the abelian-group version by transport
along the forgetful functor (which preserves homology). -/
theorem excisionPairChainMap_quasiIsoAt (X : TopCat.{0}) (K : Set X)
    (U : TopologicalSpace.Opens X) (hK : K ⊆ ↑U) (n : ℕ) :
    QuasiIsoAt (excisionPairChainMap R X K U) n := by
  have := (HomologicalComplex.quasiIsoAt_map_iff_of_preservesHomology
    (excisionPairChainMap R X K U)
    (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}) n).mp
  apply this
  exact excisionPairChainMap_quasiIsoAt_forget₂ R X K U hK n


/-- The excision map on homology
`H_n(U, U ∩ Kᶜ; R) → H_n(X, Kᶜ; R)` is an isomorphism when `K ⊆ U`. -/
theorem excisionForwardHomol_isIso (X : TopCat.{0}) (K : Set X)
    (U : TopologicalSpace.Opens X) (hK : K ⊆ ↑U) (n : ℕ) :
    IsIso (excisionForwardHomol R X K U n) := by
  have hqi := excisionPairChainMap_quasiIsoAt R X K U hK n
  rwa [quasiIsoAt_iff_isIso_homologyMap] at hqi

/-- The inverse of the excision isomorphism, providing a linear map
`H_n(X, Kᶜ; R) → H_n(U, U ∩ Kᶜ; R)` that lifts a relative homology class on
`(X, Kᶜ)` to a class supported in the open neighbourhood `U` of `K`. -/
def excisionInverseHomol
    (X : TopCat.{0}) (K : Set X) (U : TopologicalSpace.Opens X)
    (hK : K ⊆ ↑U) (n : ℕ) :
    (relSingularHomology R X Kᶜ n : Type _) →ₗ[R]
      (relSingularHomology R (TopCat.of ↑U.1) (Subtype.val ⁻¹' Kᶜ) n : Type _) := by
  classical
  haveI := excisionForwardHomol_isIso R X K U hK n
  exact (inv (excisionForwardHomol R X K U n)).hom

/-- The inclusion `U \ L ↪ Lᶜ` as a morphism in `TopCat`, used to compare
`(U \ L, (U \ L) ∩ Kᶜ)` with `(Lᶜ, Lᶜ ∩ Kᶜ)`. -/
def localityBigIncl (X : TopCat.{0}) {K : Set X} (L : Set X)
    (pair : OpenNbhdPair K L) :
    TopCat.of ↑(pair.U.1 \ L) ⟶ TopCat.of (Lᶜ : Set X) :=
  ⟨fun ⟨x, hx⟩ => ⟨x, hx.2⟩, by
    apply Continuous.subtype_mk
    exact continuous_subtype_val⟩

/-- The inclusion `(U \ L) ∩ Kᶜ ↪ Lᶜ ∩ Kᶜ`, viewed as a morphism in `TopCat`
between the relativizing subspaces. -/
def localitySubIncl (X : TopCat.{0}) (K L : Set X)
    (pair : OpenNbhdPair K L) :
    TopCat.of (Subtype.val ⁻¹' Kᶜ : Set (TopCat.of ↑(pair.U.1 \ L))) ⟶
    TopCat.of (complementInComplement X K L) :=
  ⟨fun ⟨⟨x, hxUL⟩, hxK⟩ => ⟨⟨x, hxUL.2⟩, hxK⟩, by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val⟩

/-- Commutativity of the square of inclusions relating the pair
`(U \ L, (U \ L) ∩ Kᶜ)` to `(Lᶜ, Lᶜ ∩ Kᶜ)`, in `TopCat`. -/
lemma localityIncl_comm_topcat (X : TopCat.{0}) (K L : Set X)
    (pair : OpenNbhdPair K L) :
    subtypeIncl (TopCat.of ↑(pair.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) ≫
      localityBigIncl X L pair =
    localitySubIncl X K L pair ≫
      subtypeIncl (TopCat.of (Lᶜ : Set X)) (complementInComplement X K L) := by
  apply ConcreteCategory.hom_ext
  intro ⟨⟨x, _⟩, _⟩
  rfl

/-- Chain-level version of `localityIncl_comm_topcat`: the induced square of
chain maps between singular chain complexes commutes. -/
lemma localityIncl_comm_chain (X : TopCat.{0}) (K L : Set X)
    (pair : OpenNbhdPair K L) :
    inclChainMap R (TopCat.of ↑(pair.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) ≫
      ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (localityBigIncl X L pair) =
    ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (localitySubIncl X K L pair) ≫
      inclChainMap R (TopCat.of (Lᶜ : Set X)) (complementInComplement X K L) := by
  simp only [inclChainMap, ← Functor.map_comp, localityIncl_comm_topcat X K L pair]

/-- The induced map of relative singular chain complexes
`S_*(U \ L, (U \ L) ∩ Kᶜ; R) → S_*(Lᶜ, Lᶜ ∩ Kᶜ; R)` coming from the
inclusions of pairs. -/
def localityInclChainMap (X : TopCat.{0}) (K L : Set X)
    (pair : OpenNbhdPair K L) :
    relSingChainCx R (TopCat.of ↑(pair.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) ⟶
    relSingChainCx R (TopCat.of (Lᶜ : Set X)) (complementInComplement X K L) :=
  cokernel.map _ _
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (localitySubIncl X K L pair))
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (localityBigIncl X L pair))
    (localityIncl_comm_chain R X K L pair)

/-- The induced map on relative homology
`H_q(U \ L, (U \ L) ∩ Kᶜ; R) → H_q(Lᶜ, Lᶜ ∩ Kᶜ; R)`, which is the second
ingredient (after excision) of the local construction of the fully relative
cap product. -/
def localityForwardHomol
    (X : TopCat.{0}) (K L : Set X)
    (pair : OpenNbhdPair K L) (q : ℕ) :
    (relSingularHomology R (TopCat.of ↑(pair.U.1 \ L))
      (Subtype.val ⁻¹' Kᶜ) q : Type _) →ₗ[R]
      (relSingularHomology R (TopCat.of (Lᶜ : Set X))
        (complementInComplement X K L) q : Type _) :=
  (HomologicalComplex.homologyMap (localityInclChainMap R X K L pair) q).hom


/-- The fully relative cap product at a single open neighbourhood pair: given
a cohomology class in `H^p(U, V; R)`, it produces an `R`-linear map
`H_n(X, Kᶜ; R) → H_q(Lᶜ, Lᶜ ∩ Kᶜ; R)` by composing inverse excision,
`relCapProductOnNbhd`, and `localityForwardHomol`. -/
def nbhdCapProduct
    (X : TopCat.{0}) (K L : Set X)
    (hLK : L ⊆ K) (hK : IsClosed K) (hL : IsClosed L)
    (n p q : ℕ) (hpq : p + q = n)
    (pair : OpenNbhdPair K L) :
    relCechFamily R p pair →ₗ[R]
      ((relSingularHomology R X Kᶜ n : Type _) →ₗ[R]
        (relSingularHomology R (TopCat.of (Lᶜ : Set X))
          (complementInComplement X K L) q : Type _)) := by
  classical
  subst hpq


  let excInv := excisionInverseHomol R X K pair.U pair.hK (p + q)

  let relCap := relCapProductOnNbhd R pair p q

  let locFwd := localityForwardHomol R X K L pair q

  exact (LinearMap.llcomp R _ _ _ locFwd).comp
    ((LinearMap.lcomp R _ excInv).comp relCap)


/-- The induced map of "relativizing" subspaces between two nested
neighbourhood pairs at the `n`-side: `U₂ ∩ Kᶜ ↪ U₁ ∩ Kᶜ` (recall the pair
preorder is reversed, so `pair₁ ≤ pair₂` means `U₂ ⊆ U₁`). -/
def nbhdSubIncl_n
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    TopCat.of (Subtype.val ⁻¹' Kᶜ : Set (TopCat.of ↑pair₂.U.1)) ⟶
    TopCat.of (Subtype.val ⁻¹' Kᶜ : Set (TopCat.of ↑pair₁.U.1)) :=
  ⟨fun ⟨⟨x, hxU₂⟩, hxK⟩ => ⟨⟨x, h.1 hxU₂⟩, hxK⟩, by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val⟩

/-- Compatibility square in `TopCat` between subspace and open inclusions for
nested neighbourhood pairs, on the `n`-side. -/
lemma nbhdIncl_comm_topcat_n
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    subtypeIncl (TopCat.of ↑pair₂.U.1) (Subtype.val ⁻¹' Kᶜ) ≫
      opensInclusion pair₁.U pair₂.U h.1 =
    nbhdSubIncl_n pair₁ pair₂ h ≫
      subtypeIncl (TopCat.of ↑pair₁.U.1) (Subtype.val ⁻¹' Kᶜ) := by
  apply ConcreteCategory.hom_ext
  intro ⟨⟨x, _⟩, _⟩
  rfl

/-- Chain-level version of `nbhdIncl_comm_topcat_n`: the corresponding square
of chain maps commutes. -/
lemma nbhdIncl_comm_chain_n
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    inclChainMap R (TopCat.of ↑pair₂.U.1) (Subtype.val ⁻¹' Kᶜ) ≫
      ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (opensInclusion pair₁.U pair₂.U h.1) =
    ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (nbhdSubIncl_n pair₁ pair₂ h) ≫
      inclChainMap R (TopCat.of ↑pair₁.U.1) (Subtype.val ⁻¹' Kᶜ) := by
  simp only [inclChainMap, ← Functor.map_comp, nbhdIncl_comm_topcat_n pair₁ pair₂ h]

/-- The chain map between relative chain complexes
`S_*(U₂, U₂ ∩ Kᶜ) → S_*(U₁, U₁ ∩ Kᶜ)` induced by passing to a smaller pair
(on the `n`-side). -/
def nbhdInclChainMap_n
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    relSingChainCx R (TopCat.of ↑pair₂.U.1) (Subtype.val ⁻¹' Kᶜ) ⟶
    relSingChainCx R (TopCat.of ↑pair₁.U.1) (Subtype.val ⁻¹' Kᶜ) :=
  cokernel.map _ _
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (nbhdSubIncl_n pair₁ pair₂ h))
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (opensInclusion pair₁.U pair₂.U h.1))
    (nbhdIncl_comm_chain_n R pair₁ pair₂ h)


/-- The map on relative homology
`H_n(U₂, U₂ ∩ Kᶜ; R) → H_n(U₁, U₁ ∩ Kᶜ; R)` induced by passing to a smaller
pair (on the `n`-side). -/
def nbhdHomologyInclusion_n
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) (n : ℕ) :
    (relSingularHomology R (TopCat.of ↑pair₂.U.1)
      (Subtype.val ⁻¹' Kᶜ) n : Type _) →ₗ[R]
      (relSingularHomology R (TopCat.of ↑pair₁.U.1)
        (Subtype.val ⁻¹' Kᶜ) n : Type _) :=
  (HomologicalComplex.homologyMap (nbhdInclChainMap_n R pair₁ pair₂ h) n).hom

/-- The inclusion `U₂ \ L ↪ U₁ \ L` for two nested neighbourhood pairs,
as a morphism in `TopCat`. -/
def nbhdBigIncl_q
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    TopCat.of ↑(pair₂.U.1 \ L) ⟶ TopCat.of ↑(pair₁.U.1 \ L) :=
  ⟨fun ⟨x, hx⟩ => ⟨x, h.1 hx.1, hx.2⟩, by
    apply Continuous.subtype_mk
    exact continuous_subtype_val⟩

/-- The inclusion `(U₂ \ L) ∩ Kᶜ ↪ (U₁ \ L) ∩ Kᶜ` for two nested neighbourhood
pairs, as a morphism in `TopCat` (on the `q`-side). -/
def nbhdSubIncl_q
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    TopCat.of (Subtype.val ⁻¹' Kᶜ : Set (TopCat.of ↑(pair₂.U.1 \ L))) ⟶
    TopCat.of (Subtype.val ⁻¹' Kᶜ : Set (TopCat.of ↑(pair₁.U.1 \ L))) :=
  ⟨fun ⟨⟨x, hx⟩, hxK⟩ => ⟨⟨x, h.1 hx.1, hx.2⟩, hxK⟩, by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val⟩

/-- Compatibility square in `TopCat` between subspace and big-pair inclusions
for nested neighbourhood pairs, on the `q`-side. -/
lemma nbhdIncl_comm_topcat_q
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    subtypeIncl (TopCat.of ↑(pair₂.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) ≫
      nbhdBigIncl_q pair₁ pair₂ h =
    nbhdSubIncl_q pair₁ pair₂ h ≫
      subtypeIncl (TopCat.of ↑(pair₁.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) := by
  apply ConcreteCategory.hom_ext
  intro ⟨⟨x, _, _⟩, _⟩
  rfl

/-- Chain-level version of `nbhdIncl_comm_topcat_q`: the corresponding square
of chain maps commutes on the `q`-side. -/
lemma nbhdIncl_comm_chain_q
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    inclChainMap R (TopCat.of ↑(pair₂.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) ≫
      ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (nbhdBigIncl_q pair₁ pair₂ h) =
    ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (nbhdSubIncl_q pair₁ pair₂ h) ≫
      inclChainMap R (TopCat.of ↑(pair₁.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) := by
  simp only [inclChainMap, ← Functor.map_comp, nbhdIncl_comm_topcat_q pair₁ pair₂ h]

/-- The chain map between relative chain complexes
`S_*(U₂ \ L, (U₂ \ L) ∩ Kᶜ) → S_*(U₁ \ L, (U₁ \ L) ∩ Kᶜ)` induced by passing
to a smaller pair (on the `q`-side). -/
def nbhdInclChainMap_q
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    relSingChainCx R (TopCat.of ↑(pair₂.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) ⟶
    relSingChainCx R (TopCat.of ↑(pair₁.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) :=
  cokernel.map _ _
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (nbhdSubIncl_q pair₁ pair₂ h))
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (nbhdBigIncl_q pair₁ pair₂ h))
    (nbhdIncl_comm_chain_q R pair₁ pair₂ h)


/-- The map on relative homology
`H_q(U₂ \ L, (U₂ \ L) ∩ Kᶜ; R) → H_q(U₁ \ L, (U₁ \ L) ∩ Kᶜ; R)` induced by
passing to a smaller pair (on the `q`-side). -/
def nbhdHomologyInclusion_q
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) (q : ℕ) :
    (relSingularHomology R (TopCat.of ↑(pair₂.U.1 \ L))
      (Subtype.val ⁻¹' Kᶜ) q : Type _) →ₗ[R]
      (relSingularHomology R (TopCat.of ↑(pair₁.U.1 \ L))
        (Subtype.val ⁻¹' Kᶜ) q : Type _) :=
  (HomologicalComplex.homologyMap (nbhdInclChainMap_q R pair₁ pair₂ h) q).hom

/-- Compatibility of inverse excision with the transition maps between
nested neighbourhood pairs: lifting `y ∈ H_n(X, Kᶜ; R)` to a class in
`pair₁.U` agrees with first lifting to `pair₂.U` and then transporting to
`pair₁.U` via `nbhdHomologyInclusion_n`. -/
theorem excisionInverseHomol_compatible
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) (n : ℕ)
    (y : (relSingularHomology R X Kᶜ n : Type _)) :
    excisionInverseHomol R X K pair₁.U pair₁.hK n y =
    nbhdHomologyInclusion_n R pair₁ pair₂ h n
      (excisionInverseHomol R X K pair₂.U pair₂.hK n y) := by sorry


/-- Naturality of `relCapProductOnNbhd` with respect to refinement of
neighbourhood pairs: capping with the restricted Čech class and then including
on the `q`-side equals first including on the `n`-side and then capping. -/
theorem relCapProductOnNbhd_naturality
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂)
    (p q : ℕ)
    (x : relCechFamily R p pair₁)
    (z : (relSingularHomology R (TopCat.of ↑pair₂.U.1)
      (Subtype.val ⁻¹' Kᶜ) (p + q) : Type _)) :
    nbhdHomologyInclusion_q R pair₁ pair₂ h q
      (relCapProductOnNbhd R pair₂ p q (relCechTransition R p pair₁ pair₂ h x) z) =
    relCapProductOnNbhd R pair₁ p q x
      (nbhdHomologyInclusion_n R pair₁ pair₂ h (p + q) z) := by sorry


/-- Compatibility of `localityForwardHomol` with refinement of neighbourhood
pairs: the value at `pair₂` agrees with the value at `pair₁` after using
the inclusion `nbhdHomologyInclusion_q`. -/
theorem localityForwardHomol_compatible
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) (q : ℕ)
    (w : (relSingularHomology R (TopCat.of ↑(pair₂.U.1 \ L))
      (Subtype.val ⁻¹' Kᶜ) q : Type _)) :
    localityForwardHomol R X K L pair₂ q w =
    localityForwardHomol R X K L pair₁ q
      (nbhdHomologyInclusion_q R pair₁ pair₂ h q w) := by sorry


/-- The full composite naturality of the neighbourhood-pair cap product:
combines `excisionInverseHomol_compatible`, `relCapProductOnNbhd_naturality`,
and `localityForwardHomol_compatible` so that the result at `pair₂` agrees
with the result at `pair₁` for a fixed `y ∈ H_{p+q}(X, Kᶜ; R)`. -/
theorem nbhdCapProduct_composite_naturality
    {X : TopCat.{0}} {K L : Set X}
    (hLK : L ⊆ K) (hK : IsClosed K) (hL : IsClosed L)
    (p q : ℕ)
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂)
    (x : relCechFamily R p pair₁)
    (y : (relSingularHomology R X Kᶜ (p + q) : Type _)) :
    localityForwardHomol R X K L pair₂ q
      (relCapProductOnNbhd R pair₂ p q (relCechTransition R p pair₁ pair₂ h x)
        (excisionInverseHomol R X K pair₂.U pair₂.hK (p + q) y)) =
    localityForwardHomol R X K L pair₁ q
      (relCapProductOnNbhd R pair₁ p q x
        (excisionInverseHomol R X K pair₁.U pair₁.hK (p + q) y)) := by

  rw [localityForwardHomol_compatible R pair₁ pair₂ h q]

  rw [relCapProductOnNbhd_naturality R pair₁ pair₂ h p q x]

  rw [excisionInverseHomol_compatible R pair₁ pair₂ h (p + q) y]

/-- Compatibility of `nbhdCapProduct` with the transition maps of the
neighbourhood-pair directed system, which is what is required to pass the
cap product to a well-defined map on the direct limit
`Ȟ^p(K, L; R)`. -/
theorem nbhdCapProduct_compatible
    (X : TopCat.{0}) (K L : Set X)
    (hLK : L ⊆ K) (hK : IsClosed K) (hL : IsClosed L)
    (n p q : ℕ) (hpq : p + q = n)
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂)
    (x : relCechFamily R p pair₁) :
    nbhdCapProduct R X K L hLK hK hL n p q hpq pair₂
      (relCechTransition R p pair₁ pair₂ h x) =
    nbhdCapProduct R X K L hLK hK hL n p q hpq pair₁ x := by
  subst hpq
  ext y
  simp only [nbhdCapProduct]
  exact nbhdCapProduct_composite_naturality R hLK hK hL p q pair₁ pair₂ h x y


/-- The fully relative cap product
`Ȟ^p(K, L; R) ⊗ H_n(X, Kᶜ; R) → H_q(Lᶜ, Lᶜ ∩ Kᶜ; R)` for `p + q = n`,
obtained by assembling the neighbourhood-pair cap products
`nbhdCapProduct` into a map out of the direct-limit description of
`Ȟ^p(K, L; R)`. This is the existence half of Theorem 36.1. -/
def fullyRelativeCapProduct
    (X : TopCat.{0}) (K L : Set X)
    (hLK : L ⊆ K) (hK : IsClosed K) (hL : IsClosed L)
    (n p q : ℕ) (hpq : p + q = n) :
    (cechCohomologyRel R X K L p ⊗ relSingularHomology R X Kᶜ n ⟶
      relSingularHomology R (TopCat.of (Lᶜ : Set X))
        (complementInComplement X K L) q) := by
  classical
  let capLifted : (cechCohomologyRel R X K L p : Type _) →ₗ[R]
      ((relSingularHomology R X Kᶜ n : Type _) →ₗ[R]
        (relSingularHomology R (TopCat.of (Lᶜ : Set X))
          (complementInComplement X K L) q : Type _)) :=
    Module.DirectLimit.lift R _ (relCechFamily R p)
      (fun pair₁ pair₂ h => relCechTransition R p pair₁ pair₂ h)
      (fun pair => nbhdCapProduct R X K L hLK hK hL n p q hpq pair)
      (fun pair₁ pair₂ h x => nbhdCapProduct_compatible R X K L hLK hK hL n p q hpq
        pair₁ pair₂ h x)
  exact ModuleCat.ofHom (TensorProduct.lift capLifted)

/-- The absolute (single-subspace) version of the Alexander–Whitney cap
product short-complex map: starting from a Čech class `α` for an open
neighbourhood `U` of `K`, it gives a map of short complexes from the slice
of `S_*(U, U ∩ Kᶜ)` at `(p+q)` to the slice at `q`. -/
noncomputable def awAbsCapShortComplexMap
    (R : Type) [CommRing R]
    {X : TopCat.{0}} {K : Set X}
    (U : CechCohomology.OpenNeighborhoods K) (p q : ℕ)
    (α : CechCohomology.cechFamily R K p U) :
    (relSingChainCx R (TopCat.of ↑U.1.1) (Subtype.val ⁻¹' Kᶜ)).sc (p + q) ⟶
    (relSingChainCx R (TopCat.of ↑U.1.1) (Subtype.val ⁻¹' Kᶜ)).sc q := by sorry

/-- Additivity of `awAbsCapShortComplexMap` in the Čech cohomology class `α`. -/
theorem awAbsCapShortComplexMap_add
    (R : Type) [CommRing R]
    {X : TopCat.{0}} {K : Set X}
    (U : CechCohomology.OpenNeighborhoods K) (p q : ℕ)
    (α₁ α₂ : CechCohomology.cechFamily R K p U) :
    awAbsCapShortComplexMap R U p q (α₁ + α₂) =
      awAbsCapShortComplexMap R U p q α₁ + awAbsCapShortComplexMap R U p q α₂ := by sorry

/-- `R`-linearity of `awAbsCapShortComplexMap` in the Čech class `α`. -/
theorem awAbsCapShortComplexMap_smul
    (R : Type) [CommRing R]
    {X : TopCat.{0}} {K : Set X}
    (U : CechCohomology.OpenNeighborhoods K) (p q : ℕ)
    (r : R) (α : CechCohomology.cechFamily R K p U) :
    awAbsCapShortComplexMap R U p q (r • α) =
      r • awAbsCapShortComplexMap R U p q α := by sorry


/-- Passage to homology of `awAbsCapShortComplexMap`: gives the absolute
cap-with-Čech-class map
`H_{p+q}(U, U ∩ Kᶜ) → H_q(U, U ∩ Kᶜ)`. -/
def awCapOnNbhd_descent
    (R : Type) [CommRing R]
    {X : TopCat.{0}} {K : Set X}
    (U : CechCohomology.OpenNeighborhoods K) (p q : ℕ)
    (α : CechCohomology.cechFamily R K p U) :
    (relSingularHomology R (TopCat.of ↑U.1.1)
      (Subtype.val ⁻¹' Kᶜ) (p + q) : Type _) →ₗ[R]
    (relSingularHomology R (TopCat.of ↑U.1.1)
      (Subtype.val ⁻¹' Kᶜ) q : Type _) :=
  (ShortComplex.homologyMap (awAbsCapShortComplexMap R U p q α)).hom

/-- Additivity of `awCapOnNbhd_descent` in the Čech class `α`. -/
theorem awCapOnNbhd_descent_add
    (R : Type) [CommRing R]
    {X : TopCat.{0}} {K : Set X}
    (U : CechCohomology.OpenNeighborhoods K) (p q : ℕ)
    (α₁ α₂ : CechCohomology.cechFamily R K p U)
    (c : (relSingularHomology R (TopCat.of ↑U.1.1)
      (Subtype.val ⁻¹' Kᶜ) (p + q) : Type _)) :
    awCapOnNbhd_descent R U p q (α₁ + α₂) c =
      awCapOnNbhd_descent R U p q α₁ c +
      awCapOnNbhd_descent R U p q α₂ c := by
  show (ShortComplex.homologyMap (awAbsCapShortComplexMap R U p q (α₁ + α₂))).hom c =
    (ShortComplex.homologyMap (awAbsCapShortComplexMap R U p q α₁)).hom c +
    (ShortComplex.homologyMap (awAbsCapShortComplexMap R U p q α₂)).hom c
  rw [awAbsCapShortComplexMap_add, ShortComplex.homologyMap_add]; rfl

/-- `R`-linearity of `awCapOnNbhd_descent` in the Čech class `α`. -/
theorem awCapOnNbhd_descent_smul
    (R : Type) [CommRing R]
    {X : TopCat.{0}} {K : Set X}
    (U : CechCohomology.OpenNeighborhoods K) (p q : ℕ)
    (r : R) (α : CechCohomology.cechFamily R K p U)
    (c : (relSingularHomology R (TopCat.of ↑U.1.1)
      (Subtype.val ⁻¹' Kᶜ) (p + q) : Type _)) :
    awCapOnNbhd_descent R U p q (r • α) c =
      r • awCapOnNbhd_descent R U p q α c := by
  show (ShortComplex.homologyMap (awAbsCapShortComplexMap R U p q (r • α))).hom c =
    r • (ShortComplex.homologyMap (awAbsCapShortComplexMap R U p q α)).hom c
  rw [awAbsCapShortComplexMap_smul, ShortComplex.homologyMap_smul]; rfl

/-- The absolute cap product at a single open neighbourhood, packaged as an
`R`-linear map from `H^p(U, U ∩ Kᶜ; R)` (the Čech family at `U`) into the
space of linear maps `H_{p+q}(U, U ∩ Kᶜ) → H_q(U, U ∩ Kᶜ)`. -/
def absCapOnNbhd
    {X : TopCat.{0}} {K : Set X}
    (U : CechCohomology.OpenNeighborhoods K) (p q : ℕ) :
    CechCohomology.cechFamily R K p U →ₗ[R]
      ((relSingularHomology R (TopCat.of ↑U.1.1)
        (Subtype.val ⁻¹' Kᶜ) (p + q) : Type _) →ₗ[R]
        (relSingularHomology R (TopCat.of ↑U.1.1)
          (Subtype.val ⁻¹' Kᶜ) q : Type _)) where
  toFun α := awCapOnNbhd_descent R U p q α
  map_add' α₁ α₂ := LinearMap.ext fun c =>
    awCapOnNbhd_descent_add R U p q α₁ α₂ c
  map_smul' r α := LinearMap.ext fun c =>
    awCapOnNbhd_descent_smul R U p q r α c

/-- The absolute cap product at a single neighbourhood `U`, producing a map
`H_n(X, Kᶜ; R) → H_q(X, Kᶜ; R)` from a Čech cohomology class for `U`.
Built by composing inverse excision, the local cap product, and forward
excision. -/
def absCapProductOnNbhd
    (X : TopCat.{0}) (K : Set X) (_hK : IsClosed K)
    (n p q : ℕ) (hpq : p + q = n)
    (U : CechCohomology.OpenNeighborhoods K) :
    CechCohomology.cechFamily R K p U →ₗ[R]
      ((relSingularHomology R X Kᶜ n : Type _) →ₗ[R]
        (relSingularHomology R X Kᶜ q : Type _)) := by
  classical
  subst hpq

  let excInv := excisionInverseHomol R X K U.1 U.2 (p + q)

  let absCap := absCapOnNbhd R U p q

  let excFwd := (excisionForwardHomol R X K U.1 q).hom

  exact (LinearMap.llcomp R _ _ _ excFwd).comp
    ((LinearMap.lcomp R _ excInv).comp absCap)


/-- The transition map on relative homology between two nested open
neighbourhoods of `K`, defined as inverse excision into `U₁` composed with
forward excision out of `U₂`. -/
def absNbhdHomologyIncl
    {X : TopCat.{0}} {K : Set X}
    (U₁ U₂ : CechCohomology.OpenNeighborhoods K) (_h : U₁ ≤ U₂) (n : ℕ) :
    (relSingularHomology R (TopCat.of ↑U₂.1.1)
      (Subtype.val ⁻¹' Kᶜ) n : Type _) →ₗ[R]
      (relSingularHomology R (TopCat.of ↑U₁.1.1)
        (Subtype.val ⁻¹' Kᶜ) n : Type _) := by
  classical
  exact (excisionInverseHomol R X K U₁.1 U₁.2 n).comp
    ((excisionForwardHomol R X K U₂.1 n).hom)


/-- Compatibility of `excisionInverseHomol` with the transition map
`absNbhdHomologyIncl` between nested open neighbourhoods of `K`. -/
theorem absNbhdExcisionInverse_compatible
    {X : TopCat.{0}} {K : Set X}
    (U₁ U₂ : CechCohomology.OpenNeighborhoods K) (h : U₁ ≤ U₂) (n : ℕ)
    (y : (relSingularHomology R X Kᶜ n : Type _)) :
    excisionInverseHomol R X K U₁.1 U₁.2 n y =
    absNbhdHomologyIncl R U₁ U₂ h n
      (excisionInverseHomol R X K U₂.1 U₂.2 n y) := by
  classical
  simp only [absNbhdHomologyIncl, LinearMap.comp_apply]
  congr 1
  simp only [excisionInverseHomol]
  haveI := excisionForwardHomol_isIso R X K U₂.1 U₂.2 n
  change y = (inv (excisionForwardHomol R X K U₂.1 n) ≫ excisionForwardHomol R X K U₂.1 n).hom y
  rw [IsIso.inv_hom_id]
  rfl


/-- Naturality of `absCapOnNbhd` with respect to refinement of open
neighbourhoods of `K`. -/
theorem absCapOnNbhd_naturality
    {X : TopCat.{0}} {K : Set X}
    (U₁ U₂ : CechCohomology.OpenNeighborhoods K) (h : U₁ ≤ U₂)
    (p q : ℕ)
    (x : CechCohomology.cechFamily R K p U₁)
    (z : (relSingularHomology R (TopCat.of ↑U₂.1.1)
      (Subtype.val ⁻¹' Kᶜ) (p + q) : Type _)) :
    absNbhdHomologyIncl R U₁ U₂ h q
      (absCapOnNbhd R U₂ p q (CechCohomology.cechTransition R K p U₁ U₂ h x) z) =
    absCapOnNbhd R U₁ p q x
      (absNbhdHomologyIncl R U₁ U₂ h (p + q) z) := by sorry


/-- Compatibility of the forward excision map with the transition
`absNbhdHomologyIncl`: the value at `U₂` agrees with the value at `U₁` after
inclusion. -/
theorem absExcisionForward_compatible
    {X : TopCat.{0}} {K : Set X}
    (U₁ U₂ : CechCohomology.OpenNeighborhoods K) (h : U₁ ≤ U₂) (q : ℕ)
    (w : (relSingularHomology R (TopCat.of ↑U₂.1.1)
      (Subtype.val ⁻¹' Kᶜ) q : Type _)) :
    (excisionForwardHomol R X K U₂.1 q).hom w =
    (excisionForwardHomol R X K U₁.1 q).hom
      (absNbhdHomologyIncl R U₁ U₂ h q w) := by
  classical
  simp only [absNbhdHomologyIncl, LinearMap.comp_apply]
  simp only [excisionInverseHomol]
  haveI := excisionForwardHomol_isIso R X K U₁.1 U₁.2 q
  change (excisionForwardHomol R X K U₂.1 q).hom w =
    (excisionForwardHomol R X K U₁.1 q).hom
      ((inv (excisionForwardHomol R X K U₁.1 q)).hom
        ((excisionForwardHomol R X K U₂.1 q).hom w))
  conv_rhs => rw [show (inv (excisionForwardHomol R X K U₁.1 q)).hom
      ((excisionForwardHomol R X K U₂.1 q).hom w) =
    (excisionForwardHomol R X K U₂.1 q ≫ inv (excisionForwardHomol R X K U₁.1 q)).hom w
    from rfl]
  rw [show (excisionForwardHomol R X K U₁.1 q).hom
    ((excisionForwardHomol R X K U₂.1 q ≫ inv (excisionForwardHomol R X K U₁.1 q)).hom w) =
    (excisionForwardHomol R X K U₂.1 q ≫ inv (excisionForwardHomol R X K U₁.1 q) ≫
      excisionForwardHomol R X K U₁.1 q).hom w from rfl]
  simp only [IsIso.inv_hom_id, Category.comp_id]


/-- The composite naturality statement assembling
`absExcisionForward_compatible`, `absCapOnNbhd_naturality` and
`absNbhdExcisionInverse_compatible` for the absolute cap product. -/
theorem absCapProductOnNbhd_composite_naturality
    {X : TopCat.{0}} {K : Set X}
    (hK : IsClosed K)
    (p q : ℕ)
    (U₁ U₂ : CechCohomology.OpenNeighborhoods K) (h : U₁ ≤ U₂)
    (x : CechCohomology.cechFamily R K p U₁)
    (y : (relSingularHomology R X Kᶜ (p + q) : Type _)) :
    (excisionForwardHomol R X K U₂.1 q).hom
      (absCapOnNbhd R U₂ p q (CechCohomology.cechTransition R K p U₁ U₂ h x)
        (excisionInverseHomol R X K U₂.1 U₂.2 (p + q) y)) =
    (excisionForwardHomol R X K U₁.1 q).hom
      (absCapOnNbhd R U₁ p q x
        (excisionInverseHomol R X K U₁.1 U₁.2 (p + q) y)) := by

  rw [absExcisionForward_compatible R U₁ U₂ h q]

  rw [absCapOnNbhd_naturality R U₁ U₂ h p q x]

  rw [absNbhdExcisionInverse_compatible R U₁ U₂ h (p + q) y]

/-- Compatibility of `absCapProductOnNbhd` with the Čech transition maps,
which lets it descend to the direct limit `Ȟ^p(K; R)`. -/
theorem absCapProductOnNbhd_compatible
    (X : TopCat.{0}) (K : Set X) (hK : IsClosed K)
    (n p q : ℕ) (hpq : p + q = n)
    (U₁ U₂ : CechCohomology.OpenNeighborhoods K) (h : U₁ ≤ U₂)
    (x : CechCohomology.cechFamily R K p U₁) :
    absCapProductOnNbhd R X K hK n p q hpq U₂
      (CechCohomology.cechTransition R K p U₁ U₂ h x) =
    absCapProductOnNbhd R X K hK n p q hpq U₁ x := by
  subst hpq
  ext y
  dsimp only [absCapProductOnNbhd]
  exact absCapProductOnNbhd_composite_naturality R hK p q U₁ U₂ h x y


/-- The absolute cap product
`Ȟ^p(K; R) ⊗ H_n(X, Kᶜ; R) → H_q(X, Kᶜ; R)` for `p + q = n`, obtained by
descending `absCapProductOnNbhd` to the direct-limit description of
`Ȟ^p(K; R)`. -/
def cechCapAbsolute
    (X : TopCat.{0}) (K : Set X) (hK : IsClosed K)
    (n p q : ℕ) (hpq : p + q = n) :
    (cechCohomology R X K p ⊗ relSingularHomology R X Kᶜ n ⟶
      relSingularHomology R X Kᶜ q) := by
  classical
  let capLifted : (cechCohomology R X K p : Type _) →ₗ[R]
      ((relSingularHomology R X Kᶜ n : Type _) →ₗ[R]
        (relSingularHomology R X Kᶜ q : Type _)) :=
    Module.DirectLimit.lift R _ (CechCohomology.cechFamily R K p)
      (fun U₁ U₂ h => CechCohomology.cechTransition R K p U₁ U₂ h)
      (fun U => absCapProductOnNbhd R X K hK n p q hpq U)
      (fun U₁ U₂ h x => absCapProductOnNbhd_compatible R X K hK n p q hpq
        U₁ U₂ h x)
  exact ModuleCat.ofHom (TensorProduct.lift capLifted)

/-- The absolute cap product for the subspace `L`:
`Ȟ^p(L; R) ⊗ H_n(X, Lᶜ; R) → H_q(X, Lᶜ; R)`. Same construction as
`cechCapAbsolute`, but applied to `L` rather than `K`. -/
def cechCapL
    (X : TopCat.{0}) (L : Set X) (hL : IsClosed L)
    (n p q : ℕ) (hpq : p + q = n) :
    (cechCohomology R X L p ⊗ relSingularHomology R X Lᶜ n ⟶
      relSingularHomology R X Lᶜ q) := by
  classical
  let capLifted : (cechCohomology R X L p : Type _) →ₗ[R]
      ((relSingularHomology R X Lᶜ n : Type _) →ₗ[R]
        (relSingularHomology R X Lᶜ q : Type _)) :=
    Module.DirectLimit.lift R _ (CechCohomology.cechFamily R L p)
      (fun U₁ U₂ h => CechCohomology.cechTransition R L p U₁ U₂ h)
      (fun U => absCapProductOnNbhd R X L hL n p q hpq U)
      (fun U₁ U₂ h x => absCapProductOnNbhd_compatible R X L hL n p q hpq
        U₁ U₂ h x)
  exact ModuleCat.ofHom (TensorProduct.lift capLifted)

/-- The natural map `H_n(X; R) → H_n(X, Kᶜ; R)` from absolute to relative
singular homology, induced by the cokernel projection of the relativizing
chain map. -/
def absToRelHomol
    (X : TopCat.{0}) (K : Set X) (n : ℕ) :
    absSingularHomology R X n ⟶ relSingularHomology R X Kᶜ n :=
  HomologicalComplex.homologyMap (cokernel.π (inclChainMap R X Kᶜ)) n


/-- A chain-level splitting/section of relative chains
`S_*(Lᶜ, Lᶜ ∩ Kᶜ; R) → S_*(Lᶜ; R)`, used to construct the comparison map
between the relative and absolute homology groups appearing in Theorem 36.1. -/
noncomputable def relToAbsChainMap
    (X : TopCat.{0}) (K L : Set X) :
    relSingChainCx R (TopCat.of (Lᶜ : Set X)) (complementInComplement X K L) ⟶
      singChainCx R (TopCat.of (Lᶜ : Set X)) := by sorry

/-- The composite map `H_q(Lᶜ, Lᶜ ∩ Kᶜ; R) → H_q(X; R)` obtained by first
applying `relToAbsChainMap` and then including `Lᶜ ↪ X`. -/
def relComplementToAbs
    (X : TopCat.{0}) (K L : Set X) (q : ℕ) :
    relSingularHomology R (TopCat.of (Lᶜ : Set X))
      (complementInComplement X K L) q ⟶
      absSingularHomology R X q :=
  HomologicalComplex.homologyMap (relToAbsChainMap R X K L) q ≫
    HomologicalComplex.homologyMap
      (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (subtypeIncl X Lᶜ)) q


/-- The Alexander–Whitney cap product short-complex map at the level of
absolute singular chains on `X`, parametrized by a Čech class `α` on a
neighbourhood `U` of `K`. -/
noncomputable def awCapAbsShortComplexMap
    {X : TopCat.{0}} {K : Set X}
    (U : CechCohomology.OpenNeighborhoods K) (p q : ℕ)
    (α : CechCohomology.cechFamily R K p U) :
    (singChainCx R X).sc (p + q) ⟶ (singChainCx R X).sc q := by sorry

/-- Additivity of `awCapAbsShortComplexMap` in the Čech class `α`. -/
theorem awCapAbsShortComplexMap_add
    {X : TopCat.{0}} {K : Set X}
    (U : CechCohomology.OpenNeighborhoods K) (p q : ℕ)
    (α₁ α₂ : CechCohomology.cechFamily R K p U) :
    awCapAbsShortComplexMap R U p q (α₁ + α₂) =
      awCapAbsShortComplexMap R U p q α₁ + awCapAbsShortComplexMap R U p q α₂ := by sorry

/-- `R`-linearity of `awCapAbsShortComplexMap` in the Čech class `α`. -/
theorem awCapAbsShortComplexMap_smul
    {X : TopCat.{0}} {K : Set X}
    (U : CechCohomology.OpenNeighborhoods K) (p q : ℕ)
    (r : R) (α : CechCohomology.cechFamily R K p U) :
    awCapAbsShortComplexMap R U p q (r • α) =
      r • awCapAbsShortComplexMap R U p q α := by sorry


/-- Naturality of `awCapAbsShortComplexMap` along the Čech transition maps;
allows the absolute cap product on absolute homology to descend to the
direct limit. -/
theorem awCapAbsShortComplexMap_naturality
    {X : TopCat.{0}} {K : Set X}
    (U₁ U₂ : CechCohomology.OpenNeighborhoods K) (h : U₁ ≤ U₂)
    (p q : ℕ)
    (x : CechCohomology.cechFamily R K p U₁) :
    awCapAbsShortComplexMap R U₂ p q
      (CechCohomology.cechTransition R K p U₁ U₂ h x) =
    awCapAbsShortComplexMap R U₁ p q x := by sorry

/-- Passage of `awCapAbsShortComplexMap` to absolute singular homology:
gives a linear map `H_{p+q}(X; R) → H_q(X; R)` parametrized by a Čech
cohomology class `α` on a neighbourhood `U` of `K`. -/
def awCapDescendsToAbsHomology
    {X : TopCat.{0}} {K : Set X}
    (U : CechCohomology.OpenNeighborhoods K) (p q : ℕ)
    (α : CechCohomology.cechFamily R K p U) :
    (absSingularHomology R X (p + q) : Type _) →ₗ[R]
    (absSingularHomology R X q : Type _) :=
  (ShortComplex.homologyMap (awCapAbsShortComplexMap R U p q α)).hom

/-- Additivity of `awCapDescendsToAbsHomology` in the Čech class `α`. -/
theorem awCapDescendsToAbsHomology_add
    {X : TopCat.{0}} {K : Set X}
    (U : CechCohomology.OpenNeighborhoods K) (p q : ℕ)
    (α₁ α₂ : CechCohomology.cechFamily R K p U)
    (z : (absSingularHomology R X (p + q) : Type _)) :
    awCapDescendsToAbsHomology R U p q (α₁ + α₂) z =
      awCapDescendsToAbsHomology R U p q α₁ z +
      awCapDescendsToAbsHomology R U p q α₂ z := by
  show (ShortComplex.homologyMap (awCapAbsShortComplexMap R U p q (α₁ + α₂))).hom z =
    (ShortComplex.homologyMap (awCapAbsShortComplexMap R U p q α₁)).hom z +
    (ShortComplex.homologyMap (awCapAbsShortComplexMap R U p q α₂)).hom z
  rw [awCapAbsShortComplexMap_add, ShortComplex.homologyMap_add]; rfl

/-- `R`-linearity of `awCapDescendsToAbsHomology` in the Čech class `α`. -/
theorem awCapDescendsToAbsHomology_smul
    {X : TopCat.{0}} {K : Set X}
    (U : CechCohomology.OpenNeighborhoods K) (p q : ℕ)
    (r : R) (α : CechCohomology.cechFamily R K p U)
    (z : (absSingularHomology R X (p + q) : Type _)) :
    awCapDescendsToAbsHomology R U p q (r • α) z =
      r • awCapDescendsToAbsHomology R U p q α z := by
  show (ShortComplex.homologyMap (awCapAbsShortComplexMap R U p q (r • α))).hom z =
    r • (ShortComplex.homologyMap (awCapAbsShortComplexMap R U p q α)).hom z
  rw [awCapAbsShortComplexMap_smul, ShortComplex.homologyMap_smul]; rfl


/-- The absolute cap product on absolute singular homology at a single
neighbourhood `U`, packaged as an `R`-linear map from the Čech family to the
space of linear maps `H_{p+q}(X; R) → H_q(X; R)`. -/
def absCapOnNbhdAbsHomol
    {X : TopCat.{0}} {K : Set X}
    (U : CechCohomology.OpenNeighborhoods K) (p q : ℕ) :
    CechCohomology.cechFamily R K p U →ₗ[R]
      ((absSingularHomology R X (p + q) : Type _) →ₗ[R]
        (absSingularHomology R X q : Type _)) where
  toFun α := awCapDescendsToAbsHomology R U p q α
  map_add' α₁ α₂ := LinearMap.ext fun z =>
    awCapDescendsToAbsHomology_add R U p q α₁ α₂ z
  map_smul' r α := LinearMap.ext fun z =>
    awCapDescendsToAbsHomology_smul R U p q r α z


/-- Naturality of `absCapOnNbhdAbsHomol` along the Čech transition maps:
needed to descend the absolute cap product on absolute homology to the
direct limit `Ȟ^p(K; R)`. -/
theorem absCapOnNbhdAbsHomol_naturality
    {X : TopCat.{0}} {K : Set X}
    (p q : ℕ)
    (U₁ U₂ : CechCohomology.OpenNeighborhoods K) (h : U₁ ≤ U₂)
    (x : CechCohomology.cechFamily R K p U₁)
    (z : (absSingularHomology R X (p + q) : Type _)) :
    absCapOnNbhdAbsHomol R U₂ p q
      (CechCohomology.cechTransition R K p U₁ U₂ h x) z =
    absCapOnNbhdAbsHomol R U₁ p q x z := by
  show (ShortComplex.homologyMap
    (awCapAbsShortComplexMap R U₂ p q (CechCohomology.cechTransition R K p U₁ U₂ h x))).hom z =
    (ShortComplex.homologyMap (awCapAbsShortComplexMap R U₁ p q x)).hom z
  rw [awCapAbsShortComplexMap_naturality R U₁ U₂ h p q x]

/-- `n`-indexed packaging of `absCapOnNbhdAbsHomol` for use in the descent to
the direct limit, substituting `hpq : p + q = n`. -/
def absCapProductOnNbhdAbs
    (X : TopCat.{0}) (K : Set X) (_hK : IsClosed K)
    (n p q : ℕ) (hpq : p + q = n)
    (U : CechCohomology.OpenNeighborhoods K) :
    CechCohomology.cechFamily R K p U →ₗ[R]
      ((absSingularHomology R X n : Type _) →ₗ[R]
        (absSingularHomology R X q : Type _)) := by
  subst hpq
  exact absCapOnNbhdAbsHomol R U p q

/-- Compatibility of `absCapProductOnNbhdAbs` with Čech transition maps, used
to descend to the direct limit. -/
theorem absCapProductOnNbhdAbs_compatible
    (X : TopCat.{0}) (K : Set X) (hK : IsClosed K)
    (n p q : ℕ) (hpq : p + q = n)
    (U₁ U₂ : CechCohomology.OpenNeighborhoods K) (h : U₁ ≤ U₂)
    (x : CechCohomology.cechFamily R K p U₁) :
    absCapProductOnNbhdAbs R X K hK n p q hpq U₂
      (CechCohomology.cechTransition R K p U₁ U₂ h x) =
    absCapProductOnNbhdAbs R X K hK n p q hpq U₁ x := by
  subst hpq
  ext z
  dsimp only [absCapProductOnNbhdAbs]
  exact absCapOnNbhdAbsHomol_naturality R p q U₁ U₂ h x z

/-- The cap product with `K`-Čech cohomology landing in absolute singular
homology: `Ȟ^p(K; R) ⊗ H_n(X; R) → H_q(X; R)` for `p + q = n`. -/
def cechCapAbsK
    (X : TopCat.{0}) (K : Set X) (hK : IsClosed K)
    (n p q : ℕ) (hpq : p + q = n) :
    (cechCohomology R X K p ⊗ absSingularHomology R X n ⟶
      absSingularHomology R X q) := by
  classical
  let capLifted : (cechCohomology R X K p : Type _) →ₗ[R]
      ((absSingularHomology R X n : Type _) →ₗ[R]
        (absSingularHomology R X q : Type _)) :=
    Module.DirectLimit.lift R _ (CechCohomology.cechFamily R K p)
      (fun U₁ U₂ h => CechCohomology.cechTransition R K p U₁ U₂ h)
      (fun U => absCapProductOnNbhdAbs R X K hK n p q hpq U)
      (fun U₁ U₂ h x => absCapProductOnNbhdAbs_compatible R X K hK n p q hpq
        U₁ U₂ h x)
  exact ModuleCat.ofHom (TensorProduct.lift capLifted)

/-- The cap product with `L`-Čech cohomology landing in absolute singular
homology: `Ȟ^p(L; R) ⊗ H_n(X; R) → H_q(X; R)` for `p + q = n`. -/
def cechCapAbsL
    (X : TopCat.{0}) (L : Set X) (hL : IsClosed L)
    (n p q : ℕ) (hpq : p + q = n) :
    (cechCohomology R X L p ⊗ absSingularHomology R X n ⟶
      absSingularHomology R X q) := by
  classical
  let capLifted : (cechCohomology R X L p : Type _) →ₗ[R]
      ((absSingularHomology R X n : Type _) →ₗ[R]
        (absSingularHomology R X q : Type _)) :=
    Module.DirectLimit.lift R _ (CechCohomology.cechFamily R L p)
      (fun U₁ U₂ h => CechCohomology.cechTransition R L p U₁ U₂ h)
      (fun U => absCapProductOnNbhdAbs R X L hL n p q hpq U)
      (fun U₁ U₂ h x => absCapProductOnNbhdAbs_compatible R X L hL n p q hpq
        U₁ U₂ h x)
  exact ModuleCat.ofHom (TensorProduct.lift capLifted)

/-- The fully relative cap product applied to a class in absolute homology:
`Ȟ^p(K, L; R) ⊗ H_n(X; R) → H_q(Lᶜ, Lᶜ ∩ Kᶜ; R)`, obtained by first sending
`H_n(X; R)` to `H_n(X, Kᶜ; R)` and then capping. -/
def fullyRelativeCapProductAbs
    (X : TopCat.{0}) (K L : Set X)
    (hLK : L ⊆ K) (hK : IsClosed K) (hL : IsClosed L)
    (n p q : ℕ) (hpq : p + q = n) :
    (cechCohomologyRel R X K L p ⊗ absSingularHomology R X n ⟶
      relSingularHomology R (TopCat.of (Lᶜ : Set X))
        (complementInComplement X K L) q) :=
  whiskerLeft (cechCohomologyRel R X K L p) (absToRelHomol R X K n) ≫
    fullyRelativeCapProduct R X K L hLK hK hL n p q hpq

/-- All data witnessing Theorem 36.1: a fully relative cap product
`Ȟ^p(K, L; R) ⊗ H_n(X, Kᶜ; R) → H_q(Lᶜ, Lᶜ ∩ Kᶜ; R)` together with the two
commuting ladders ("first" using `H_n(X, Kᶜ)` and "second" using `H_n(X)`)
involving the long exact sequences of the pairs `(K, L)` in Čech cohomology
and the relative homology long exact sequences in singular homology. -/
structure FullyRelativeCapProductData
    (X : TopCat.{0}) (K L : Set X)
    (hLK : L ⊆ K) (hK : IsClosed K) (hL : IsClosed L)
    (n : ℕ) where
  capProduct : ∀ (p q : ℕ) (_hpq : p + q = n),
    (cechCohomologyRel R X K L p ⊗ relSingularHomology R X Kᶜ n ⟶
      relSingularHomology R (TopCat.of (Lᶜ : Set X))
        (complementInComplement X K L) q)
  firstLadder_restrict : ∀ (p q : ℕ) (hpq : p + q = n),
    capProduct p q hpq ≫ homolTripleInclusion R X K L q =
      whiskerRight (cechCohomRestrict R X K L p)
        (relSingularHomology R X Kᶜ n) ≫
      cechCapAbsolute R X K hK n p q hpq
  firstLadder_subspace : ∀ (p q : ℕ) (hpq : p + q = n),
    cechCapAbsolute R X K hK n p q hpq ≫ homolRestriction R X K L q =
      tensorHom (cechCohomToSubspace R X K L p)
        (homolRestriction R X K L n) ≫
      cechCapL R X L hL n p q hpq
  firstLadder_coboundary : ∀ (p q : ℕ) (hpq : p + (q + 1) = n),
    whiskerRight (cechCohomCoboundary R X K L p)
      (relSingularHomology R X Kᶜ n) ≫
      capProduct (p + 1) q (by omega) =
    whiskerLeft (cechCohomology R X L p)
      (homolRestriction R X K L n) ≫
      cechCapL R X L hL n p (q + 1) hpq ≫
      homolTripleBoundary R X K L q
  secondLadder_restrict : ∀ (p q : ℕ) (hpq : p + q = n),
    whiskerRight (cechCohomRestrict R X K L p)
      (absSingularHomology R X n) ≫
      cechCapAbsK R X K hK n p q hpq =
    fullyRelativeCapProductAbs R X K L hLK hK hL n p q hpq ≫
      relComplementToAbs R X K L q
  secondLadder_subspace : ∀ (p q : ℕ) (hpq : p + q = n),
    cechCapAbsK R X K hK n p q hpq =
      whiskerRight (cechCohomToSubspace R X K L p)
        (absSingularHomology R X n) ≫
      cechCapAbsL R X L hL n p q hpq
  secondLadder_coboundary : ∀ (p q : ℕ) (hpq : p + (q + 1) = n),
    whiskerRight (cechCohomCoboundary R X K L p)
      (absSingularHomology R X n) ≫
      fullyRelativeCapProductAbs R X K L hLK hK hL n (p + 1) q (by omega) =
    cechCapAbsL R X L hL n p (q + 1) hpq ≫
      absToRelHomol R X L (q + 1) ≫
      homolTripleBoundary R X K L q


/-- First commutative square (restriction) in the first ladder of
Theorem 36.1: capping with `Ȟ^p(K, L; R)` and projecting `H_q(Lᶜ, Lᶜ ∩ Kᶜ)`
into `H_q(X, Kᶜ)` agrees with restricting `Ȟ^p(K, L; R) → Ȟ^p(K; R)` and
then applying the absolute cap product. -/
theorem theorem_36_1_firstLadder_restrict
    (X : TopCat.{0}) (K L : Set X)
    (hLK : L ⊆ K) (hK : IsClosed K) (hL : IsClosed L)
    (n p q : ℕ) (hpq : p + q = n) :
    fullyRelativeCapProduct R X K L hLK hK hL n p q hpq ≫
      homolTripleInclusion R X K L q =
    whiskerRight (cechCohomRestrict R X K L p)
      (relSingularHomology R X Kᶜ n) ≫
    cechCapAbsolute R X K hK n p q hpq := by sorry


/-- Second commutative square (subspace) in the first ladder of Theorem 36.1:
the absolute cap product with `K` followed by restricting `Kᶜ → Lᶜ` agrees
with restricting both `K → L` (in Čech cohomology) and `Kᶜ → Lᶜ` (in
singular homology) and then capping with `L`. -/
theorem theorem_36_1_firstLadder_subspace
    (X : TopCat.{0}) (K L : Set X)
    (hLK : L ⊆ K) (hK : IsClosed K) (hL : IsClosed L)
    (n p q : ℕ) (hpq : p + q = n) :
    cechCapAbsolute R X K hK n p q hpq ≫ homolRestriction R X K L q =
    tensorHom (cechCohomToSubspace R X K L p)
      (homolRestriction R X K L n) ≫
    cechCapL R X L hL n p q hpq := by sorry


/-- Coboundary commutative square in the first ladder of Theorem 36.1: the
Čech coboundary `Ȟ^p(L; R) → Ȟ^{p+1}(K, L; R)` is matched by the boundary
`H_{q+1}(X, Lᶜ; R) → H_q(Lᶜ, Lᶜ ∩ Kᶜ; R)` of the long exact sequence of the
triple. -/
theorem theorem_36_1_firstLadder_coboundary
    (X : TopCat.{0}) (K L : Set X)
    (hLK : L ⊆ K) (hK : IsClosed K) (hL : IsClosed L)
    (n p q : ℕ) (hpq : p + (q + 1) = n) :
    whiskerRight (cechCohomCoboundary R X K L p)
      (relSingularHomology R X Kᶜ n) ≫
    fullyRelativeCapProduct R X K L hLK hK hL n (p + 1) q (by omega) =
    whiskerLeft (cechCohomology R X L p)
      (homolRestriction R X K L n) ≫
    cechCapL R X L hL n p (q + 1) hpq ≫
    homolTripleBoundary R X K L q := by sorry


/-- First commutative square (restriction) in the second ladder of
Theorem 36.1, where the homology variable lies in `H_n(X)` rather than
`H_n(X, Kᶜ)`. -/
theorem theorem_36_1_secondLadder_restrict
    (X : TopCat.{0}) (K L : Set X)
    (hLK : L ⊆ K) (hK : IsClosed K) (hL : IsClosed L)
    (n p q : ℕ) (hpq : p + q = n) :
    whiskerRight (cechCohomRestrict R X K L p)
      (absSingularHomology R X n) ≫
    cechCapAbsK R X K hK n p q hpq =
    fullyRelativeCapProductAbs R X K L hLK hK hL n p q hpq ≫
    relComplementToAbs R X K L q := by sorry


/-- Second commutative square (subspace) in the second ladder of
Theorem 36.1: cap with `Ȟ^p(K)` agrees with first restricting `K → L` and
then capping with `Ȟ^p(L)`, when the homology variable lies in `H_n(X)`. -/
theorem theorem_36_1_secondLadder_subspace
    (X : TopCat.{0}) (K L : Set X)
    (hLK : L ⊆ K) (hK : IsClosed K) (hL : IsClosed L)
    (n p q : ℕ) (hpq : p + q = n) :
    cechCapAbsK R X K hK n p q hpq =
    whiskerRight (cechCohomToSubspace R X K L p)
      (absSingularHomology R X n) ≫
    cechCapAbsL R X L hL n p q hpq := by sorry


/-- Coboundary commutative square in the second ladder of Theorem 36.1: the
Čech coboundary `Ȟ^p(L) → Ȟ^{p+1}(K, L)` is matched by the composite
`H_{q+1}(X, Lᶜ) → H_q(Lᶜ, Lᶜ ∩ Kᶜ)` of the long exact sequence of the
triple. -/
theorem theorem_36_1_secondLadder_coboundary
    (X : TopCat.{0}) (K L : Set X)
    (hLK : L ⊆ K) (hK : IsClosed K) (hL : IsClosed L)
    (n p q : ℕ) (hpq : p + (q + 1) = n) :
    whiskerRight (cechCohomCoboundary R X K L p)
      (absSingularHomology R X n) ≫
    fullyRelativeCapProductAbs R X K L hLK hK hL n (p + 1) q (by omega) =
    cechCapAbsL R X L hL n p (q + 1) hpq ≫
    absToRelHomol R X L (q + 1) ≫
    homolTripleBoundary R X K L q := by sorry

/-- **Theorem 36.1.** For closed subspaces `L ⊆ K` of `X`, there is a fully
relative cap product
`∩ : Ȟ^p(K, L; R) ⊗ H_n(X, X - K; R) → H_q(X - L, X - K; R)`, `p + q = n`,
such that for any `x_K ∈ H_n(X, X - K)` the ladder involving the long exact
sequences of the pairs `(K, L)` in Čech cohomology and the corresponding
relative singular homology long exact sequences commutes (with `x_L` the
restriction of `x_K` to `H_n(X, X - L)`), and for any `x ∈ H_n(X)` the
corresponding ladder also commutes (with `x_K` the restriction of `x` to
`H_n(X, X - K)`). Packaged as a `FullyRelativeCapProductData`. -/
def theorem_36_1
    (X : TopCat.{0}) (K L : Set X)
    (hLK : L ⊆ K) (hK : IsClosed K) (hL : IsClosed L) (n : ℕ) :
    FullyRelativeCapProductData R X K L hLK hK hL n where
  capProduct p q hpq := fullyRelativeCapProduct R X K L hLK hK hL n p q hpq
  firstLadder_restrict p q hpq :=
    theorem_36_1_firstLadder_restrict R X K L hLK hK hL n p q hpq
  firstLadder_subspace p q hpq :=
    theorem_36_1_firstLadder_subspace R X K L hLK hK hL n p q hpq
  firstLadder_coboundary p q hpq :=
    theorem_36_1_firstLadder_coboundary R X K L hLK hK hL n p q hpq
  secondLadder_restrict p q hpq :=
    theorem_36_1_secondLadder_restrict R X K L hLK hK hL n p q hpq
  secondLadder_subspace p q hpq :=
    theorem_36_1_secondLadder_subspace R X K L hLK hK hL n p q hpq
  secondLadder_coboundary p q hpq :=
    theorem_36_1_secondLadder_coboundary R X K L hLK hK hL n p q hpq

end FullyRelativeCapProduct

open Set FullyRelativeCapProduct

/-- The standing hypothesis for the Čech/singular Mayer–Vietoris compatibility
theorem: either `X` is a normal space and `A, B` are closed in `X`, or `X` is
Hausdorff and `A, B` are compact. -/
def MayerVietorisHypothesis (X : Type*) [TopologicalSpace X]
    (A B : Set X) : Prop :=
  (NormalSpace X ∧ IsClosed A ∧ IsClosed B) ∨
  (T2Space X ∧ IsCompact A ∧ IsCompact B)

/-- Data witnessing the Čech/singular Mayer–Vietoris compatibility ladder of
Theorem 36.2: a Mayer–Vietoris sequence in Čech cohomology of `A, B, A ∪ B,
A ∩ B`, a Mayer–Vietoris sequence in relative singular homology of their
complements, exactness of both sequences, "cap rungs" connecting them indexed
by subsets `S ∈ {A, B, A ∪ B, A ∩ B}` for each `(p, q)` with `p + q = n`, and
three commutative squares expressing compatibility with the union-to-sum,
sum-to-intersection, and connecting morphisms. -/
structure MayerVietorisLadder (R : Type) [CommRing R]
    (X : TopCat.{0}) (A B : Set X) (n : ℕ)
    (x_union : relSingularHomology R X (A ∪ B)ᶜ n) where

  topUnionToSum : ∀ p : ℕ,
    (cechCohomology R X (A ∪ B) p ⟶
      cechCohomology R X A p ⊞ cechCohomology R X B p)
  topSumToInter : ∀ p : ℕ,
    (cechCohomology R X A p ⊞ cechCohomology R X B p ⟶
      cechCohomology R X (A ∩ B) p)
  topConnecting : ∀ p : ℕ,
    (cechCohomology R X (A ∩ B) p ⟶ cechCohomology R X (A ∪ B) (p + 1))

  botUnionToSum : ∀ q : ℕ,
    (relSingularHomology R X (A ∪ B)ᶜ q ⟶
      relSingularHomology R X Aᶜ q ⊞ relSingularHomology R X Bᶜ q)
  botSumToInter : ∀ q : ℕ,
    (relSingularHomology R X Aᶜ q ⊞ relSingularHomology R X Bᶜ q ⟶
      relSingularHomology R X (A ∩ B)ᶜ q)
  botConnecting : ∀ q : ℕ,
    (relSingularHomology R X (A ∩ B)ᶜ q ⟶ relSingularHomology R X (A ∪ B)ᶜ (q - 1))
  capRung : ∀ (p q : ℕ) (S : Set X), p + q = n →
    (cechCohomology R X S p ⟶ relSingularHomology R X Sᶜ q)

  top_exact_sum : ∀ p : ℕ, Function.Exact
    (topUnionToSum p).hom (topSumToInter p).hom
  top_exact_inter : ∀ p : ℕ, Function.Exact
    (topSumToInter p).hom (topConnecting p).hom
  top_exact_union : ∀ p : ℕ, Function.Exact
    (topConnecting p).hom (topUnionToSum (p + 1)).hom

  bot_exact_sum : ∀ q : ℕ, Function.Exact
    (botUnionToSum q).hom (botSumToInter q).hom
  bot_exact_inter : ∀ q : ℕ, Function.Exact
    (botSumToInter q).hom (botConnecting q).hom
  bot_exact_union : ∀ q : ℕ, Function.Exact
    (botConnecting q).hom (botUnionToSum (q - 1)).hom

  comm_sq1 : ∀ (p q : ℕ) (hpq : p + q = n),
    capRung p q (A ∪ B) hpq ≫ botUnionToSum q =
      topUnionToSum p ≫ Limits.biprod.map (capRung p q A hpq) (capRung p q B hpq)
  comm_sq2 : ∀ (p q : ℕ) (hpq : p + q = n),
    Limits.biprod.map (capRung p q A hpq) (capRung p q B hpq) ≫ botSumToInter q =
      topSumToInter p ≫ capRung p q (A ∩ B) hpq
  comm_sq3 : ∀ (p q : ℕ) (hpq : p + q = n) (hpq' : (p + 1) + (q - 1) = n),
    topConnecting p ≫ capRung (p + 1) (q - 1) (A ∪ B) hpq' =
      capRung p q (A ∩ B) hpq ≫ botConnecting q

/-- Abstract data of a Mayer–Vietoris long exact sequence in Čech cohomology
for the cover `A, B` of `A ∪ B`: a union-to-sum map, a sum-to-intersection
map, a degree-raising connecting morphism, and the three exactness conditions
making the resulting sequence long exact. -/
structure CechMVSequence (R : Type) [CommRing R]
    (X : TopCat.{0}) (A B : Set X) where
  unionToSum : ∀ p : ℕ,
    (cechCohomology R X (A ∪ B) p ⟶
      cechCohomology R X A p ⊞ cechCohomology R X B p)
  sumToInter : ∀ p : ℕ,
    (cechCohomology R X A p ⊞ cechCohomology R X B p ⟶
      cechCohomology R X (A ∩ B) p)
  connecting : ∀ p : ℕ,
    (cechCohomology R X (A ∩ B) p ⟶ cechCohomology R X (A ∪ B) (p + 1))
  exact_sum : ∀ p : ℕ, Function.Exact
    (unionToSum p).hom (sumToInter p).hom
  exact_inter : ∀ p : ℕ, Function.Exact
    (sumToInter p).hom (connecting p).hom
  exact_union : ∀ p : ℕ, Function.Exact
    (connecting p).hom (unionToSum (p + 1)).hom

/-- Abstract data of a Mayer–Vietoris long exact sequence in relative singular
homology for the cover `A, B` of `A ∪ B` (taken in the complements): a
union-to-sum map, a sum-to-intersection map, a degree-lowering connecting
morphism, and the three exactness conditions. -/
structure SingularMVSequence (R : Type) [CommRing R]
    (X : TopCat.{0}) (A B : Set X) where
  unionToSum : ∀ q : ℕ,
    (relSingularHomology R X (A ∪ B)ᶜ q ⟶
      relSingularHomology R X Aᶜ q ⊞ relSingularHomology R X Bᶜ q)
  sumToInter : ∀ q : ℕ,
    (relSingularHomology R X Aᶜ q ⊞ relSingularHomology R X Bᶜ q ⟶
      relSingularHomology R X (A ∩ B)ᶜ q)
  connecting : ∀ q : ℕ,
    (relSingularHomology R X (A ∩ B)ᶜ q ⟶ relSingularHomology R X (A ∪ B)ᶜ (q - 1))
  exact_sum : ∀ q : ℕ, Function.Exact
    (unionToSum q).hom (sumToInter q).hom
  exact_inter : ∀ q : ℕ, Function.Exact
    (sumToInter q).hom (connecting q).hom
  exact_union : ∀ q : ℕ, Function.Exact
    (connecting q).hom (unionToSum (q - 1)).hom

/-- The "cap rung" data connecting a Čech Mayer–Vietoris sequence to a
singular Mayer–Vietoris sequence in the presence of a fixed homology class
`x_union ∈ H_n(X, (A ∪ B)ᶜ)`: cap product maps for each subset
`S ∈ {A, B, A ∪ B, A ∩ B}` and `(p, q)` with `p + q = n`, plus the three
commutative squares expressing Mayer–Vietoris naturality. -/
structure MVCapProductData (R : Type) [CommRing R]
    (X : TopCat.{0}) (A B : Set X) (n : ℕ)
    (x_union : relSingularHomology R X (A ∪ B)ᶜ n)
    (cechMV : CechMVSequence R X A B)
    (singMV : SingularMVSequence R X A B) where
  capRung : ∀ (p q : ℕ) (S : Set X), p + q = n →
    (cechCohomology R X S p ⟶ relSingularHomology R X Sᶜ q)
  comm_sq1 : ∀ (p q : ℕ) (hpq : p + q = n),
    capRung p q (A ∪ B) hpq ≫ singMV.unionToSum q =
      cechMV.unionToSum p ≫
        Limits.biprod.map (capRung p q A hpq) (capRung p q B hpq)
  comm_sq2 : ∀ (p q : ℕ) (hpq : p + q = n),
    Limits.biprod.map (capRung p q A hpq) (capRung p q B hpq) ≫
      singMV.sumToInter q =
      cechMV.sumToInter p ≫ capRung p q (A ∩ B) hpq
  comm_sq3 : ∀ (p q : ℕ) (hpq : p + q = n) (hpq' : (p + 1) + (q - 1) = n),
    cechMV.connecting p ≫ capRung (p + 1) (q - 1) (A ∪ B) hpq' =
      capRung p q (A ∩ B) hpq ≫ singMV.connecting q

/-- The Mayer–Vietoris union-to-sum map in Čech cohomology,
`Ȟ^p(A ∪ B; R) → Ȟ^p(A; R) ⊕ Ȟ^p(B; R)`, given by pairing the two
restriction maps. -/
def cechMV_unionToSum
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X) (p : ℕ) :
    (cechCohomology R X (A ∪ B) p ⟶
      cechCohomology R X A p ⊞ cechCohomology R X B p) :=
  biprod.lift
    (cechCohomToSubspace R X (A ∪ B) A p)
    (cechCohomToSubspace R X (A ∪ B) B p)

/-- The Mayer–Vietoris sum-to-intersection map in Čech cohomology,
`Ȟ^p(A; R) ⊕ Ȟ^p(B; R) → Ȟ^p(A ∩ B; R)`, given by the difference of the
restriction maps. -/
def cechMV_sumToInter
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X) (p : ℕ) :
    (cechCohomology R X A p ⊞ cechCohomology R X B p ⟶
      cechCohomology R X (A ∩ B) p) :=
  biprod.desc
    (cechCohomToSubspace R X A (A ∩ B) p)
    (-(cechCohomToSubspace R X B (A ∩ B) p))


/-- The Mayer–Vietoris connecting morphism in Čech cohomology,
`Ȟ^p(A ∩ B; R) → Ȟ^{p+1}(A ∪ B; R)`, witnessing the long exact sequence
under the Mayer–Vietoris hypothesis. -/
noncomputable def cechMV_connecting_aux
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X)
    (hyp : MayerVietorisHypothesis X A B) (p : ℕ) :
    (cechCohomology R X (A ∩ B) p ⟶ cechCohomology R X (A ∪ B) (p + 1)) := by sorry


/-- Exactness at the sum `Ȟ^p(A; R) ⊕ Ȟ^p(B; R)` of the Čech Mayer–Vietoris
sequence: the union-to-sum map and sum-to-intersection map are exact. -/
theorem cechMV_exact_sum_aux
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X)
    (hyp : MayerVietorisHypothesis X A B) (p : ℕ) :
    Function.Exact
      (cechMV_unionToSum R X A B p).hom
      (cechMV_sumToInter R X A B p).hom := by sorry


/-- Exactness at the intersection `Ȟ^p(A ∩ B; R)` of the Čech Mayer–Vietoris
sequence: the sum-to-intersection map and the connecting morphism are exact. -/
theorem cechMV_exact_inter_aux
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X)
    (hyp : MayerVietorisHypothesis X A B) (p : ℕ) :
    Function.Exact
      (cechMV_sumToInter R X A B p).hom
      (cechMV_connecting_aux R X A B hyp p).hom := by sorry


/-- Exactness at the union `Ȟ^{p+1}(A ∪ B; R)` of the Čech Mayer–Vietoris
sequence: the connecting morphism and the next union-to-sum map are exact. -/
theorem cechMV_exact_union_aux
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X)
    (hyp : MayerVietorisHypothesis X A B) (p : ℕ) :
    Function.Exact
      (cechMV_connecting_aux R X A B hyp p).hom
      (cechMV_unionToSum R X A B (p + 1)).hom := by sorry

/-- Packages the Čech Mayer–Vietoris sequence under the Mayer–Vietoris
hypothesis, bundled with witnesses that the bundled union-to-sum and
sum-to-intersection morphisms agree with `cechMV_unionToSum` and
`cechMV_sumToInter`. -/
def cechMV_sequence_data
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X)
    (hyp : MayerVietorisHypothesis X A B) :
    { mv : CechMVSequence R X A B //
      (∀ p, mv.unionToSum p = cechMV_unionToSum R X A B p) ∧
      (∀ p, mv.sumToInter p = cechMV_sumToInter R X A B p) } :=
  ⟨{ unionToSum := cechMV_unionToSum R X A B
     sumToInter := cechMV_sumToInter R X A B
     connecting := cechMV_connecting_aux R X A B hyp
     exact_sum := cechMV_exact_sum_aux R X A B hyp
     exact_inter := cechMV_exact_inter_aux R X A B hyp
     exact_union := cechMV_exact_union_aux R X A B hyp },
   fun _ => rfl, fun _ => rfl⟩

/-- Existence of a connecting morphism `δ` making the Čech Mayer–Vietoris
sequence exact at all three positions, extracted from `cechMV_sequence_data`. -/
theorem cechMV_sequence_exact
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X)
    (hyp : MayerVietorisHypothesis X A B) (p : ℕ) :
    ∃ (δ : cechCohomology R X (A ∩ B) p ⟶ cechCohomology R X (A ∪ B) (p + 1)),
      Function.Exact
        (cechMV_unionToSum R X A B p).hom
        (cechMV_sumToInter R X A B p).hom ∧
      Function.Exact
        (cechMV_sumToInter R X A B p).hom
        δ.hom ∧
      Function.Exact
        δ.hom
        (cechMV_unionToSum R X A B (p + 1)).hom := by
  obtain ⟨mv, hmaps_union, hmaps_inter⟩ := cechMV_sequence_data R X A B hyp
  refine ⟨mv.connecting p, ?_, ?_, ?_⟩
  · rw [← hmaps_union p, ← hmaps_inter p]
    exact mv.exact_sum p
  · rw [← hmaps_inter p]
    exact mv.exact_inter p
  · rw [← hmaps_union (p + 1)]
    exact mv.exact_union p

/-- The chosen Čech Mayer–Vietoris connecting morphism extracted from
`cechMV_sequence_exact`. -/
noncomputable def cechMV_connecting
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X)
    (hyp : MayerVietorisHypothesis X A B) (p : ℕ) :
    (cechCohomology R X (A ∩ B) p ⟶ cechCohomology R X (A ∪ B) (p + 1)) :=
  (cechMV_sequence_exact R X A B hyp p).choose

/-- Exactness of the Čech Mayer–Vietoris sequence at the sum position. -/
theorem cechMV_exact_sum
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X)
    (hyp : MayerVietorisHypothesis X A B) (p : ℕ) :
    Function.Exact
      (cechMV_unionToSum R X A B p).hom
      (cechMV_sumToInter R X A B p).hom :=
  (cechMV_sequence_exact R X A B hyp p).choose_spec.1

/-- Exactness of the Čech Mayer–Vietoris sequence at the intersection
position. -/
theorem cechMV_exact_inter
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X)
    (hyp : MayerVietorisHypothesis X A B) (p : ℕ) :
    Function.Exact
      (cechMV_sumToInter R X A B p).hom
      (cechMV_connecting R X A B hyp p).hom :=
  (cechMV_sequence_exact R X A B hyp p).choose_spec.2.1

/-- Exactness of the Čech Mayer–Vietoris sequence at the union position
(after the connecting morphism). -/
theorem cechMV_exact_union
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X)
    (hyp : MayerVietorisHypothesis X A B) (p : ℕ) :
    Function.Exact
      (cechMV_connecting R X A B hyp p).hom
      (cechMV_unionToSum R X A B (p + 1)).hom :=
  (cechMV_sequence_exact R X A B hyp p).choose_spec.2.2

/-- The full Čech Mayer–Vietoris sequence as a `CechMVSequence`, packaging
together the union-to-sum, sum-to-intersection, and connecting morphisms
along with the three exactness statements. -/
noncomputable def cechMV_of_hyp
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X)
    (hyp : MayerVietorisHypothesis X A B) :
    CechMVSequence R X A B where
  unionToSum := cechMV_unionToSum R X A B
  sumToInter := cechMV_sumToInter R X A B
  connecting := cechMV_connecting R X A B hyp
  exact_sum := cechMV_exact_sum R X A B hyp
  exact_inter := cechMV_exact_inter R X A B hyp
  exact_union := cechMV_exact_union R X A B hyp


/-- The Mayer–Vietoris union-to-sum map in relative singular homology of the
complements, `H_q(X, (A ∪ B)ᶜ) → H_q(X, Aᶜ) ⊕ H_q(X, Bᶜ)`, given by pairing
the two restriction maps. -/
def singularMV_unionToSum
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X)
    (_hyp : MayerVietorisHypothesis X A B) (q : ℕ) :
    (relSingularHomology R X (A ∪ B)ᶜ q ⟶
      relSingularHomology R X Aᶜ q ⊞ relSingularHomology R X Bᶜ q) :=
  biprod.lift
    (homolRestriction R X (A ∪ B) A q)
    (homolRestriction R X (A ∪ B) B q)


/-- The Mayer–Vietoris sum-to-intersection map in relative singular homology
of the complements, `H_q(X, Aᶜ) ⊕ H_q(X, Bᶜ) → H_q(X, (A ∩ B)ᶜ)`, given by
the difference of the restriction maps. -/
def singularMV_sumToInter
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X)
    (_hyp : MayerVietorisHypothesis X A B) (q : ℕ) :
    (relSingularHomology R X Aᶜ q ⊞ relSingularHomology R X Bᶜ q ⟶
      relSingularHomology R X (A ∩ B)ᶜ q) :=
  biprod.desc
    (homolRestriction R X A (A ∩ B) q)
    (-(homolRestriction R X B (A ∩ B) q))


/-- The Mayer–Vietoris connecting morphism in relative singular homology of
the complements, `H_q(X, (A ∩ B)ᶜ) → H_{q-1}(X, (A ∪ B)ᶜ)`, witnessing the
long exact sequence under the Mayer–Vietoris hypothesis. -/
noncomputable def singularMV_connecting
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X)
    (hyp : MayerVietorisHypothesis X A B) (q : ℕ) :
    (relSingularHomology R X (A ∩ B)ᶜ q ⟶ relSingularHomology R X (A ∪ B)ᶜ (q - 1)) := by sorry


/-- Exactness at the sum `H_q(X, Aᶜ) ⊕ H_q(X, Bᶜ)` of the singular
Mayer–Vietoris sequence. -/
theorem singularMV_exact_sum
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X)
    (hyp : MayerVietorisHypothesis X A B) (q : ℕ) :
    Function.Exact
      (singularMV_unionToSum R X A B hyp q).hom
      (singularMV_sumToInter R X A B hyp q).hom := by sorry


/-- Exactness at the intersection `H_q(X, (A ∩ B)ᶜ)` of the singular
Mayer–Vietoris sequence. -/
theorem singularMV_exact_inter
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X)
    (hyp : MayerVietorisHypothesis X A B) (q : ℕ) :
    Function.Exact
      (singularMV_sumToInter R X A B hyp q).hom
      (singularMV_connecting R X A B hyp q).hom := by sorry


/-- Exactness at the union `H_{q-1}(X, (A ∪ B)ᶜ)` of the singular
Mayer–Vietoris sequence (after the connecting morphism). -/
theorem singularMV_exact_union
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X)
    (hyp : MayerVietorisHypothesis X A B) (q : ℕ) :
    Function.Exact
      (singularMV_connecting R X A B hyp q).hom
      (singularMV_unionToSum R X A B hyp (q - 1)).hom := by sorry

/-- The full singular Mayer–Vietoris sequence as a `SingularMVSequence`,
packaging the union-to-sum, sum-to-intersection, and connecting morphisms
together with the three exactness statements. -/
def singularMV_of_hyp
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X)
    (hyp : MayerVietorisHypothesis X A B) :
    SingularMVSequence R X A B :=
  { unionToSum := singularMV_unionToSum R X A B hyp
    sumToInter := singularMV_sumToInter R X A B hyp
    connecting := singularMV_connecting R X A B hyp
    exact_sum := singularMV_exact_sum R X A B hyp
    exact_inter := singularMV_exact_inter R X A B hyp
    exact_union := singularMV_exact_union R X A B hyp }

/-- The Alexander–Whitney cap product short-complex map at the level of
relative singular chains on a neighbourhood `U` of `S`, modulo the chains on
the complement `Sᶜ`, parametrized by a Čech class `α`. -/
noncomputable def awCapAbsShortComplexMapS
    (R : Type) [CommRing R] (X : TopCat.{0}) (S : Set X)
    (U : CechCohomology.OpenNeighborhoods S) (p q : ℕ)
    (α : CechCohomology.cechFamily R S p U) :
    (relSingChainCx R (TopCat.of ↑U.1.1) (Subtype.val ⁻¹' Sᶜ)).sc (p + q) ⟶
    (relSingChainCx R (TopCat.of ↑U.1.1) (Subtype.val ⁻¹' Sᶜ)).sc q := by sorry

/-- Additivity of `awCapAbsShortComplexMapS` in the Čech class `α`. -/
theorem awCapAbsShortComplexMapS_add
    (R : Type) [CommRing R] (X : TopCat.{0}) (S : Set X)
    (U : CechCohomology.OpenNeighborhoods S) (p q : ℕ)
    (α₁ α₂ : CechCohomology.cechFamily R S p U) :
    awCapAbsShortComplexMapS R X S U p q (α₁ + α₂) =
      awCapAbsShortComplexMapS R X S U p q α₁ + awCapAbsShortComplexMapS R X S U p q α₂ := by sorry

/-- `R`-linearity of `awCapAbsShortComplexMapS` in the Čech class `α`. -/
theorem awCapAbsShortComplexMapS_smul
    (R : Type) [CommRing R] (X : TopCat.{0}) (S : Set X)
    (U : CechCohomology.OpenNeighborhoods S) (p q : ℕ)
    (r : R) (α : CechCohomology.cechFamily R S p U) :
    awCapAbsShortComplexMapS R X S U p q (r • α) =
      r • awCapAbsShortComplexMapS R X S U p q α := by sorry

/-- Passage of `awCapAbsShortComplexMapS` to relative singular homology of
the neighbourhood: gives an `R`-linear map
`H_{p+q}(U, Sᶜ ∩ U) → H_q(U, Sᶜ ∩ U)` parametrized by the Čech class. -/
def awCapDescendsToHomologyAbs
    (R : Type) [CommRing R] (X : TopCat.{0}) (S : Set X)
    (U : CechCohomology.OpenNeighborhoods S) (p q : ℕ)
    (α : CechCohomology.cechFamily R S p U) :
    (relSingularHomology R (TopCat.of ↑U.1.1)
      (Subtype.val ⁻¹' Sᶜ) (p + q) : Type _) →ₗ[R]
    (relSingularHomology R (TopCat.of ↑U.1.1)
      (Subtype.val ⁻¹' Sᶜ) q : Type _) :=
  (ShortComplex.homologyMap (awCapAbsShortComplexMapS R X S U p q α)).hom

/-- Additivity of `awCapDescendsToHomologyAbs` in the Čech class `α`. -/
theorem awCapDescendsToHomologyAbs_add
    (R : Type) [CommRing R] (X : TopCat.{0}) (S : Set X)
    (U : CechCohomology.OpenNeighborhoods S) (p q : ℕ)
    (α₁ α₂ : CechCohomology.cechFamily R S p U)
    (c : (relSingularHomology R (TopCat.of ↑U.1.1)
      (Subtype.val ⁻¹' Sᶜ) (p + q) : Type _)) :
    awCapDescendsToHomologyAbs R X S U p q (α₁ + α₂) c =
      awCapDescendsToHomologyAbs R X S U p q α₁ c +
      awCapDescendsToHomologyAbs R X S U p q α₂ c := by
  show (ShortComplex.homologyMap (awCapAbsShortComplexMapS R X S U p q (α₁ + α₂))).hom c =
    (ShortComplex.homologyMap (awCapAbsShortComplexMapS R X S U p q α₁)).hom c +
    (ShortComplex.homologyMap (awCapAbsShortComplexMapS R X S U p q α₂)).hom c
  rw [awCapAbsShortComplexMapS_add, ShortComplex.homologyMap_add]; rfl

/-- `R`-linearity of `awCapDescendsToHomologyAbs` in the Čech class `α`. -/
theorem awCapDescendsToHomologyAbs_smul
    (R : Type) [CommRing R] (X : TopCat.{0}) (S : Set X)
    (U : CechCohomology.OpenNeighborhoods S) (p q : ℕ)
    (r : R) (α : CechCohomology.cechFamily R S p U)
    (c : (relSingularHomology R (TopCat.of ↑U.1.1)
      (Subtype.val ⁻¹' Sᶜ) (p + q) : Type _)) :
    awCapDescendsToHomologyAbs R X S U p q (r • α) c =
      r • awCapDescendsToHomologyAbs R X S U p q α c := by
  show (ShortComplex.homologyMap (awCapAbsShortComplexMapS R X S U p q (r • α))).hom c =
    r • (ShortComplex.homologyMap (awCapAbsShortComplexMapS R X S U p q α)).hom c
  rw [awCapAbsShortComplexMapS_smul, ShortComplex.homologyMap_smul]; rfl


/-- The cap product on relative singular homology of a neighbourhood `U` of
`S`, packaged as an `R`-linear map from the Čech family to the space of
linear maps `H_{p+q}(U, Sᶜ ∩ U) → H_q(U, Sᶜ ∩ U)`. -/
def absCapOnNbhdHomol
    (R : Type) [CommRing R] (X : TopCat.{0}) (S : Set X)
    (U : CechCohomology.OpenNeighborhoods S) (p q : ℕ) :
    CechCohomology.cechFamily R S p U →ₗ[R]
      ((relSingularHomology R (TopCat.of ↑U.1.1)
        (Subtype.val ⁻¹' Sᶜ) (p + q) : Type _) →ₗ[R]
        (relSingularHomology R (TopCat.of ↑U.1.1)
          (Subtype.val ⁻¹' Sᶜ) q : Type _)) where
  toFun α := awCapDescendsToHomologyAbs R X S U p q α
  map_add' α₁ α₂ := LinearMap.ext fun c =>
    awCapDescendsToHomologyAbs_add R X S U p q α₁ α₂ c
  map_smul' r α := LinearMap.ext fun c =>
    awCapDescendsToHomologyAbs_smul R X S U p q r α c


/-- The map induced on relative singular homology by the inclusion of a
neighbourhood `U` of `S` into `X`: `H_q(U, Sᶜ ∩ U) → H_q(X, Sᶜ)`. -/
def inclusionForwardHomol
    (R : Type) [CommRing R] (X : TopCat.{0}) (S : Set X)
    (U : CechCohomology.OpenNeighborhoods S) (q : ℕ) :
    (relSingularHomology R (TopCat.of ↑U.1.1)
      (Subtype.val ⁻¹' Sᶜ) q : Type _) →ₗ[R]
      (relSingularHomology R X Sᶜ q : Type _) :=
  (excisionForwardHomol R X S U.1 q).hom


/-- The transition map on relative singular homology between two
neighbourhoods `U₁ ≤ U₂` of `S`, obtained as the composition of the
inclusion-induced map `U₂ → X` with the inverse of the excision isomorphism
for `U₁`. -/
def absNbhdHomologyInclusion
    (R : Type) [CommRing R] (X : TopCat.{0}) (S : Set X)
    (U₁ U₂ : CechCohomology.OpenNeighborhoods S) (_h : U₁ ≤ U₂) (n : ℕ) :
    (relSingularHomology R (TopCat.of ↑U₂.1.1)
      (Subtype.val ⁻¹' Sᶜ) n : Type _) →ₗ[R]
      (relSingularHomology R (TopCat.of ↑U₁.1.1)
        (Subtype.val ⁻¹' Sᶜ) n : Type _) := by
  classical
  exact (excisionInverseHomol R X S U₁.1 U₁.2 n).comp
    ((excisionForwardHomol R X S U₂.1 n).hom)


/-- Compatibility of the excision inverse isomorphisms across two
neighbourhoods `U₁ ≤ U₂`: factoring the inverse for `U₁` through `U₂` via
`absNbhdHomologyInclusion`. -/
theorem absNbhdExcisionInverseHomol_compatible
    (R : Type) [CommRing R] (X : TopCat.{0}) (S : Set X)
    (U₁ U₂ : CechCohomology.OpenNeighborhoods S) (h : U₁ ≤ U₂) (n : ℕ)
    (y : (relSingularHomology R X Sᶜ n : Type _)) :
    excisionInverseHomol R X S U₁.1 U₁.2 n y =
    absNbhdHomologyInclusion R X S U₁ U₂ h n
      (excisionInverseHomol R X S U₂.1 U₂.2 n y) := by
  classical
  simp only [absNbhdHomologyInclusion, LinearMap.comp_apply]
  congr 1
  simp only [excisionInverseHomol]
  haveI := excisionForwardHomol_isIso R X S U₂.1 U₂.2 n
  change y = (inv (excisionForwardHomol R X S U₂.1 n) ≫ excisionForwardHomol R X S U₂.1 n).hom y
  rw [IsIso.inv_hom_id]
  rfl


/-- Naturality of `absCapOnNbhdHomol` along the Čech transition maps and the
neighbourhood inclusion: needed to descend the cap product on neighbourhood
homology to the Čech direct limit. -/
theorem absCapOnNbhdHomol_naturality
    (R : Type) [CommRing R] (X : TopCat.{0}) (S : Set X)
    (U₁ U₂ : CechCohomology.OpenNeighborhoods S) (h : U₁ ≤ U₂)
    (p q : ℕ)
    (x : CechCohomology.cechFamily R S p U₁)
    (z : (relSingularHomology R (TopCat.of ↑U₂.1.1)
      (Subtype.val ⁻¹' Sᶜ) (p + q) : Type _)) :
    absNbhdHomologyInclusion R X S U₁ U₂ h q
      (absCapOnNbhdHomol R X S U₂ p q
        (CechCohomology.cechTransition R S p U₁ U₂ h x) z) =
    absCapOnNbhdHomol R X S U₁ p q x
      (absNbhdHomologyInclusion R X S U₁ U₂ h (p + q) z) := by sorry


/-- Compatibility of `inclusionForwardHomol` across two neighbourhoods
`U₁ ≤ U₂`: the inclusion-induced map for `U₂` factors through
`absNbhdHomologyInclusion` followed by the inclusion-induced map for `U₁`. -/
theorem absNbhdInclusionForwardHomol_compatible
    (R : Type) [CommRing R] (X : TopCat.{0}) (S : Set X)
    (U₁ U₂ : CechCohomology.OpenNeighborhoods S) (h : U₁ ≤ U₂) (q : ℕ)
    (w : (relSingularHomology R (TopCat.of ↑U₂.1.1)
      (Subtype.val ⁻¹' Sᶜ) q : Type _)) :
    inclusionForwardHomol R X S U₂ q w =
    inclusionForwardHomol R X S U₁ q
      (absNbhdHomologyInclusion R X S U₁ U₂ h q w) := by
  classical
  simp only [inclusionForwardHomol, absNbhdHomologyInclusion, LinearMap.comp_apply]
  simp only [excisionInverseHomol]
  haveI := excisionForwardHomol_isIso R X S U₁.1 U₁.2 q
  change (excisionForwardHomol R X S U₂.1 q).hom w =
    (excisionForwardHomol R X S U₁.1 q).hom
      ((inv (excisionForwardHomol R X S U₁.1 q)).hom
        ((excisionForwardHomol R X S U₂.1 q).hom w))
  conv_rhs => rw [show (inv (excisionForwardHomol R X S U₁.1 q)).hom
      ((excisionForwardHomol R X S U₂.1 q).hom w) =
    (excisionForwardHomol R X S U₂.1 q ≫ inv (excisionForwardHomol R X S U₁.1 q)).hom w
    from rfl]
  rw [show (excisionForwardHomol R X S U₁.1 q).hom
    ((excisionForwardHomol R X S U₂.1 q ≫ inv (excisionForwardHomol R X S U₁.1 q)).hom w) =
    (excisionForwardHomol R X S U₂.1 q ≫ inv (excisionForwardHomol R X S U₁.1 q) ≫
      excisionForwardHomol R X S U₁.1 q).hom w from rfl]
  simp only [IsIso.inv_hom_id, Category.comp_id]


/-- Naturality of the composite "inclusion-cap-excise" cap rung across two
neighbourhoods `U₁ ≤ U₂`, combining the three naturality lemmas above.
Used to descend the cap rung to the Čech direct limit. -/
theorem absNbhdCapRung_composite_naturality
    (R : Type) [CommRing R] (X : TopCat.{0}) (S : Set X)
    (p q : ℕ)
    (U₁ U₂ : CechCohomology.OpenNeighborhoods S) (h : U₁ ≤ U₂)
    (x : CechCohomology.cechFamily R S p U₁)
    (y : (relSingularHomology R X Sᶜ (p + q) : Type _)) :
    inclusionForwardHomol R X S U₂ q
      (absCapOnNbhdHomol R X S U₂ p q
        (CechCohomology.cechTransition R S p U₁ U₂ h x)
        (excisionInverseHomol R X S U₂.1 U₂.2 (p + q) y)) =
    inclusionForwardHomol R X S U₁ q
      (absCapOnNbhdHomol R X S U₁ p q x
        (excisionInverseHomol R X S U₁.1 U₁.2 (p + q) y)) := by

  rw [absNbhdInclusionForwardHomol_compatible R X S U₁ U₂ h q]

  rw [absCapOnNbhdHomol_naturality R X S U₁ U₂ h p q x]

  rw [absNbhdExcisionInverseHomol_compatible R X S U₁ U₂ h (p + q) y]


/-- The neighbourhood-level cap product "rung" at a fixed class
`x_S ∈ H_n(X, Sᶜ)`: pulled back via excision to the neighbourhood `U`, capped
with a Čech `p`-cocycle, and pushed forward to `X`, yielding a linear map
`Ȟ-family(U, S, p) → H_q(X, Sᶜ)` (`p + q = n`). -/
def absNbhdCapRung
    (R : Type) [CommRing R] (X : TopCat.{0}) (S : Set X)
    (n p q : ℕ) (hpq : p + q = n)
    (x_S : relSingularHomology R X Sᶜ n)
    (U : CechCohomology.OpenNeighborhoods S) :
    CechCohomology.cechFamily R S p U →ₗ[R]
      (relSingularHomology R X Sᶜ q : Type _) := by
  subst hpq
  exact (inclusionForwardHomol R X S U q).comp
    (LinearMap.flip (absCapOnNbhdHomol R X S U p q)
      (excisionInverseHomol R X S U.1 U.2 (p + q) x_S))

/-- Compatibility of `absNbhdCapRung` with Čech transition maps across two
neighbourhoods `U₁ ≤ U₂`, used to descend the cap rung to the Čech direct
limit `Ȟ^p(S; R)`. -/
theorem absNbhdCapRung_compatible
    (R : Type) [CommRing R] (X : TopCat.{0}) (S : Set X)
    (n p q : ℕ) (hpq : p + q = n)
    (x_S : relSingularHomology R X Sᶜ n)
    (U₁ U₂ : CechCohomology.OpenNeighborhoods S) (h : U₁ ≤ U₂)
    (x : CechCohomology.cechFamily R S p U₁) :
    absNbhdCapRung R X S n p q hpq x_S U₂
      (CechCohomology.cechTransition R S p U₁ U₂ h x) =
    absNbhdCapRung R X S n p q hpq x_S U₁ x := by
  subst hpq
  exact absNbhdCapRung_composite_naturality R X S p q U₁ U₂ h x x_S

/-- The cap product "rung" `Ȟ^p(S; R) → H_q(X, Sᶜ; R)` at a fixed class
`x_S ∈ H_n(X, Sᶜ)`, obtained by descending the neighbourhood-level cap rung
`absNbhdCapRung` along the Čech direct limit (`p + q = n`). -/
def cechCapRung
    (R : Type) [CommRing R] (X : TopCat.{0}) (S : Set X)
    (n p q : ℕ) (hpq : p + q = n)
    (x_S : relSingularHomology R X Sᶜ n) :
    (cechCohomology R X S p ⟶ relSingularHomology R X Sᶜ q) := by
  classical
  exact ModuleCat.ofHom (Module.DirectLimit.lift R _
    (CechCohomology.cechFamily R S p)
    (fun U V h => CechCohomology.cechTransition R S p U V h)
    (fun U => absNbhdCapRung R X S n p q hpq x_S U)
    (fun U₁ U₂ h x => absNbhdCapRung_compatible R X S n p q hpq x_S U₁ U₂ h x))


/-- Naturality of `cechCapRung` along an inclusion `L ⊆ K` of closed
subsets: capping with the restricted class on `L` agrees with capping on `K`
and then restricting the resulting homology class. -/
theorem cechCapRung_naturality
    (R : Type) [CommRing R] (X : TopCat.{0}) (K L : Set X)
    (n p q : ℕ) (hpq : p + q = n)
    (x_K : relSingularHomology R X Kᶜ n) :
    cechCohomToSubspace R X K L p ≫
      cechCapRung R X L n p q hpq ((homolRestriction R X K L n).hom x_K) =
    cechCapRung R X K n p q hpq x_K ≫ homolRestriction R X K L q := by sorry


/-- Compatibility of `cechCapRung` with the Mayer–Vietoris connecting
morphisms: the Čech coboundary `Ȟ^p(A ∩ B) → Ȟ^{p+1}(A ∪ B)` followed by
capping with `x_{A ∪ B}` equals capping with `x_{A ∩ B}` followed by the
singular connecting morphism. -/
theorem cechCapRung_naturality_connecting
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X)
    (hyp : MayerVietorisHypothesis X A B)
    (n p q : ℕ) (hpq : p + q = n) (hpq' : (p + 1) + (q - 1) = n)
    (x_union : relSingularHomology R X (A ∪ B)ᶜ n) :
    cechMV_connecting R X A B hyp p ≫
      cechCapRung R X (A ∪ B) n (p + 1) (q - 1) hpq'
        ((homolRestriction R X (A ∪ B) (A ∪ B) n).hom x_union) =
    cechCapRung R X (A ∩ B) n p q hpq
      ((homolRestriction R X (A ∪ B) (A ∩ B) n).hom x_union) ≫
      singularMV_connecting R X A B hyp q := by sorry


/-- Compatibility of `cechCapRung` with the Mayer–Vietoris union-to-sum
maps: capping on `A ∪ B` followed by the singular union-to-sum map equals
the Čech union-to-sum map followed by separately capping on `A` and `B`. -/
theorem cechCapRung_naturality_unionToSum
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X)
    (hyp : MayerVietorisHypothesis X A B)
    (n p q : ℕ) (hpq : p + q = n)
    (x_union : relSingularHomology R X (A ∪ B)ᶜ n) :
    cechCapRung R X (A ∪ B) n p q hpq
      ((homolRestriction R X (A ∪ B) (A ∪ B) n).hom x_union) ≫
      singularMV_unionToSum R X A B hyp q =
    cechMV_unionToSum R X A B p ≫
      Limits.biprod.map
        (cechCapRung R X A n p q hpq
          ((homolRestriction R X (A ∪ B) A n).hom x_union))
        (cechCapRung R X B n p q hpq
          ((homolRestriction R X (A ∪ B) B n).hom x_union)) := by sorry


/-- Compatibility of `cechCapRung` with the Mayer–Vietoris
sum-to-intersection maps: separately capping on `A`, `B` followed by the
singular sum-to-intersection map equals the Čech sum-to-intersection map
followed by capping on `A ∩ B`. -/
theorem cechCapRung_naturality_sumToInter
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X)
    (hyp : MayerVietorisHypothesis X A B)
    (n p q : ℕ) (hpq : p + q = n)
    (x_union : relSingularHomology R X (A ∪ B)ᶜ n) :
    Limits.biprod.map
      (cechCapRung R X A n p q hpq
        ((homolRestriction R X (A ∪ B) A n).hom x_union))
      (cechCapRung R X B n p q hpq
        ((homolRestriction R X (A ∪ B) B n).hom x_union)) ≫
      singularMV_sumToInter R X A B hyp q =
    cechMV_sumToInter R X A B p ≫
      cechCapRung R X (A ∩ B) n p q hpq
        ((homolRestriction R X (A ∪ B) (A ∩ B) n).hom x_union) := by sorry


/-- First commutative square of the Mayer–Vietoris cap-product ladder: cap
on `A ∪ B` followed by the singular union-to-sum equals the Čech
union-to-sum followed by the cap on `A` and `B`. Bundled form of
`cechCapRung_naturality_unionToSum`. -/
theorem mvCapProduct_comm_sq1
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X) (n : ℕ)
    (x_union : relSingularHomology R X (A ∪ B)ᶜ n)
    (hyp : MayerVietorisHypothesis X A B)
    (p q : ℕ) (hpq : p + q = n) :
    cechCapRung R X (A ∪ B) n p q hpq
      ((homolRestriction R X (A ∪ B) (A ∪ B) n).hom x_union) ≫
      (singularMV_of_hyp R X A B hyp).unionToSum q =
      (cechMV_of_hyp R X A B hyp).unionToSum p ≫
        Limits.biprod.map
          (cechCapRung R X A n p q hpq
            ((homolRestriction R X (A ∪ B) A n).hom x_union))
          (cechCapRung R X B n p q hpq
            ((homolRestriction R X (A ∪ B) B n).hom x_union)) := by
  simp only [singularMV_of_hyp, cechMV_of_hyp]
  exact cechCapRung_naturality_unionToSum R X A B hyp n p q hpq x_union

/-- Second commutative square of the Mayer–Vietoris cap-product ladder: cap
on `A` and `B` followed by the singular sum-to-intersection equals the Čech
sum-to-intersection followed by the cap on `A ∩ B`. Bundled form of
`cechCapRung_naturality_sumToInter`. -/
theorem mvCapProduct_comm_sq2
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X) (n : ℕ)
    (x_union : relSingularHomology R X (A ∪ B)ᶜ n)
    (hyp : MayerVietorisHypothesis X A B)
    (p q : ℕ) (hpq : p + q = n) :
    Limits.biprod.map
      (cechCapRung R X A n p q hpq
        ((homolRestriction R X (A ∪ B) A n).hom x_union))
      (cechCapRung R X B n p q hpq
        ((homolRestriction R X (A ∪ B) B n).hom x_union)) ≫
      (singularMV_of_hyp R X A B hyp).sumToInter q =
      (cechMV_of_hyp R X A B hyp).sumToInter p ≫
        cechCapRung R X (A ∩ B) n p q hpq
          ((homolRestriction R X (A ∪ B) (A ∩ B) n).hom x_union) := by
  simp only [singularMV_of_hyp, cechMV_of_hyp]
  exact cechCapRung_naturality_sumToInter R X A B hyp n p q hpq x_union

/-- Third commutative square of the Mayer–Vietoris cap-product ladder:
the Čech connecting morphism followed by capping on `A ∪ B` equals capping
on `A ∩ B` followed by the singular connecting morphism. Bundled form of
`cechCapRung_naturality_connecting`. -/
theorem mvCapProduct_comm_sq3
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X) (n : ℕ)
    (x_union : relSingularHomology R X (A ∪ B)ᶜ n)
    (hyp : MayerVietorisHypothesis X A B)
    (p q : ℕ) (hpq : p + q = n) (hpq' : (p + 1) + (q - 1) = n) :
    (cechMV_of_hyp R X A B hyp).connecting p ≫
      cechCapRung R X (A ∪ B) n (p + 1) (q - 1) hpq'
        ((homolRestriction R X (A ∪ B) (A ∪ B) n).hom x_union) =
      cechCapRung R X (A ∩ B) n p q hpq
        ((homolRestriction R X (A ∪ B) (A ∩ B) n).hom x_union) ≫
        (singularMV_of_hyp R X A B hyp).connecting q := by
  simp only [singularMV_of_hyp, cechMV_of_hyp]
  exact cechCapRung_naturality_connecting R X A B hyp n p q hpq hpq' x_union

/-- Assembles the `MVCapProductData` connecting the Čech and singular
Mayer–Vietoris sequences at a fixed class `x_union ∈ H_n(X, (A ∪ B)ᶜ)`: cap
rungs for each subset and the three compatibility squares. -/
def mvCapProduct_of_hyp
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X) (n : ℕ)
    (hyp : MayerVietorisHypothesis X A B)
    (x_union : relSingularHomology R X (A ∪ B)ᶜ n) :
    MVCapProductData R X A B n x_union
      (cechMV_of_hyp R X A B hyp) (singularMV_of_hyp R X A B hyp) where
  capRung p q S hpq :=
    cechCapRung R X S n p q hpq
      ((homolRestriction R X (A ∪ B) S n).hom x_union)
  comm_sq1 p q hpq := mvCapProduct_comm_sq1 R X A B n x_union hyp p q hpq
  comm_sq2 p q hpq := mvCapProduct_comm_sq2 R X A B n x_union hyp p q hpq
  comm_sq3 p q hpq hpq' := mvCapProduct_comm_sq3 R X A B n x_union hyp p q hpq hpq'

/-- **Theorem 36.2.** Let `A, B` be closed in a normal space or compact in a
Hausdorff space `X`. Then for any class `x_{A ∪ B} ∈ H_n(X, X - (A ∪ B))`
there is a commutative ladder of Mayer–Vietoris sequences connecting the
Čech cohomology Mayer–Vietoris sequence of `A, B, A ∪ B, A ∩ B` to the
singular homology Mayer–Vietoris sequence of their complements, in which the
classes `x_A, x_B, x_{A ∩ B}` arise as restrictions of `x_{A ∪ B}` and the
cap-product rungs are indexed by subsets `S ∈ {A, B, A ∪ B, A ∩ B}` and
`(p, q)` with `p + q = n`. Packaged as a `MayerVietorisLadder`. -/
noncomputable def cechSingular_mayerVietoris_ladder
    (R : Type) [CommRing R]
    (X : TopCat.{0})
    (A B : Set X)
    (n : ℕ)
    (hyp : MayerVietorisHypothesis X A B)
    (x_union : relSingularHomology R X (A ∪ B)ᶜ n) :
    MayerVietorisLadder R X A B n x_union :=
  let cechMV := cechMV_of_hyp R X A B hyp
  let singMV := singularMV_of_hyp R X A B hyp
  let capData := mvCapProduct_of_hyp R X A B n hyp x_union
  { topUnionToSum := cechMV.unionToSum
    topSumToInter := cechMV.sumToInter
    topConnecting := cechMV.connecting
    botUnionToSum := singMV.unionToSum
    botSumToInter := singMV.sumToInter
    botConnecting := singMV.connecting
    capRung := capData.capRung
    top_exact_sum := cechMV.exact_sum
    top_exact_inter := cechMV.exact_inter
    top_exact_union := cechMV.exact_union
    bot_exact_sum := singMV.exact_sum
    bot_exact_inter := singMV.exact_inter
    bot_exact_union := singMV.exact_union
    comm_sq1 := capData.comm_sq1
    comm_sq2 := capData.comm_sq2
    comm_sq3 := capData.comm_sq3 }
