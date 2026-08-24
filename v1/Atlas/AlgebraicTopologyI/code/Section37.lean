/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Topology.Compactness.Compact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Comma.Final
import Mathlib.Topology.Separation.Hausdorff
import Atlas.AlgebraicTopologyI.code.Section34

open CategoryTheory

noncomputable section

namespace PoincareDuality

variable (R : Type) [CommRing R]

/-- Relative singular cohomology $H^p(X, A; R)$ of a pair $(X, A)$ with coefficients in
$R$, as an object of `ModuleCat.{0} R`. -/
noncomputable def relativeSingularCohomology
    (X : Type) [TopologicalSpace X] (A : Set X) (p : ℕ) : ModuleCat.{0} R := by sorry


/-- Relative singular homology $H_q(X, A; R)$ of a pair $(X, A)$ with coefficients in
$R$, as an object of `ModuleCat.{0} R`. -/
noncomputable def relativeSingularHomology
    (X : Type) [TopologicalSpace X] (A : Set X) (q : ℕ) : ModuleCat.{0} R := by sorry


/-- Functoriality of relative singular homology: a continuous map of pairs
$f : (X, A) \to (Y, B)$ (i.e. $f$ with $f(A) \subseteq B$) induces
$f_* : H_q(X, A; R) \to H_q(Y, B; R)$. -/
noncomputable def relativeSingularHomology_map
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : f '' A ⊆ B) (q : ℕ) :
    relativeSingularHomology R X A q ⟶ relativeSingularHomology R Y B q := by sorry


/-- The map induced by the identity $\mathrm{id}_X$ on relative singular homology is the
identity morphism. -/
theorem relativeSingularHomology_map_id
    {X : Type} [TopologicalSpace X] (A : Set X) (q : ℕ)
    (h : (ContinuousMap.id X) '' A ⊆ A) :
    relativeSingularHomology_map R (ContinuousMap.id X) A A h q = 𝟙 _ := by sorry


/-- The functor on pairs preserves composition: $(g \circ f)_* = g_* \circ f_*$ on
relative singular homology. -/
theorem relativeSingularHomology_map_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z))
    (A : Set X) (B : Set Y) (D : Set Z)
    (hf : f '' A ⊆ B) (hg : g '' B ⊆ D)
    (hgf : (g.comp f) '' A ⊆ D) (q : ℕ) :
    relativeSingularHomology_map R f A B hf q ≫
    relativeSingularHomology_map R g B D hg q =
    relativeSingularHomology_map R (g.comp f) A D hgf q := by sorry


/-- If two maps of pairs $f, g : (X, A) \to (Y, B)$ are equal as continuous maps, the
induced maps on relative singular homology agree. -/
theorem relativeSingularHomology_map_congr
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f g : C(X, Y)) (hfg : f = g) (A : Set X) (B : Set Y)
    (hf : f '' A ⊆ B) (hg : g '' A ⊆ B) (q : ℕ) :
    relativeSingularHomology_map R f A B hf q =
    relativeSingularHomology_map R g A B hg q := by sorry


/-- An $n$-manifold $M$ is `IsROriented` if it admits an $R$-orientation, i.e. a coherent
choice of local-homology generators. This is the prerequisite for talking about a
fundamental class and hence Poincaré duality with coefficients in $R$. -/
class IsROriented (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] : Prop where
  isROrientable : OrientationHomology.IsROrientable n M R

/-- The restriction map $H_n(M; R) \to H_n(M, M - \{x\}; R)$ to the local homology at a
point $x$, induced by enlarging the relative subset from $\emptyset$ to $\{x\}^c$. -/
noncomputable def restrictToLocalHomology
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x : M) :
    relativeSingularHomology R M ∅ n ⟶ relativeSingularHomology R M ({x}ᶜ) n := by sorry


/-- The restriction $H_n(M, M-K; R) \to H_n(M, M-\{x\}; R)$ from the relative homology
along a compact subset $K$ to the local homology at a point $x \in K$. This is the map
used to detect whether a class in $H_n(M, M-K; R)$ is a fundamental class along $K$. -/
def restrictAlongToLocalHomology
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (K : Set M) (x : M) (hx : x ∈ K) :
    relativeSingularHomology R M Kᶜ n ⟶ relativeSingularHomology R M ({x}ᶜ) n :=
  relativeSingularHomology_map R (ContinuousMap.id M) Kᶜ ({x}ᶜ)
    (by simp only [ContinuousMap.coe_id, Set.image_id]
        exact Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)) n


/-- The predicate "$\mu$ generates the local homology at $x$": the $R$-submodule spanned
by $\mu \in H_n(M, M-\{x\}; R)$ is the whole module. An $R$-orientation along $K$ is
characterised by producing local generators at every $x \in K$. -/
def isLocalHomologyGenerator
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (x : M) (μ : (relativeSingularHomology R M ({x}ᶜ) n : Type)) : Prop :=
  Submodule.span R {μ} = ⊤

/-- Identification of the relative-homology module used in the Section 34 orientation
machinery with the relative singular homology used here. Glue isomorphism that lets us
transport fundamental-class results across the two presentations. -/
noncomputable def homologyBridgeToSection37
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (A : Set M) :
    OrientationHomology.relativeHomologyModule R n M A ≅ relativeSingularHomology R M A n := by sorry


/-- Compatibility of the bridge `homologyBridgeToSection37` with restriction to local
homology: restricting first and then bridging equals bridging first and then restricting. -/
theorem homologyBridge_restriction_comm
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x : M)
    (α : ↥(OrientationHomology.relativeHomologyModule R n M ∅)) :
    (restrictToLocalHomology R n M x).hom ((homologyBridgeToSection37 R n M ∅).hom α) =
    (homologyBridgeToSection37 R n M ({x}ᶜ)).hom
      ((OrientationHomology.restrictionHomologyMap R n M ∅ {x}ᶜ (Set.empty_subset _)).hom α) := by sorry


/-- Existence of a fundamental class in the Section-34 form: for a compact oriented
$n$-manifold $M$, there exists $\alpha \in H_n(M, \emptyset; R)$ whose restriction to
each local homology $H_n(M, M-\{x\}; R)$ is a generator. -/
theorem fundamentalClass_in_relativeHomology
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (h : OrientationHomology.IsROrientable n M R) :
    ∃ (α : ↥(OrientationHomology.relativeHomologyModule R n M ∅)),
      ∀ (x : M), Submodule.span R
        {(OrientationHomology.restrictionHomologyMap R n M ∅ {x}ᶜ
          (Set.empty_subset _)).hom α} = ⊤ := by sorry


/-- Existence of a fundamental class $\mu \in H_n(M; R)$ in the present
`relativeSingularHomology` formulation: each local-homology restriction
$(\restrictToLocalHomology)(\mu)$ generates $H_n(M, M-\{x\}; R)$ for every $x$. -/
theorem fundamentalClass_of_isROrientable
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (h : OrientationHomology.IsROrientable n M R) :
    ∃ (μ : (relativeSingularHomology R M ∅ n : Type)),
      ∀ (x : M), isLocalHomologyGenerator R n M x
        ((restrictToLocalHomology R n M x).hom μ) := by

  obtain ⟨α, hα⟩ := fundamentalClass_in_relativeHomology R n M h

  let μ : ↥(relativeSingularHomology R M ∅ n) := (homologyBridgeToSection37 R n M ∅).hom α
  refine ⟨μ, fun x => ?_⟩

  unfold isLocalHomologyGenerator


  have hcomm := homologyBridge_restriction_comm R n M x α


  rw [show (restrictToLocalHomology R n M x).hom μ =
    (homologyBridgeToSection37 R n M ({x}ᶜ)).hom
      ((OrientationHomology.restrictionHomologyMap R n M ∅ {x}ᶜ
        (Set.empty_subset _)).hom α) from hcomm]


  set β := (OrientationHomology.restrictionHomologyMap R n M ∅ {x}ᶜ
    (Set.empty_subset _)).hom α
  have hgen : Submodule.span R {β} = ⊤ := hα x


  have hsurj : Function.Surjective (homologyBridgeToSection37 R n M ({x}ᶜ)).hom := by
    intro y
    exact ⟨(homologyBridgeToSection37 R n M ({x}ᶜ)).inv y, by
      simp⟩

  rw [eq_top_iff] at hgen ⊢
  intro y _
  obtain ⟨z, hz⟩ := hsurj y
  rw [← hz]
  have hz_mem : z ∈ Submodule.span R {β} := hgen (Submodule.mem_top)
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hz_mem
  rw [← hr, map_smul]
  exact Submodule.mem_span_singleton.mpr ⟨r, rfl⟩


/-- Uniqueness of the fundamental class: any two classes whose local-homology restrictions
are simultaneously generators at every point of a compact connected oriented manifold
coincide. -/
theorem fundamentalClass_unique
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (μ₁ μ₂ : (relativeSingularHomology R M ∅ n : Type))
    (h₁ : ∀ (x : M), isLocalHomologyGenerator R n M x
        ((restrictToLocalHomology R n M x).hom μ₁))
    (h₂ : ∀ (x : M), isLocalHomologyGenerator R n M x
        ((restrictToLocalHomology R n M x).hom μ₂)) :
    μ₁ = μ₂ := by sorry


/-- Čech cohomology $\check H^p(X, K, L; R)$ of a triple $(X, K, L)$ used to phrase the
fully relative Poincaré duality theorem. Defined as the colimit of relative singular
cohomologies $H^p(U, V; R)$ over open neighbourhoods $V \subseteq U$ of $L \subseteq K$. -/
noncomputable def cechCohomology
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) : ModuleCat.{0} R := by sorry


/-- Restriction map $\check H^p(M, M, L; R) \to H^p(M; R)$ from Čech cohomology of the
triple $(M, M, L)$ to absolute singular cohomology. -/
noncomputable def cohomRestriction
    (M : Type) [TopologicalSpace M] (L : Set M) (p : ℕ) :
    cechCohomology R M Set.univ L p ⟶ relativeSingularCohomology R M ∅ p := by sorry


/-- Restriction-to-subspace map $H^p(M; R) \to \check H^p(M, L; R)$ used in the
Mayer-Vietoris-like long exact sequence underlying Poincaré duality. -/
noncomputable def cohomToSubspace
    (M : Type) [TopologicalSpace M] (L : Set M) (p : ℕ) :
    relativeSingularCohomology R M ∅ p ⟶ cechCohomology R M L ∅ p := by sorry


/-- Coboundary/connecting map $\check H^p(M, L; R) \to \check H^{p+1}(M, M, L; R)$ in the
long exact sequence of the triple $(M, M, L)$. -/
noncomputable def cohomCoboundary
    (M : Type) [TopologicalSpace M] (L : Set M) (p : ℕ) :
    cechCohomology R M L ∅ p ⟶ cechCohomology R M Set.univ L (p + 1) := by sorry


/-- Inclusion-induced map $H_q(L^c; R) \to H_q(M; R)$, where the open complement $L^c$ is
viewed as a topological subspace. -/
noncomputable def homolFromOpen
    (M : Type) [TopologicalSpace M] (L : Set M) (q : ℕ) :
    relativeSingularHomology R (↥Lᶜ) ∅ q ⟶ relativeSingularHomology R M ∅ q := by sorry


/-- Pair-restriction map $H_q(M; R) \to H_q(M, L^c; R)$ enlarging the relative subset
from $\emptyset$ to $L^c$. -/
noncomputable def homolToRelative
    (M : Type) [TopologicalSpace M] (L : Set M) (q : ℕ) :
    relativeSingularHomology R M ∅ q ⟶ relativeSingularHomology R M Lᶜ q := by sorry


/-- Connecting homomorphism $H_{q+1}(M, L^c; R) \to H_q(L^c; R)$ of the long exact sequence
of the pair $(M, L^c)$. -/
noncomputable def homolBoundary
    (M : Type) [TopologicalSpace M] (L : Set M) (q : ℕ) :
    relativeSingularHomology R M Lᶜ (q + 1) ⟶ relativeSingularHomology R (↥Lᶜ) ∅ q := by sorry


/-- $M$ is $R$-oriented along $K$ if there is a class
$\mu \in H_n(M, M-K; R)$ whose local restriction at every $x \in K$ is a generator. This is
the data needed for cap-product Poincaré duality along $K$. -/
class IsROrientedAlong (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (K : Set M) : Prop where
  hasFundamentalClassAlong :
    ∃ (μ : (relativeSingularHomology R M Kᶜ n : Type)),
      ∀ (x : M) (hx : x ∈ K), isLocalHomologyGenerator R n M x
        ((restrictAlongToLocalHomology R n M K x hx).hom μ)

/-- Compatibility lemma: the restriction $\restrictAlongToLocalHomology$ at $K = M$ equals
the absolute restriction-to-local-homology (after the canonical identification
$M - M = \emptyset$). -/
theorem restrictAlongToLocalHomology_univ_eq
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (x : M) (hx : x ∈ (Set.univ : Set M)) :
    restrictAlongToLocalHomology R n M Set.univ x hx =
      eqToHom (by rw [Set.compl_univ]) ≫ restrictToLocalHomology R n M x := by sorry

/-- An $R$-oriented compact manifold is $R$-oriented along $M$ (the entire space), with
fundamental class transported via the identification $H_n(M, M^c; R) = H_n(M; R)$. -/
theorem isROrientedAlong_univ_of_isROriented
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M] :
    ∃ (μ : (relativeSingularHomology R M (Set.univᶜ) n : Type)),
      ∀ (x : M) (hx : x ∈ (Set.univ : Set M)),
        isLocalHomologyGenerator R n M x
          ((restrictAlongToLocalHomology R n M Set.univ x hx).hom μ) := by

  obtain ⟨μ, hμ⟩ := fundamentalClass_of_isROrientable R n M (IsROriented.isROrientable)

  refine ⟨Set.compl_univ ▸ μ, fun x hx => ?_⟩
  have h_compat := restrictAlongToLocalHomology_univ_eq R n M x hx
  simp only [h_compat, ModuleCat.hom_comp]
  simp only [LinearMap.comp_apply]

  have cancel : ∀ (S : Set M) (h : S = ∅) (ν : ↑(relativeSingularHomology R M ∅ n)),
      (eqToHom (show relativeSingularHomology R M S n = relativeSingularHomology R M ∅ n
        from by rw [h])).hom (h ▸ ν) = ν := by
    intro S h ν
    subst h
    rfl
  rw [cancel (Set.univᶜ) Set.compl_univ μ]
  exact hμ x


/-- Instance: any compact $R$-oriented manifold is automatically $R$-oriented along
$M = \Set.univ$. -/
instance isROrientedAlong_univ
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M] :
    IsROrientedAlong R n M Set.univ where
  hasFundamentalClassAlong :=
    isROrientedAlong_univ_of_isROriented R n M

/-- Subset-monotonicity of the relative-singular-homology functor: an inclusion
$A \subseteq B$ induces the natural map $H_q(X, A; R) \to H_q(X, B; R)$. -/
def relativeSingularHomologyRestrict
    (X : Type) [TopologicalSpace X] (A B : Set X) (h : A ⊆ B) (q : ℕ) :
    ↑(relativeSingularHomology R X A q) →
    ↑(relativeSingularHomology R X B q) :=
  (relativeSingularHomology_map R (ContinuousMap.id X) A B
    (by simp only [ContinuousMap.coe_id, Set.image_id]; exact h) q).hom


/-- Compatibility of restriction-to-local-homology with the pair-restriction
$H_n(M, K^c; R) \to H_n(M, L^c; R)$ along $L \subseteq K$: restricting to local homology at
$x \in L$ commutes with the pair restriction, and equals the local restriction from $K$. -/
theorem restrictAlongToLocalHomology_comp_restrict
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K L : Set M) (hLK : L ⊆ K) (x : M) (hxL : x ∈ L)
    (μ : (relativeSingularHomology R M Kᶜ n : Type)) :
    (restrictAlongToLocalHomology R n M L x hxL).hom
      (relativeSingularHomologyRestrict R M Kᶜ Lᶜ (Set.compl_subset_compl.mpr hLK) n μ) =
    (restrictAlongToLocalHomology R n M K x (hLK hxL)).hom μ := by
  simp only [restrictAlongToLocalHomology, relativeSingularHomologyRestrict]
  change (relativeSingularHomology_map R (ContinuousMap.id M) Kᶜ Lᶜ _ n ≫
    relativeSingularHomology_map R (ContinuousMap.id M) Lᶜ {x}ᶜ _ n).hom μ =
    (relativeSingularHomology_map R (ContinuousMap.id M) Kᶜ {x}ᶜ _ n).hom μ
  have hcomp := relativeSingularHomology_map_comp R
    (ContinuousMap.id M) (ContinuousMap.id M)
    Kᶜ Lᶜ ({x}ᶜ)
    (by simp only [ContinuousMap.coe_id, Set.image_id]
        exact Set.compl_subset_compl.mpr hLK)
    (by simp only [ContinuousMap.coe_id, Set.image_id]
        exact Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hxL))
    (by simp only [ContinuousMap.comp_id, ContinuousMap.coe_id, Set.image_id]
        exact Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr (hLK hxL)))
    n
  have hcongr := relativeSingularHomology_map_congr R
    ((ContinuousMap.id M).comp (ContinuousMap.id M)) (ContinuousMap.id M)
    ((ContinuousMap.id M).comp_id) Kᶜ ({x}ᶜ)
    (by simp only [ContinuousMap.comp_id, ContinuousMap.coe_id, Set.image_id]
        exact Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr (hLK hxL)))
    (by simp only [ContinuousMap.coe_id, Set.image_id]
        exact Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr (hLK hxL)))
    n
  rw [hcomp, hcongr]


/-- $R$-orientability descends to subsets: if $M$ is $R$-oriented along $K$ and $L \subseteq
K$, then $M$ is $R$-oriented along $L$, via the pair-restriction of fundamental classes. -/
theorem isROrientedAlong_of_subset
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K L : Set M) (hLK : L ⊆ K) (hOr : IsROrientedAlong R n M K) :
    IsROrientedAlong R n M L where
  hasFundamentalClassAlong := by
    obtain ⟨μ, hμ⟩ := hOr.hasFundamentalClassAlong
    refine ⟨relativeSingularHomologyRestrict R M Kᶜ Lᶜ
      (Set.compl_subset_compl.mpr hLK) n μ, fun x hxL => ?_⟩
    rw [restrictAlongToLocalHomology_comp_restrict R n M K L hLK x hxL μ]
    exact hμ x (hLK hxL)


/-- **Step 1 of the absolute cap-product iso (Theorem 37.1).** For $K \subseteq \mathbb{R}^n$
compact and convex, the cap-product map $\check H^p(\mathbb{R}^n, K; R) \to H_q(\mathbb{R}^n,
\mathbb{R}^n - K; R)$ is an isomorphism for $p + q = n$, proved by direct computation using
contractibility of $K$. -/
noncomputable def capProductIso_step1_compactConvex
    (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hConv : Convex ℝ K)
    (hOr : IsROrientedAlong R n (EuclideanSpace ℝ (Fin n)) K)
    (p q : ℕ) (hpq : p + q = n) :
    cechCohomology R (EuclideanSpace ℝ (Fin n)) K ∅ p ≅
      relativeSingularHomology R (EuclideanSpace ℝ (Fin n)) Kᶜ q := by sorry


/-- **Step 2 of Theorem 37.1.** Extends Step 1 from compact convex sets to finite unions of
compact convex sets, via Mayer-Vietoris and the five lemma. -/
noncomputable def capProductIso_step2_finiteUnionConvex
    (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hFinConvex : ∃ (S : Finset (Set (EuclideanSpace ℝ (Fin n)))),
      (∀ C ∈ S, IsCompact C ∧ Convex ℝ C) ∧ K = ⋃₀ ↑S)
    (hOr : IsROrientedAlong R n (EuclideanSpace ℝ (Fin n)) K)
    (p q : ℕ) (hpq : p + q = n) :
    cechCohomology R (EuclideanSpace ℝ (Fin n)) K ∅ p ≅
      relativeSingularHomology R (EuclideanSpace ℝ (Fin n)) Kᶜ q := by sorry


/-- **Step 3 of Theorem 37.1.** Extends Step 2 to arbitrary compact subsets $K \subseteq
\mathbb{R}^n$ by writing $K$ as the decreasing intersection of finite unions of cubes (or
compact convex sets), and passing to the colimit. -/
noncomputable def capProductIso_step3_compactEuclidean
    (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hOr : IsROrientedAlong R n (EuclideanSpace ℝ (Fin n)) K)
    (p q : ℕ) (hpq : p + q = n) :
    cechCohomology R (EuclideanSpace ℝ (Fin n)) K ∅ p ≅
      relativeSingularHomology R (EuclideanSpace ℝ (Fin n)) Kᶜ q := by sorry


/-- **Step 4 of Theorem 37.1.** Generalises Step 3 from $\mathbb{R}^n$ to charted manifolds
$M$, for $K$ a finite union of compacts each lying in a single chart, via Mayer-Vietoris on
charts and the previous step. -/
noncomputable def capProductIso_step4_finiteUnionCharts
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K : Set M) (hK : IsCompact K)
    (hFinChart : ∃ (S : Finset (Set M)),
      (∀ C ∈ S, IsCompact C ∧ ∃ e ∈ atlas (EuclideanSpace ℝ (Fin n)) M, C ⊆ e.source) ∧
      K = ⋃₀ ↑S)
    (hOr : IsROrientedAlong R n M K)
    (p q : ℕ) (hpq : p + q = n) :
    cechCohomology R M K ∅ p ≅ relativeSingularHomology R M Kᶜ q := by sorry


/-- Geometric input for Step 5: every compact $K$ in a charted manifold is the decreasing
intersection of compacts $A_i$, each of which is a finite union of compacts contained in
single chart neighbourhoods. Allows passing from Step 4 to arbitrary compacts. -/
theorem compact_decreasingIntersection_finiteUnionCharts
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K : Set M) (hK : IsCompact K) :
    ∃ (A : ℕ → Set M),
      (∀ i, IsCompact (A i)) ∧
      (∀ i, A (i + 1) ⊆ A i) ∧
      (K = ⋂ i, A i) ∧
      (∀ i, ∃ (S : Finset (Set M)),
        (∀ C ∈ S, IsCompact C ∧ ∃ e ∈ atlas (EuclideanSpace ℝ (Fin n)) M, C ⊆ e.source) ∧
        A i = ⋃₀ ↑S) := by sorry

section CechCohomologyDecreasingCompact
open Limits TopologicalSpace

variable (R : Type) [CommRing R]

/-- Restriction map $\check H^p(M, K; R) \to \check H^p(M, K'; R)$ for $K' \subseteq K$,
realised on Čech cohomology by enlarging the open neighbourhood system from $K$ to $K'$. -/
noncomputable def cechCohomologyRestriction
    (M : Type) [TopologicalSpace M] (K K' : Set M) (_hKK' : K' ⊆ K) (p : ℕ) :
    cechCohomology R M K ∅ p ⟶ cechCohomology R M K' ∅ p := by sorry

/-- For a Hausdorff manifold and an antitone family $A_k$ of compacts with intersection
$A_\infty$, the restriction $\check H^p(M, A_k; R) \to \check H^p(M, A_\infty; R)$ is an
iso. The key colimit/continuity statement of Lemma 37.2. -/
theorem cechCohomologyRestriction_isIso_of_colimit
    {n : ℕ} (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (A : ℕ → Set M) (hA : Antitone A) (hcpt : ∀ k, IsCompact (A k))
    (p : ℕ) (k : ℕ) :
    IsIso (cechCohomologyRestriction R M (A k) (⋂ j, A j) (Set.iInter_subset A k) p) := by sorry

/-- Packaging form of `cechCohomologyRestriction_isIso_of_colimit`: the restriction map
itself equals the `hom`-component of an explicit isomorphism. -/
theorem cechCohomologyRestriction_eq_iso_hom
    {n : ℕ} (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (A : ℕ → Set M) (hA : Antitone A) (hcpt : ∀ k, IsCompact (A k))
    (p : ℕ) (k : ℕ) :
    ∃ (iso : cechCohomology R M (A k) ∅ p ≅ cechCohomology R M (⋂ j, A j) ∅ p),
      cechCohomologyRestriction R M (A k) (⋂ j, A j) (Set.iInter_subset A k) p = iso.hom := by
  haveI := cechCohomologyRestriction_isIso_of_colimit (n := n) R M A hA hcpt p k
  exact ⟨asIso (cechCohomologyRestriction R M (A k) (⋂ j, A j) (Set.iInter_subset A k) p), rfl⟩

/-- Convenient typeclass form of `cechCohomologyRestriction_isIso_of_colimit`. -/
theorem cechCohomologyRestriction_isIso
    {n : ℕ} (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (A : ℕ → Set M) (hA : Antitone A) (hcpt : ∀ k, IsCompact (A k))
    (p : ℕ) (k : ℕ) :
    IsIso (cechCohomologyRestriction R M (A k) (⋂ j, A j)
      (Set.iInter_subset A k) p) := by
  obtain ⟨iso, heq⟩ := cechCohomologyRestriction_eq_iso_hom (n := n) R M A hA hcpt p k
  rw [heq]
  infer_instance

/-- Iso form of the colimit statement (Lemma 37.2): for an antitone family of compacts $A_k$
with intersection $A_\infty$, the natural map
$\check H^p(M, A_k; R) \to \check H^p(M, A_\infty; R)$ is an iso for every $k$. -/
noncomputable def cechCohomology_decreasing_compact_iso
    {n : ℕ} (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (A : ℕ → Set M) (hA : Antitone A) (hcpt : ∀ k, IsCompact (A k))
    (p : ℕ) (k : ℕ) :
    cechCohomology R M (A k) ∅ p ≅ cechCohomology R M (⋂ j, A j) ∅ p := by
  haveI := cechCohomologyRestriction_isIso (n := n) R M A hA hcpt p k
  exact asIso (cechCohomologyRestriction R M (A k) (⋂ j, A j)
    (Set.iInter_subset A k) p)

end CechCohomologyDecreasingCompact


/-- Public-facing alias for `cechCohomology_decreasing_compact_iso`. -/
noncomputable def cechCohomology_decreasingCompact_iso
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (A : ℕ → Set M) (hA : Antitone A) (hcpt : ∀ k, IsCompact (A k))
    (p : ℕ) (k : ℕ) :
    cechCohomology R M (A k) ∅ p ≅ cechCohomology R M (⋂ j, A j) ∅ p :=
  cechCohomology_decreasing_compact_iso (n := n) R M A hA hcpt p k


/-- Homological analogue of the colimit statement: for an antitone family of compacts $A_k$
with intersection $A_\infty$, the pair-homology $H_q(M, A_\infty^c; R)$ is isomorphic to
$H_q(M, A_k^c; R)$ for every $k$. -/
noncomputable def relativeSingularHomology_colimit_decreasingCompact
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (A : ℕ → Set M) (hA : Antitone A) (hcpt : ∀ k, IsCompact (A k))
    (q : ℕ) (k : ℕ) :
    relativeSingularHomology R M (⋂ j, A j)ᶜ q ≅
      relativeSingularHomology R M (A k)ᶜ q := by sorry


/-- Upward extension: if $M$ is $R$-oriented along $K \subseteq K'$ and $K'$ is a finite
union of compacts each lying in a single chart, then $M$ is $R$-oriented along $K'$. Used
when bootstrapping orientability from arbitrary compacts to chart-finite-union compacts. -/
theorem isROrientedAlong_of_supset_finiteUnionCharts
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K K' : Set M) (hKK' : K ⊆ K') (hK' : IsCompact K')
    (hFinChart : ∃ (S : Finset (Set M)),
      (∀ C ∈ S, IsCompact C ∧ ∃ e ∈ atlas (EuclideanSpace ℝ (Fin n)) M, C ⊆ e.source) ∧
      K' = ⋃₀ ↑S)
    (hOr : IsROrientedAlong R n M K) :
    IsROrientedAlong R n M K' := by sorry


/-- **Step 5 of Theorem 37.1.** Final step: for arbitrary compact $K$ in a Hausdorff
charted manifold $M$, the cap-product map is an iso, obtained as a colimit of Step-4 isos
along an antitone family of finite-chart-union approximations to $K$. -/
noncomputable def capProductIso_step5_arbitraryCompact
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K : Set M) (hK : IsCompact K)
    (hOr : IsROrientedAlong R n M K)
    (p q : ℕ) (hpq : p + q = n) :
    cechCohomology R M K ∅ p ≅ relativeSingularHomology R M Kᶜ q := by

  have hex := compact_decreasingIntersection_finiteUnionCharts n M K hK
  let A := Classical.choose hex
  have hA_spec := Classical.choose_spec hex
  have hA_compact : ∀ i, IsCompact (A i) := hA_spec.1
  have hA_decreasing : ∀ i, A (i + 1) ⊆ A i := hA_spec.2.1
  have hK_eq : K = ⋂ i, A i := hA_spec.2.2.1
  have hA_finChart := hA_spec.2.2.2

  have hAntitone : Antitone A := antitone_nat_of_succ_le hA_decreasing


  have hK_inter : K = ⋂ j, A j := hK_eq
  have cech_iso : cechCohomology R M (A 0) ∅ p ≅ cechCohomology R M K ∅ p := by
    conv_rhs => rw [hK_inter]
    exact cechCohomology_decreasingCompact_iso R n M A hAntitone hA_compact p 0

  have homology_iso : relativeSingularHomology R M Kᶜ q ≅
      relativeSingularHomology R M (A 0)ᶜ q := by
    conv_lhs => rw [hK_inter]
    exact relativeSingularHomology_colimit_decreasingCompact R n M A hAntitone hA_compact q 0

  have hOr0 : IsROrientedAlong R n M (A 0) := by
    exact isROrientedAlong_of_supset_finiteUnionCharts R n M K (A 0)
      (hK_inter ▸ Set.iInter_subset A 0) (hA_compact 0) (hA_finChart 0) hOr

  have step4_iso : cechCohomology R M (A 0) ∅ p ≅ relativeSingularHomology R M (A 0)ᶜ q :=
    capProductIso_step4_finiteUnionCharts R n M (A 0) (hA_compact 0) (hA_finChart 0)
      hOr0 p q hpq

  exact cech_iso.symm.trans (step4_iso.trans homology_iso.symm)


/-- The cap-product map $\cap[\mu_K] : \check H^p(M, K; R) \to H_q(M, M-K; R)$ with the
fundamental class $\mu_K$ along $K$. Underlies the absolute Poincaré duality iso. -/
noncomputable def capProductWithFundamentalClass
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K : Set M) (hK : IsCompact K)
    (hOr : IsROrientedAlong R n M K)
    (p q : ℕ) (hpq : p + q = n) :
    cechCohomology R M K ∅ p ⟶ relativeSingularHomology R M Kᶜ q := by sorry

/-- The absolute cap-product iso, packaged: for compact $K \subseteq M$ along which $M$ is
$R$-oriented, $\check H^p(M, K; R) \cong H_q(M, M-K; R)$ for $p + q = n$. Wraps Step 5. -/
def absoluteCapProductIso
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K : Set M) (hK : IsCompact K)
    (hOr : IsROrientedAlong R n M K)
    (p q : ℕ) (hpq : p + q = n) :
    cechCohomology R M K ∅ p ≅ relativeSingularHomology R M Kᶜ q :=
  capProductIso_step5_arbitraryCompact R n M K hK hOr p q hpq

/-- The `hom` component of `absoluteCapProductIso` is, by construction, the cap-product map
$\cap[\mu_K]$. -/
theorem absoluteCapProductIso_hom_eq_capProduct
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K : Set M) (hK : IsCompact K)
    (hOr : IsROrientedAlong R n M K)
    (p q : ℕ) (hpq : p + q = n) :
    (absoluteCapProductIso R n M K hK hOr p q hpq).hom =
      capProductWithFundamentalClass R n M K hK hOr p q hpq := by sorry

/-- Five-lemma for `ModuleCat R`: given a ladder of two horizontal 4-term exact sequences
with `α` epi, `β`, `δ` iso, `ε` mono, the middle map `γ` is an iso. Specialisation of the
abelian-category five lemma. -/
theorem fiveLemma_moduleCat_isIso
    {A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : ModuleCat.{0} R}
    (f₁ : A₁ ⟶ A₂) (f₂ : A₂ ⟶ A₃) (f₃ : A₃ ⟶ A₄) (f₄ : A₄ ⟶ A₅)
    (g₁ : B₁ ⟶ B₂) (g₂ : B₂ ⟶ B₃) (g₃ : B₃ ⟶ B₄) (g₄ : B₄ ⟶ B₅)
    (α : A₁ ⟶ B₁) (β : A₂ ⟶ B₂) (γ : A₃ ⟶ B₃) (δ : A₄ ⟶ B₄) (ε : A₅ ⟶ B₅)
    (sq₁ : f₁ ≫ β = α ≫ g₁) (sq₂ : f₂ ≫ γ = β ≫ g₂)
    (sq₃ : f₃ ≫ δ = γ ≫ g₃) (sq₄ : f₄ ≫ ε = δ ≫ g₄)
    (hexTopExact : (ComposableArrows.mk₄ f₁ f₂ f₃ f₄).Exact)
    (hexBotExact : (ComposableArrows.mk₄ g₁ g₂ g₃ g₄).Exact)
    (hα : Epi α) (hβ : IsIso β) (hδ : IsIso δ) (hε : Mono ε) :
    IsIso γ :=
  Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hexTopExact hexBotExact
    (ComposableArrows.homMk₄ α β γ δ ε sq₁ sq₂ sq₃ sq₄) hα hβ hδ hε


/-- The "left tail" of the long exact sequence in Čech cohomology of the triple $(M, K, L)$:
the $(p-1)$-st term, used as the source of the connecting map $f_4$ and target of $f_1$. -/
noncomputable def cechCohomLES_left
    (M : Type) [TopologicalSpace M] (K L : Set M) (p : ℕ) :
    ModuleCat.{0} R := by sorry


/-- First map in the Čech-cohomology long exact sequence of the triple $(M, K, L)$:
the connecting map into $\check H^p(M, K; R)$. -/
noncomputable def cechCohomLES_f₁
    (M : Type) [TopologicalSpace M] (K L : Set M) (p : ℕ) :
    cechCohomLES_left R M K L p ⟶ cechCohomology R M K ∅ p := by sorry

/-- Second map in the Čech-cohomology long exact sequence of the triple: pair-extension
$\check H^p(M, K; R) \to \check H^p(M, K, L; R)$. -/
noncomputable def cechCohomLES_f₂
    (M : Type) [TopologicalSpace M] (K L : Set M) (p : ℕ) :
    cechCohomology R M K ∅ p ⟶ cechCohomology R M K L p := by sorry

/-- Third map in the Čech-cohomology long exact sequence of the triple: restriction
$\check H^p(M, K, L; R) \to \check H^p(M, L; R)$. -/
noncomputable def cechCohomLES_f₃
    (M : Type) [TopologicalSpace M] (K L : Set M) (p : ℕ) :
    cechCohomology R M K L p ⟶ cechCohomology R M L ∅ p := by sorry

/-- Fourth map (connecting/coboundary) in the Čech-cohomology long exact sequence of the
triple: $\check H^p(M, L; R) \to \check H^{p+1}_{\text{left}}(M, K, L; R)$. -/
noncomputable def cechCohomLES_f₄
    (M : Type) [TopologicalSpace M] (K L : Set M) (p : ℕ) :
    cechCohomology R M L ∅ p ⟶ cechCohomLES_left R M K L (p + 1) := by sorry


/-- "Right tail" of the singular-homology long exact sequence of the pair $(M, K, L)$:
provides the $(q-1)$-st target/source for the connecting maps $g_1$ and $g_4$. -/
noncomputable def singHomolLES_right
    (M : Type) [TopologicalSpace M] (K L : Set M) (q : ℕ) :
    ModuleCat.{0} R := by sorry


/-- First map in the singular-homology long exact sequence of the pair, going from the right
tail in degree $q + 1$ into $H_q(M, K^c; R)$. -/
noncomputable def singHomolLES_g₁
    (M : Type) [TopologicalSpace M] (K L : Set M) (q : ℕ) :
    singHomolLES_right R M K L (q + 1) ⟶ relativeSingularHomology R M Kᶜ q := by sorry

/-- Second map: $H_q(M, K^c; R) \to H_q(L^c, K^c \cap L^c; R)$, restriction along the open
inclusion $L^c \hookrightarrow M$. -/
noncomputable def singHomolLES_g₂
    (M : Type) [TopologicalSpace M] (K L : Set M) (q : ℕ) :
    relativeSingularHomology R M Kᶜ q ⟶
      relativeSingularHomology R (↥(Lᶜ)) (Subtype.val ⁻¹' Kᶜ) q := by sorry

/-- Third map: $H_q(L^c, K^c \cap L^c; R) \to H_q(M, L^c; R)$, the "next" pair-restriction
in the LES. -/
noncomputable def singHomolLES_g₃
    (M : Type) [TopologicalSpace M] (K L : Set M) (q : ℕ) :
    relativeSingularHomology R (↥(Lᶜ)) (Subtype.val ⁻¹' Kᶜ) q ⟶
      relativeSingularHomology R M Lᶜ q := by sorry

/-- Fourth map (connecting): $H_q(M, L^c; R) \to \text{right tail at }q$. -/
noncomputable def singHomolLES_g₄
    (M : Type) [TopologicalSpace M] (K L : Set M) (q : ℕ) :
    relativeSingularHomology R M Lᶜ q ⟶ singHomolLES_right R M K L q := by sorry

/-- Cap product with a specific class $\mu_K \in H_n(M, K^c; R)$, going
$\check H^p(M, K, L; R) \to H_q(L^c, K^c \cap L^c; R)$. -/
noncomputable def capProductWithClass
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K L : Set M) (p q : ℕ) (hpq : p + q = n)
    (μ_K : (relativeSingularHomology R M Kᶜ n : Type)) :
    cechCohomology R M K L p ⟶
      relativeSingularHomology R (↥(Lᶜ)) (Subtype.val ⁻¹' Kᶜ) q := by sorry

/-- The relative-pair cap-product, specialised to a chosen fundamental class along $K$
witnessed by `IsROrientedAlong R n M K`. This is the middle map $\gamma$ of the five-lemma
ladder. -/
def capProductRelativePair
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K L : Set M) [IsROrientedAlong R n M K]
    (p q : ℕ) (hpq : p + q = n) :
    cechCohomology R M K L p ⟶
      relativeSingularHomology R (↥(Lᶜ)) (Subtype.val ⁻¹' Kᶜ) q :=
  capProductWithClass R n M K L p q hpq
    (IsROrientedAlong.hasFundamentalClassAlong (R := R) (n := n) (M := M) (K := K)).choose


/-- The cap-product map at the leftmost position of the five-lemma ladder used to deduce
the fully-relative iso (Theorem 37.1) from the absolute one. -/
noncomputable def capProductLES_α
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K L : Set M) [IsROrientedAlong R n M K]
    (p q : ℕ) (hpq : p + q = n) :
    cechCohomLES_left R M K L p ⟶ singHomolLES_right R M K L (q + 1) := by sorry

/-- The cap-product map at the rightmost position of the five-lemma ladder for fully relative
Poincaré duality. -/
noncomputable def capProductLES_ε
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K L : Set M) [IsROrientedAlong R n M K]
    (p q : ℕ) (hpq : p + q = n) :
    cechCohomLES_left R M K L (p + 1) ⟶ singHomolLES_right R M K L q := by sorry


/-- Successive maps $f_1, f_2$ of the Čech-cohomology LES compose to zero. -/
theorem cechCohomLES_comp_f₁_f₂
    (M : Type) [TopologicalSpace M] (K L : Set M) (p : ℕ) :
    cechCohomLES_f₁ R M K L p ≫ cechCohomLES_f₂ R M K L p = 0 := by sorry

/-- Successive maps $f_2, f_3$ of the Čech-cohomology LES compose to zero. -/
theorem cechCohomLES_comp_f₂_f₃
    (M : Type) [TopologicalSpace M] (K L : Set M) (p : ℕ) :
    cechCohomLES_f₂ R M K L p ≫ cechCohomLES_f₃ R M K L p = 0 := by sorry

/-- Successive maps $f_3, f_4$ of the Čech-cohomology LES compose to zero. -/
theorem cechCohomLES_comp_f₃_f₄
    (M : Type) [TopologicalSpace M] (K L : Set M) (p : ℕ) :
    cechCohomLES_f₃ R M K L p ≫ cechCohomLES_f₄ R M K L p = 0 := by sorry


/-- Exactness at position 1 of the Čech-cohomology LES of the triple $(M, K, L)$. -/
theorem cechCohomLES_exact₁
    (M : Type) [TopologicalSpace M] (K L : Set M) (p : ℕ) :
    (CategoryTheory.ShortComplex.mk
      (cechCohomLES_f₁ R M K L p) (cechCohomLES_f₂ R M K L p)
      (cechCohomLES_comp_f₁_f₂ R M K L p)).Exact := by sorry

/-- Exactness at position 2 of the Čech-cohomology LES of the triple $(M, K, L)$. -/
theorem cechCohomLES_exact₂
    (M : Type) [TopologicalSpace M] (K L : Set M) (p : ℕ) :
    (CategoryTheory.ShortComplex.mk
      (cechCohomLES_f₂ R M K L p) (cechCohomLES_f₃ R M K L p)
      (cechCohomLES_comp_f₂_f₃ R M K L p)).Exact := by sorry

/-- Exactness at position 3 of the Čech-cohomology LES of the triple $(M, K, L)$. -/
theorem cechCohomLES_exact₃
    (M : Type) [TopologicalSpace M] (K L : Set M) (p : ℕ) :
    (CategoryTheory.ShortComplex.mk
      (cechCohomLES_f₃ R M K L p) (cechCohomLES_f₄ R M K L p)
      (cechCohomLES_comp_f₃_f₄ R M K L p)).Exact := by sorry

/-- Combined statement: the 4-term composable arrow $f_1 \to f_2 \to f_3 \to f_4$ is exact,
packaging the three positional exactness lemmas. -/
theorem cechCohomLES_exact
    (M : Type) [TopologicalSpace M] (K L : Set M) (p : ℕ) :
    (ComposableArrows.mk₄
      (cechCohomLES_f₁ R M K L p) (cechCohomLES_f₂ R M K L p)
      (cechCohomLES_f₃ R M K L p) (cechCohomLES_f₄ R M K L p)).Exact :=
  ComposableArrows.exact_of_δ₀
    (cechCohomLES_exact₁ R M K L p).exact_toComposableArrows
    (ComposableArrows.exact_of_δ₀
      (cechCohomLES_exact₂ R M K L p).exact_toComposableArrows
      (cechCohomLES_exact₃ R M K L p).exact_toComposableArrows)

/-- Exactness of the 4-term composable arrow $g_1 \to g_2 \to g_3 \to g_4$ in singular
homology, i.e. of the LES of the pair $(M, K, L)$. -/
theorem singHomolLES_exact
    (M : Type) [TopologicalSpace M] (K L : Set M) (q : ℕ) :
    (ComposableArrows.mk₄
      (singHomolLES_g₁ R M K L q) (singHomolLES_g₂ R M K L q)
      (singHomolLES_g₃ R M K L q) (singHomolLES_g₄ R M K L q)).Exact := by sorry

/-- Commutativity of square 1 in the five-lemma ladder for Theorem 37.1: cap-product with
the fundamental class intertwines the leftmost connecting maps of the Čech-cohomology and
singular-homology LESs. -/
theorem fiveLemmaLadder_sq₁
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K L : Set M) (hKL : L ⊆ K) (hK : IsCompact K) (hL : IsCompact L)
    [IsROrientedAlong R n M K]
    (p q : ℕ) (hpq : p + q = n)
    (isoK : cechCohomology R M K ∅ p ≅ relativeSingularHomology R M Kᶜ q) :
    cechCohomLES_f₁ R M K L p ≫ isoK.hom =
      capProductLES_α R n M K L p q hpq ≫ singHomolLES_g₁ R M K L q := by sorry

/-- Commutativity of square 2 in the five-lemma ladder for Theorem 37.1. -/
theorem fiveLemmaLadder_sq₂
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K L : Set M) (hKL : L ⊆ K) (hK : IsCompact K) (hL : IsCompact L)
    [IsROrientedAlong R n M K]
    (p q : ℕ) (hpq : p + q = n)
    (isoK : cechCohomology R M K ∅ p ≅ relativeSingularHomology R M Kᶜ q) :
    cechCohomLES_f₂ R M K L p ≫ capProductRelativePair R n M K L p q hpq =
      isoK.hom ≫ singHomolLES_g₂ R M K L q := by sorry

/-- Commutativity of square 3 in the five-lemma ladder for Theorem 37.1. -/
theorem fiveLemmaLadder_sq₃
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K L : Set M) (hKL : L ⊆ K) (hK : IsCompact K) (hL : IsCompact L)
    [IsROrientedAlong R n M K]
    (p q : ℕ) (hpq : p + q = n)
    (isoL : cechCohomology R M L ∅ p ≅ relativeSingularHomology R M Lᶜ q) :
    cechCohomLES_f₃ R M K L p ≫ isoL.hom =
      capProductRelativePair R n M K L p q hpq ≫ singHomolLES_g₃ R M K L q := by sorry

/-- Commutativity of square 4 in the five-lemma ladder for Theorem 37.1. -/
theorem fiveLemmaLadder_sq₄
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K L : Set M) (hKL : L ⊆ K) (hK : IsCompact K) (hL : IsCompact L)
    [IsROrientedAlong R n M K]
    (p q : ℕ) (hpq : p + q = n)
    (isoL : cechCohomology R M L ∅ p ≅ relativeSingularHomology R M Lᶜ q) :
    cechCohomLES_f₄ R M K L p ≫ capProductLES_ε R n M K L p q hpq =
      isoL.hom ≫ singHomolLES_g₄ R M K L q := by sorry

/-- Left-end leftmost cap-product map is epi. The hypothesis epi-ness needed to invoke the
five lemma on the cap-product ladder of Theorem 37.1. -/
theorem capProductLES_α_epi
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K L : Set M) (hKL : L ⊆ K) (hK : IsCompact K) (hL : IsCompact L)
    [IsROrientedAlong R n M K]
    (hOrL : IsROrientedAlong R n M L)
    (p q : ℕ) (hpq : p + q = n)
    (isoK : cechCohomology R M K ∅ p ≅ relativeSingularHomology R M Kᶜ q)
    (isoL : cechCohomology R M L ∅ p ≅ relativeSingularHomology R M Lᶜ q) :
    Epi (capProductLES_α R n M K L p q hpq) := by sorry

/-- Right-end cap-product map is mono. The mono-ness needed to invoke the five lemma on
the cap-product ladder of Theorem 37.1. -/
theorem capProductLES_ε_mono
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K L : Set M) (hKL : L ⊆ K) (hK : IsCompact K) (hL : IsCompact L)
    [IsROrientedAlong R n M K]
    (hOrL : IsROrientedAlong R n M L)
    (p q : ℕ) (hpq : p + q = n)
    (isoK : cechCohomology R M K ∅ p ≅ relativeSingularHomology R M Kᶜ q)
    (isoL : cechCohomology R M L ∅ p ≅ relativeSingularHomology R M Lᶜ q) :
    Mono (capProductLES_ε R n M K L p q hpq) := by sorry

/-- The five-lemma reduction: from absolute Poincaré duality isos at $K$ and $L$, deduce
the fully relative Poincaré duality iso at the pair $(K, L)$. The combinatorial core of
Theorem 37.1. -/
def fiveLemma_capProduct_reduction
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K L : Set M) (hKL : L ⊆ K) (hK : IsCompact K) (hL : IsCompact L)
    [hOrK : IsROrientedAlong R n M K]
    (hOrL : IsROrientedAlong R n M L)
    (p q : ℕ) (hpq : p + q = n)
    (isoK : cechCohomology R M K ∅ p ≅ relativeSingularHomology R M Kᶜ q)
    (isoL : cechCohomology R M L ∅ p ≅ relativeSingularHomology R M Lᶜ q) :
    cechCohomology R M K L p ≅ relativeSingularHomology R (↥(Lᶜ)) (Subtype.val ⁻¹' Kᶜ) q := by

  let γ := capProductRelativePair R n M K L p q hpq

  have hγ_isIso : IsIso γ := by
    exact fiveLemma_moduleCat_isIso R
      (cechCohomLES_f₁ R M K L p) (cechCohomLES_f₂ R M K L p)
      (cechCohomLES_f₃ R M K L p) (cechCohomLES_f₄ R M K L p)
      (singHomolLES_g₁ R M K L q) (singHomolLES_g₂ R M K L q)
      (singHomolLES_g₃ R M K L q) (singHomolLES_g₄ R M K L q)
      (capProductLES_α R n M K L p q hpq)
      isoK.hom γ isoL.hom
      (capProductLES_ε R n M K L p q hpq)
      (fiveLemmaLadder_sq₁ R n M K L hKL hK hL p q hpq isoK)
      (fiveLemmaLadder_sq₂ R n M K L hKL hK hL p q hpq isoK)
      (fiveLemmaLadder_sq₃ R n M K L hKL hK hL p q hpq isoL)
      (fiveLemmaLadder_sq₄ R n M K L hKL hK hL p q hpq isoL)
      (cechCohomLES_exact R M K L p)
      (singHomolLES_exact R M K L q)
      (capProductLES_α_epi R n M K L hKL hK hL hOrL p q hpq isoK isoL)
      isoK.isIso_hom isoL.isIso_hom
      (capProductLES_ε_mono R n M K L hKL hK hL hOrL p q hpq isoK isoL)
  exact asIso γ

/-- **Theorem 37.1 (Fully relative Poincaré duality, iso form).** For a Hausdorff charted
$n$-manifold $M$ and $L \subseteq K \subseteq M$ both compact with $M$ $R$-oriented along
$K$, there is a natural iso
$$\check H^p(M, K, L; R) \cong H_q(L^c, K^c \cap L^c; R)\qquad (p + q = n).$$ -/
def fullyRelativeCapProductIso
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K L : Set M) (hKL : L ⊆ K) (hK : IsCompact K) (hL : IsCompact L)
    [hOrK : IsROrientedAlong R n M K]
    (p q : ℕ) (hpq : p + q = n) :
    cechCohomology R M K L p ≅ relativeSingularHomology R (↥(Lᶜ)) (Subtype.val ⁻¹' Kᶜ) q :=

  let hOrL : IsROrientedAlong R n M L := isROrientedAlong_of_subset R n M K L hKL hOrK

  let isoK := absoluteCapProductIso R n M K hK hOrK p q hpq
  let isoL := absoluteCapProductIso R n M L hL hOrL p q hpq

  fiveLemma_capProduct_reduction R n M K L hKL hK hL hOrL p q hpq isoK isoL

/-- The fully relative cap-product morphism, i.e. the `hom` component of
`fullyRelativeCapProductIso`. -/
def fullyRelativeCapProduct
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K L : Set M) (hKL : L ⊆ K) (hK : IsCompact K) (hL : IsCompact L)
    [IsROrientedAlong R n M K]
    (p q : ℕ) (hpq : p + q = n) :
    cechCohomology R M K L p ⟶ relativeSingularHomology R (↥(Lᶜ)) (Subtype.val ⁻¹' Kᶜ) q :=
  (fullyRelativeCapProductIso R n M K L hKL hK hL p q hpq).hom

/-- The fully relative cap-product morphism is an iso, by virtue of being the `hom` of an
iso. -/
theorem fullyRelativeCapProduct_isIso
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K L : Set M) (hKL : L ⊆ K) (hK : IsCompact K) (hL : IsCompact L)
    [IsROrientedAlong R n M K]
    (p q : ℕ) (hpq : p + q = n) :
    IsIso (fullyRelativeCapProduct R n M K L hKL hK hL p q hpq) :=
  (fullyRelativeCapProductIso R n M K L hKL hK hL p q hpq).isIso_hom

/-- Compact Poincaré duality (absolute form): for compact $R$-oriented manifold along $K$,
$\check H^p(M, K; R) \cong H_q(M, M-K; R)$ for $p + q = n$. Alias for
`absoluteCapProductIso`. -/
def poincareDualityCompact
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K : Set M) (hK : IsCompact K) [hOr : IsROrientedAlong R n M K]
    (p q : ℕ) (hpq : p + q = n) :
    cechCohomology R M K ∅ p ≅ relativeSingularHomology R M Kᶜ q :=
  absoluteCapProductIso R n M K hK hOr p q hpq

/-- **Corollary 37.4.** The absolute cap-product iso is, in particular, an iso (so each
direction of Poincaré duality is realised by an actual morphism), packaged as a typeclass. -/
theorem corollary_37_4
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K : Set M) (hK : IsCompact K) [hOr : IsROrientedAlong R n M K]
    (p q : ℕ) (hpq : p + q = n) :
    IsIso (absoluteCapProductIso R n M K hK hOr p q hpq).hom :=
  (absoluteCapProductIso R n M K hK hOr p q hpq).isIso_hom

/-- Computational identity: when $K = M$ and $L = \emptyset$, the Čech-cohomology module
agrees with the absolute singular cohomology module. -/
theorem cechCohomology_univ_empty_eq
    (M : Type) [TopologicalSpace M] (p : ℕ) :
    cechCohomology R M Set.univ ∅ p = relativeSingularCohomology R M ∅ p := by sorry

/-- The canonical iso turning the equality `cechCohomology_univ_empty_eq` into a categorical
isomorphism. Used to phrase $H^p(M; R) \to \check H^p(M, M; R)$ as an iso. -/
def cohomAbsoluteToCech
    (M : Type) [TopologicalSpace M] (p : ℕ) :
    relativeSingularCohomology R M ∅ p ≅ cechCohomology R M Set.univ ∅ p :=
  eqToIso (cechCohomology_univ_empty_eq R M p).symm

/-- A homeomorphism $f : X \to Y$ of pairs (sending $A$ onto $B$) induces an isomorphism of
relative singular homology modules. -/
def relativeSingularHomology_isoOfHomeo
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X ≃ₜ Y) (A : Set X) (B : Set Y) (hAB : f '' A = B) (q : ℕ) :
    relativeSingularHomology R X A q ≅ relativeSingularHomology R Y B q := by
  have hfwd : (f : C(X, Y)) '' A ⊆ B := hAB ▸ le_refl _
  have hbwd : (f.symm : C(Y, X)) '' B ⊆ A := by
    rw [← hAB]; intro x hx; obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨a, ha, rfl⟩ := hy; simp; exact ha
  have hcomp1 : ((f.symm : C(Y, X)).comp (f : C(X, Y))) '' A ⊆ A := by
    intro x hx; obtain ⟨a, ha, rfl⟩ := hx; simp; exact ha
  have hcomp2 : ((f : C(X, Y)).comp (f.symm : C(Y, X))) '' B ⊆ B := by
    intro x hx; obtain ⟨b, hb, rfl⟩ := hx; simp; exact hb
  have hid_A : (ContinuousMap.id X) '' A ⊆ A := by simp
  have hid_B : (ContinuousMap.id Y) '' B ⊆ B := by simp
  exact Iso.mk
    (relativeSingularHomology_map R (f : C(X, Y)) A B hfwd q)
    (relativeSingularHomology_map R (f.symm : C(Y, X)) B A hbwd q)
    (by
      rw [relativeSingularHomology_map_comp R (f : C(X, Y)) (f.symm : C(Y, X))
        A B A hfwd hbwd hcomp1 q]
      rw [relativeSingularHomology_map_congr R _ (ContinuousMap.id X)
        (by ext x; simp) A A hcomp1 hid_A q]
      exact relativeSingularHomology_map_id R A q hid_A)
    (by
      rw [relativeSingularHomology_map_comp R (f.symm : C(Y, X)) (f : C(X, Y))
        B A B hbwd hfwd hcomp2 q]
      rw [relativeSingularHomology_map_congr R _ (ContinuousMap.id Y)
        (by ext x; simp) B B hcomp2 hid_B q]
      exact relativeSingularHomology_map_id R B q hid_B)

/-- Identification $H_q(M^c, M^c \cap \emptyset^c; R) \cong H_q(M; R)$ when $M = M^c$ via
the empty-complement convention. Glue iso used in `capFundamentalAbsolute`. -/
def homolSubtypeUnivToAbsolute
    (M : Type) [TopologicalSpace M] (q : ℕ) :
    relativeSingularHomology R (↥(∅ : Set M)ᶜ) (Subtype.val ⁻¹' (Set.univ : Set M)ᶜ) q ≅
    relativeSingularHomology R M ∅ q := by
  rw [show (∅ : Set M)ᶜ = Set.univ from Set.compl_empty]
  exact relativeSingularHomology_isoOfHomeo R (Homeomorph.Set.univ M)
    (Subtype.val ⁻¹' (Set.univ : Set M)ᶜ) ∅
    (by simp [Homeomorph.Set.univ, Set.compl_univ]) q

/-- The absolute cap-product $\cap [M] : H^p(M; R) \to H_q(M; R)$ on a compact $R$-oriented
manifold, defined as the composite of `cohomAbsoluteToCech`, `fullyRelativeCapProduct` at
$(K, L) = (M, \emptyset)$, and the homology bridge. -/
def capFundamentalAbsolute
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (p q : ℕ) (hpq : p + q = n) :
    relativeSingularCohomology R M ∅ p ⟶ relativeSingularHomology R M ∅ q :=
  (cohomAbsoluteToCech R M p).hom ≫
  fullyRelativeCapProduct R n M Set.univ ∅ (Set.empty_subset _)
    isCompact_univ isCompact_empty p q hpq ≫
  (homolSubtypeUnivToAbsolute R M q).hom

/-- The defining decomposition of `capFundamentalAbsolute`, made available as a rewrite
lemma for downstream proofs. -/
theorem capFundamentalAbsolute_eq_compose
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (p q : ℕ) (hpq : p + q = n) :
    capFundamentalAbsolute R n M p q hpq =
    (cohomAbsoluteToCech R M p).hom ≫
    fullyRelativeCapProduct R n M Set.univ ∅ (Set.empty_subset _)
      isCompact_univ isCompact_empty p q hpq ≫
    (homolSubtypeUnivToAbsolute R M q).hom :=
  rfl

/-- The "relative" cap-product $\cap [M] : \check H^p(M, M, L; R) \to H_q(L^c; R)$ for $L$
closed, packaged as a single morphism with the codomain $H_q(L^c; R) = H_q(L^c, \emptyset;
R)$. Top row of the Poincaré-duality ladder. -/
def capFundamental
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (L : Set M) (hL : IsClosed L) (p q : ℕ) (hpq : p + q = n) :
    cechCohomology R M Set.univ L p ⟶ relativeSingularHomology R (↥Lᶜ) ∅ q :=
  fullyRelativeCapProduct R n M Set.univ L (Set.subset_univ L)
    isCompact_univ hL.isCompact p q hpq ≫
  eqToHom (by simp [Set.compl_univ, Set.preimage_empty])

/-- The "subspace" cap-product $\cap [M] : \check H^p(M, L; R) \to H_q(M, L^c; R)$ for $L$
closed, the bottom row of the Poincaré-duality ladder. -/
def capFundamentalSubspace
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (L : Set M) (hL : IsClosed L) (p q : ℕ) (hpq : p + q = n) :
    cechCohomology R M L ∅ p ⟶ relativeSingularHomology R M Lᶜ q :=
  (absoluteCapProductIso R n M L hL.isCompact
    (isROrientedAlong_of_subset R n M Set.univ L (Set.subset_univ L)
      (isROrientedAlong_univ R n M)) p q hpq).hom

/-- Structure packaging the Poincaré-duality "ladder" for a closed subset $L \subseteq M$:
the three cap-products `capFundamental`, `capFundamentalAbsolute`, `capFundamentalSubspace`,
each an iso, fitting into commutative squares with the connecting maps (restriction, pair
inclusion, boundary) of the long exact sequence of the pair $(M, L)$. -/
structure PoincareDualityLadder
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]

    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (L : Set M) (hL : IsClosed L) where
  capRelative_isIso : ∀ (p q : ℕ) (hpq : p + q = n),
    IsIso (capFundamental R n M L hL p q hpq)
  capAbsolute_isIso : ∀ (p q : ℕ) (hpq : p + q = n),
    IsIso (capFundamentalAbsolute R n M p q hpq)
  capSubspace_isIso : ∀ (p q : ℕ) (hpq : p + q = n),
    IsIso (capFundamentalSubspace R n M L hL p q hpq)
  comm_restrict : ∀ (p q : ℕ) (hpq : p + q = n),
    capFundamental R n M L hL p q hpq ≫ homolFromOpen R M L q =
    cohomRestriction R M L p ≫ capFundamentalAbsolute R n M p q hpq
  comm_subspace : ∀ (p q : ℕ) (hpq : p + q = n),
    capFundamentalAbsolute R n M p q hpq ≫ homolToRelative R M L q =
    cohomToSubspace R M L p ≫ capFundamentalSubspace R n M L hL p q hpq
  comm_boundary : ∀ (p q : ℕ) (hpq : p + (q + 1) = n),
    capFundamentalSubspace R n M L hL p (q + 1) hpq ≫ homolBoundary R M L q =
    cohomCoboundary R M L p ≫ capFundamental R n M L hL (p + 1) q (by omega)

/-- The defining decomposition of `capFundamental` as the composite of
`fullyRelativeCapProduct` (at $(M, L)$) and a glue iso. -/
theorem capFundamental_eq_compose
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (L : Set M) (hL : IsClosed L) (p q : ℕ) (hpq : p + q = n) :
    capFundamental R n M L hL p q hpq =
    fullyRelativeCapProduct R n M Set.univ L (Set.subset_univ L)
      isCompact_univ hL.isCompact p q hpq ≫
    eqToHom (by simp [Set.compl_univ, Set.preimage_empty]) :=
  rfl

/-- The defining decomposition of `capFundamentalSubspace` as the `hom` of
`absoluteCapProductIso` at $K = L$. -/
theorem capFundamentalSubspace_eq_compose
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (L : Set M) (hL : IsClosed L) (p q : ℕ) (hpq : p + q = n) :
    capFundamentalSubspace R n M L hL p q hpq =
    (absoluteCapProductIso R n M L hL.isCompact
      (isROrientedAlong_of_subset R n M Set.univ L (Set.subset_univ L)
        (isROrientedAlong_univ R n M)) p q hpq).hom :=
  rfl

/-- Commutativity of the restriction square in the Poincaré-duality ladder:
$\cap [M]$ followed by `homolFromOpen` equals `cohomRestriction` followed by
`capFundamentalAbsolute`. -/
theorem comm_restrict_naturality
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (L : Set M) (hL : IsClosed L) (p q : ℕ) (hpq : p + q = n) :
    capFundamental R n M L hL p q hpq ≫ homolFromOpen R M L q =
    cohomRestriction R M L p ≫ capFundamentalAbsolute R n M p q hpq := by sorry


/-- Commutativity of the subspace square in the Poincaré-duality ladder. -/
theorem comm_subspace_naturality
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (L : Set M) (hL : IsClosed L) (p q : ℕ) (hpq : p + q = n) :
    capFundamentalAbsolute R n M p q hpq ≫ homolToRelative R M L q =
    cohomToSubspace R M L p ≫ capFundamentalSubspace R n M L hL p q hpq := by sorry


/-- Commutativity of the boundary/connecting square in the Poincaré-duality ladder. -/
theorem comm_boundary_naturality
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (L : Set M) (hL : IsClosed L) (p q : ℕ) (hpq : p + (q + 1) = n) :
    capFundamentalSubspace R n M L hL p (q + 1) hpq ≫ homolBoundary R M L q =
    cohomCoboundary R M L p ≫ capFundamental R n M L hL (p + 1) q (by omega) := by sorry


/-- `capFundamental` is an iso, deduced from Theorem 37.1 (`fullyRelativeCapProduct_isIso`). -/
theorem capRelative_isIso_of_thm_37_1
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (L : Set M) (hL : IsClosed L) (p q : ℕ) (hpq : p + q = n) :
    IsIso (capFundamental R n M L hL p q hpq) := by
  rw [capFundamental_eq_compose]
  haveI : IsIso (fullyRelativeCapProduct R n M Set.univ L (Set.subset_univ L)
    isCompact_univ hL.isCompact p q hpq) :=
    fullyRelativeCapProduct_isIso R n M Set.univ L (Set.subset_univ L)
      isCompact_univ hL.isCompact p q hpq
  infer_instance

/-- `capFundamentalAbsolute` is an iso, deduced from Theorem 37.1 at $(K, L) = (M,
\emptyset)$. -/
theorem capAbsolute_isIso_of_thm_37_1
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (p q : ℕ) (hpq : p + q = n) :
    IsIso (capFundamentalAbsolute R n M p q hpq) := by
  rw [capFundamentalAbsolute_eq_compose]
  haveI : IsIso (fullyRelativeCapProduct R n M Set.univ ∅ (Set.empty_subset _)
    isCompact_univ isCompact_empty p q hpq) :=
    fullyRelativeCapProduct_isIso R n M Set.univ ∅ (Set.empty_subset _)
      isCompact_univ isCompact_empty p q hpq
  infer_instance

/-- `capFundamentalSubspace` is an iso, deduced from `absoluteCapProductIso` at $K = L$. -/
theorem capSubspace_isIso_of_thm_37_1
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (L : Set M) (hL : IsClosed L) (p q : ℕ) (hpq : p + q = n) :
    IsIso (capFundamentalSubspace R n M L hL p q hpq) := by
  rw [capFundamentalSubspace_eq_compose]
  exact (absoluteCapProductIso R n M L hL.isCompact
    (isROrientedAlong_of_subset R n M Set.univ L (Set.subset_univ L)
      (isROrientedAlong_univ R n M)) p q hpq).isIso_hom

/-- Alias for `comm_restrict_naturality`, exposing it as the "restriction square commutes"
input to the Poincaré-duality ladder. -/
theorem comm_restrict_of_thm_37_1
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (L : Set M) (hL : IsClosed L) (p q : ℕ) (hpq : p + q = n) :
    capFundamental R n M L hL p q hpq ≫ homolFromOpen R M L q =
    cohomRestriction R M L p ≫ capFundamentalAbsolute R n M p q hpq :=
  comm_restrict_naturality R n M L hL p q hpq

/-- Alias for `comm_subspace_naturality`. -/
theorem comm_subspace_of_thm_37_1
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (L : Set M) (hL : IsClosed L) (p q : ℕ) (hpq : p + q = n) :
    capFundamentalAbsolute R n M p q hpq ≫ homolToRelative R M L q =
    cohomToSubspace R M L p ≫ capFundamentalSubspace R n M L hL p q hpq :=
  comm_subspace_naturality R n M L hL p q hpq

/-- Alias for `comm_boundary_naturality`. -/
theorem comm_boundary_of_thm_37_1
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (L : Set M) (hL : IsClosed L) (p q : ℕ) (hpq : p + (q + 1) = n) :
    capFundamentalSubspace R n M L hL p (q + 1) hpq ≫ homolBoundary R M L q =
    cohomCoboundary R M L p ≫ capFundamental R n M L hL (p + 1) q (by omega) :=
  comm_boundary_naturality R n M L hL p q hpq

/-- **Corollary 37.3.** For any closed $L \subseteq M$ in a compact $R$-oriented
$n$-manifold, the Poincaré-duality ladder exists: the three cap-products are isos and the
three connecting squares commute. -/
theorem corollary_37_3
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (L : Set M) (hL : IsClosed L) :
    PoincareDualityLadder R n M L hL :=
  { capRelative_isIso := capRelative_isIso_of_thm_37_1 R n M L hL
    capAbsolute_isIso := capAbsolute_isIso_of_thm_37_1 R n M
    capSubspace_isIso := capSubspace_isIso_of_thm_37_1 R n M L hL
    comm_restrict := comm_restrict_of_thm_37_1 R n M L hL
    comm_subspace := comm_subspace_of_thm_37_1 R n M L hL
    comm_boundary := comm_boundary_of_thm_37_1 R n M L hL }

/-- The absolute cap-product is an iso, extracted from the ladder at $L = \emptyset$. -/
theorem capFundamentalAbsolute_isIso
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (p q : ℕ) (hpq : p + q = n) :
    IsIso (capFundamentalAbsolute R n M p q hpq) :=
  (corollary_37_3 R n M (∅ : Set M) isClosed_empty).capAbsolute_isIso p q hpq

/-- The iso form of Corollary 37.3 for `capFundamental`: $\check H^p(M, M, L; R) \cong
H_q(L^c; R)$ as an explicit isomorphism. -/
def corollary_37_3_iso
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (L : Set M) (hL : IsClosed L) (p q : ℕ) (hpq : p + q = n) :
    cechCohomology R M Set.univ L p ≅ relativeSingularHomology R (↥Lᶜ) ∅ q :=
  (fullyRelativeCapProductIso R n M Set.univ L (Set.subset_univ L)
    isCompact_univ hL.isCompact p q hpq).trans <|
  eqToIso (by simp [Set.compl_univ, Set.preimage_empty])

/-- Alternative iso-form proof of `capFundamentalAbsolute_isIso`, by directly composing the
factors of `capFundamentalAbsolute_eq_compose`. -/
theorem capFundamentalAbsolute_isIso'
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (p q : ℕ) (hpq : p + q = n) :
    IsIso (capFundamentalAbsolute R n M p q hpq) := by
  rw [capFundamentalAbsolute_eq_compose]
  haveI : IsIso (fullyRelativeCapProduct R n M Set.univ ∅ (Set.empty_subset _)
    isCompact_univ isCompact_empty p q hpq) :=
    fullyRelativeCapProduct_isIso R n M Set.univ ∅ (Set.empty_subset _)
      isCompact_univ isCompact_empty p q hpq
  infer_instance

/-- **Poincaré duality (categorical form).** For a compact $R$-oriented $n$-manifold, the
absolute cap-product $\cap [M] : H^p(M; R) \to H_q(M; R)$ is an iso for $p + q = n$. -/
theorem poincare_duality
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (p q : ℕ) (hpq : p + q = n) :
    IsIso (capFundamentalAbsolute R n M p q hpq) :=
  capFundamentalAbsolute_isIso' R n M p q hpq

/-- The iso form of Poincaré duality: $H^p(M; R) \cong H_q(M; R)$ as a categorical
isomorphism in `ModuleCat R`. -/
def poincareDualityIso
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (p q : ℕ) (hpq : p + q = n) :
    relativeSingularCohomology R M ∅ p ≅ relativeSingularHomology R M ∅ q :=
  (cohomAbsoluteToCech R M p).trans <|
  (absoluteCapProductIso R n M Set.univ isCompact_univ
    (isROrientedAlong_univ R n M) p q hpq).trans <|
  eqToIso (by rw [Set.compl_univ])

/-- Variant of `poincareDualityIso` using the substitution $q = n - p$: $H^p(M; R) \cong
H_{n-p}(M; R)$ for $p \le n$. -/
def poincareDualityIso'
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (p : ℕ) (hp : p ≤ n) :
    relativeSingularCohomology R M ∅ p ≅ relativeSingularHomology R M ∅ (n - p) :=
  poincareDualityIso R n M p (n - p) (Nat.add_sub_cancel' hp)

/-- Numerical consequence of Poincaré duality: $\dim_R H^p(M; R) = \dim_R H_q(M; R)$ for
$p + q = n$, deduced from `poincareDualityIso`. -/
theorem poincareDuality_finrank_eq
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (p q : ℕ) (hpq : p + q = n) :
    Module.finrank R (↑(relativeSingularCohomology R M ∅ p) : Type) =
    Module.finrank R (↑(relativeSingularHomology R M ∅ q) : Type) :=
  (poincareDualityIso R n M p q hpq).toLinearEquiv.finrank_eq

/-- Over a field $F$, the universal-coefficient theorem yields a (non-canonical) iso
$H^p(X; F) \cong H_p(X; F)$, because Ext groups vanish over a field. -/
noncomputable def universalCoefficientFieldIso
    (F : Type) [Field F]
    (X : Type) [TopologicalSpace X] (p : ℕ) :
    relativeSingularCohomology F X ∅ p ≅ relativeSingularHomology F X ∅ p := by sorry


end PoincareDuality

end

open CategoryTheory TopologicalSpace Limits

namespace PoincareDuality

universe u

section OpenNhdsColimit

variable {α : Type u} [TopologicalSpace α]

/-- An open neighbourhood of a set $K$: an open subset $U \subseteq \alpha$ together with
the inclusion $K \subseteq U$. The indexing category for the Čech-cohomology colimit. -/
structure OpenNhdsOfSet (K : Set α) where
  toOpens : Opens α
  subset_carrier : K ⊆ toOpens.carrier

namespace OpenNhdsOfSet
variable {K : Set α}

/-- Reverse-inclusion preorder: $U \le V$ iff $V \subseteq U$, so that the system of
neighbourhoods is directed downward. -/
instance : Preorder (OpenNhdsOfSet K) where
  le U V := V.toOpens ≤ U.toOpens
  le_refl _ := le_refl _
  le_trans _ _ _ hab hbc := le_trans hbc hab

/-- $\alpha$ itself is always an open neighbourhood of $K$, so the type is nonempty. -/
instance : Nonempty (OpenNhdsOfSet K) := ⟨⟨⊤, Set.subset_univ K⟩⟩

/-- The preorder on open neighbourhoods is directed: any two neighbourhoods admit a common
refinement (their intersection). -/
instance : IsDirected (OpenNhdsOfSet K) (· ≤ ·) where
  directed U V :=
    ⟨⟨U.toOpens ⊓ V.toOpens,
      fun _ hx => ⟨U.subset_carrier hx, V.subset_carrier hx⟩⟩,
     (inf_le_left : U.toOpens ⊓ V.toOpens ≤ U.toOpens),
     (inf_le_right : U.toOpens ⊓ V.toOpens ≤ V.toOpens)⟩

/-- Forgetful functor `OpenNhdsOfSet K ⥤ (Opens α)ᵒᵖ` sending $U$ to its underlying open
set, contravariantly: the source for Čech-cohomology colimits over neighbourhoods of $K$. -/
def inclusionFunctorOp : OpenNhdsOfSet K ⥤ (Opens α)ᵒᵖ where
  obj U := Opposite.op U.toOpens
  map {_U _V} f := (homOfLE (leOfHom f)).op
  map_id _ := rfl
  map_comp _ _ := rfl

end OpenNhdsOfSet

/-- An "indexed" open neighbourhood: a pair $(k, U)$ where $U$ is an open neighbourhood of
$A_k$. Used to interpolate between the colimits along the family $\{A_k\}$ and the colimit
along their intersection, in the proof of Lemma 37.2. -/
structure CombinedOpenNhds (A : ℕ → Set α) where
  idx : ℕ
  nhd : OpenNhdsOfSet (A idx)

namespace CombinedOpenNhds
variable {A : ℕ → Set α}

/-- Reverse-inclusion preorder on `CombinedOpenNhds`: $(k, U) \le (k', V)$ iff
$V \subseteq U$, ignoring the indices. -/
instance : Preorder (CombinedOpenNhds A) where
  le p q := q.nhd.toOpens ≤ p.nhd.toOpens
  le_refl _ := le_refl _
  le_trans _ _ _ hab hbc := le_trans hbc hab

/-- The pair $(0, \top)$ is always a combined open neighbourhood, hence the type is
nonempty. -/
instance : Nonempty (CombinedOpenNhds A) := ⟨⟨0, ⟨⊤, Set.subset_univ _⟩⟩⟩

/-- For an antitone (decreasing) family of subsets $A_k$, the preorder on combined
neighbourhoods is directed: take a common refinement index and intersect the neighbourhoods. -/
@[reducible]
def isDirectedOfAntitone (hA : Antitone A) :
    IsDirected (CombinedOpenNhds A) (· ≤ ·) where
  directed p q :=
    ⟨⟨max p.idx q.idx,
      ⟨p.nhd.toOpens ⊓ q.nhd.toOpens,
       fun _ hx => ⟨p.nhd.subset_carrier (hA (le_max_left _ _) hx),
                     q.nhd.subset_carrier (hA (le_max_right _ _) hx)⟩⟩⟩,
     (inf_le_left : p.nhd.toOpens ⊓ q.nhd.toOpens ≤ p.nhd.toOpens),
     (inf_le_right : p.nhd.toOpens ⊓ q.nhd.toOpens ≤ q.nhd.toOpens)⟩

/-- Forgetful map from a combined open neighbourhood $(k, U)$ to an open neighbourhood of
the intersection $\bigcap_k A_k$: since $\bigcap_k A_k \subseteq A_k \subseteq U$. -/
def toNhdsInter (_hA : Antitone A) :
    CombinedOpenNhds A → OpenNhdsOfSet (⋂ k, A k) :=
  fun p => ⟨p.nhd.toOpens, Set.iInter_subset_of_subset p.idx p.nhd.subset_carrier⟩

/-- The forgetful map `toNhdsInter` is monotone with respect to the reverse-inclusion
preorders. -/
theorem toNhdsInter_monotone (hA : Antitone A) :
    Monotone (toNhdsInter hA) := fun _ _ h => h

/-- Cofinality of `toNhdsInter`: in a Hausdorff space, every open neighbourhood of the
intersection $\bigcap_k A_k$ of an antitone family of compacts $A_k$ contains some $A_k$,
giving a refinement coming from a combined open neighbourhood. -/
theorem toNhdsInter_cofinal [T2Space α]
    (hA : Antitone A) (hcpt : ∀ k, IsCompact (A k)) :
    ∀ (V : OpenNhdsOfSet (⋂ k, A k)), ∃ (p : CombinedOpenNhds A),
      V ≤ toNhdsInter hA p := by
  intro V
  have hdir : Directed (· ⊇ ·) A :=
    fun i j => ⟨max i j, hA (le_max_left _ _), hA (le_max_right _ _)⟩
  obtain ⟨k, hk⟩ := exists_subset_nhds_of_isCompact hdir hcpt
    (fun x hx => V.toOpens.isOpen.mem_nhds (V.subset_carrier hx))
  exact ⟨⟨k, ⟨V.toOpens, hk⟩⟩, le_refl _⟩

/-- Finality of `toNhdsInter` as a functor: cofinality plus monotonicity in a Hausdorff
space ensure that colimits along the combined index agree with colimits along open
neighbourhoods of the intersection. -/
theorem toNhdsInter_functor_final [T2Space α]
    (hA : Antitone A) (hcpt : ∀ k, IsCompact (A k)) :
    letI : IsDirected (CombinedOpenNhds A) (· ≤ ·) := isDirectedOfAntitone hA
    (toNhdsInter_monotone hA).functor.Final := by
  letI : IsDirected (CombinedOpenNhds A) (· ≤ ·) := isDirectedOfAntitone hA
  rw [Monotone.final_functor_iff]
  exact toNhdsInter_cofinal hA hcpt

/-- **Lemma 37.2 (categorical core).** In a Hausdorff space, for any presheaf $F$ on the
opens of $\alpha$ and an antitone family of compacts $A_k$ with intersection $A$, the colimit
of $F$ over open neighbourhoods of $A$ is canonically isomorphic to the colimit of $F$
along the combined index built from the $A_k$. -/
noncomputable def cechCohomology_colimit_iso [T2Space α]
    {C : Type*} [Category C]
    (A : ℕ → Set α) (hA : Antitone A) (hcpt : ∀ k, IsCompact (A k))
    (F : (Opens α)ᵒᵖ ⥤ C)
    [HasColimit (OpenNhdsOfSet.inclusionFunctorOp ⋙ F : OpenNhdsOfSet (⋂ k, A k) ⥤ C)] :
    let G := (OpenNhdsOfSet.inclusionFunctorOp ⋙ F : OpenNhdsOfSet (⋂ k, A k) ⥤ C)
    letI : IsDirected (CombinedOpenNhds A) (· ≤ ·) := isDirectedOfAntitone hA
    letI : (toNhdsInter_monotone hA).functor.Final :=
      toNhdsInter_functor_final hA hcpt
    colimit ((toNhdsInter_monotone hA).functor ⋙ G) ≅ colimit G := by
  letI : IsDirected (CombinedOpenNhds A) (· ≤ ·) := isDirectedOfAntitone hA
  haveI : (toNhdsInter_monotone hA).functor.Final :=
    toNhdsInter_functor_final hA hcpt
  exact Functor.Final.colimitIso _ _

end CombinedOpenNhds

end OpenNhdsColimit

section CechCohomologySpecialization

variable {α : Type} [TopologicalSpace α]

namespace CombinedOpenNhds

variable {A : ℕ → Set α}

/-- `cechCohomology_colimit_iso` specialised to `C = ModuleCat.{0} R`, the variant used to
prove Lemma 37.2 in the Čech-cohomology setting. -/
noncomputable def cechCohomology_colimit_iso_cech [T2Space α]
    (R : Type) [CommRing R]
    (A : ℕ → Set α) (hA : Antitone A) (hcpt : ∀ k, IsCompact (A k))
    (F : (Opens α)ᵒᵖ ⥤ ModuleCat.{0} R)
    [HasColimit (OpenNhdsOfSet.inclusionFunctorOp ⋙ F :
      OpenNhdsOfSet (⋂ k, A k) ⥤ ModuleCat.{0} R)] :
    let G := (OpenNhdsOfSet.inclusionFunctorOp ⋙ F :
      OpenNhdsOfSet (⋂ k, A k) ⥤ ModuleCat.{0} R)
    letI : IsDirected (CombinedOpenNhds A) (· ≤ ·) := isDirectedOfAntitone hA
    letI : (toNhdsInter_monotone hA).functor.Final :=
      toNhdsInter_functor_final hA hcpt
    colimit ((toNhdsInter_monotone hA).functor ⋙ G) ≅ colimit G :=
  cechCohomology_colimit_iso A hA hcpt F

end CombinedOpenNhds

end CechCohomologySpecialization

end PoincareDuality

namespace CapProduct

open PoincareDuality

variable (R : Type) [CommRing R]

/-- **Corollary 37.5 (cap-product / PID form).** Over a PID $R$, for a compact $R$-oriented
$n$-manifold $M$, the absolute cap-product map
$\cap[M] : H^p(M; R) \to H_q(M; R)$ is an iso for $p + q = n$. -/
theorem poincare_duality
    [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (p q : ℕ) (hpq : p + q = n) :
    IsIso (capFundamentalAbsolute R n M p q hpq) :=
  capFundamentalAbsolute_isIso R n M p q hpq

end CapProduct

namespace PoincareDualityCompact

open CategoryTheory PoincareDuality

/-- Bridge identifying the `SingularCohomology.singularCohomology` module (used elsewhere in
the project) with the `relativeSingularCohomology … ∅` module used in this file, as
$R$-linear equivalence. -/
noncomputable def cohomologyBridge (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (p : ℕ) :
    (SingularCohomology.singularCohomology R (TopCat.of M) (ModuleCat.of R R) p : Type) ≃ₗ[R]
    (relativeSingularCohomology R M ∅ p : Type) := by sorry

/-- Bridge identifying the `SingularCohomology.singularHomologyModule` module (used
elsewhere) with the `relativeSingularHomology … ∅` module used in this file, as $R$-linear
equivalence. -/
noncomputable def homologyBridge (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (q : ℕ) :
    (SingularCohomology.singularHomologyModule R (TopCat.of M) q : Type) ≃ₗ[R]
    (relativeSingularHomology R M ∅ q : Type) := by sorry

/-- An `IsROriented` instance in the outer namespace promotes to one in
`PoincareDuality.IsROriented`, which is the form used by `poincareDualityMap`. -/
instance isROriented_toPoincareDuality (R : Type) [CommRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [h : IsROriented R n M] : PoincareDuality.IsROriented R n M :=
  ⟨h.isROrientable⟩

/-- Compatibility: the externally defined `poincareDualityMap` equals the composite of
`cohomologyBridge`, `capFundamentalAbsolute`, and the inverse of `homologyBridge`. -/
theorem poincareDualityMap_bridge_comm (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    [PoincareDuality.IsROriented R n M]
    (p q : ℕ) (hpq : p + q = n) :
    poincareDualityMap R n M p q hpq =
    (homologyBridge R n M q).symm.toLinearMap ∘ₗ
    (capFundamentalAbsolute R n M p q hpq).hom' ∘ₗ
    (cohomologyBridge R n M p).toLinearMap := by sorry

/-- If `capFundamentalAbsolute` is an iso, then `poincareDualityMap` is bijective, by
composing with the two bridge equivalences. -/
theorem poincareDualityMap_bijective_of_isIso (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    [PoincareDuality.IsROriented R n M]
    (p q : ℕ) (hpq : p + q = n)
    (hiso : IsIso (capFundamentalAbsolute R n M p q hpq)) :
    Function.Bijective (poincareDualityMap R n M p q hpq) := by
  rw [poincareDualityMap_bridge_comm R n M p q hpq]
  show Function.Bijective ↑((homologyBridge R n M q).symm.toLinearMap ∘ₗ
    (capFundamentalAbsolute R n M p q hpq).hom' ∘ₗ (cohomologyBridge R n M p).toLinearMap)
  rw [LinearMap.coe_comp, LinearMap.coe_comp]
  have hf_bij : Function.Bijective (capFundamentalAbsolute R n M p q hpq).hom' :=
    ConcreteCategory.bijective_of_isIso (capFundamentalAbsolute R n M p q hpq)
  exact Function.Bijective.comp (LinearEquiv.bijective (homologyBridge R n M q).symm)
    (Function.Bijective.comp hf_bij (LinearEquiv.bijective (cohomologyBridge R n M p)))

/-- `poincareDualityMap` is bijective for any compact $R$-oriented $n$-manifold over a PID
$R$, obtained by combining `poincareDualityMap_bijective_of_isIso` with
`CapProduct.poincare_duality`. -/
theorem poincareDualityMap_bijective
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (p q : ℕ) (hpq : p + q = n) :
    Function.Bijective (poincareDualityMap R n M p q hpq) := by
  letI hPD : PoincareDuality.IsROriented R n M := isROriented_toPoincareDuality R n M
  exact poincareDualityMap_bijective_of_isIso R n M p q hpq
    (CapProduct.poincare_duality R n M p q hpq)

/-- Poincaré duality as an explicit $R$-linear equivalence
$H^p(M; R) \cong H_q(M; R)$, packaged from `poincareDualityMap_bijective`. -/
noncomputable def poincareDualityEquiv
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (p q : ℕ) (hpq : p + q = n) :
    (SingularCohomology.singularCohomology R (TopCat.of M) (ModuleCat.of R R) p : Type) ≃ₗ[R]
    (SingularCohomology.singularHomologyModule R (TopCat.of M) q : Type) :=
  LinearEquiv.ofBijective
    (poincareDualityMap R n M p q hpq)
    (poincareDualityMap_bijective R n M p q hpq)

end PoincareDualityCompact

namespace PoincareDualityZMod2

open CategoryTheory AlgebraicTopology LinearMap SingularCohomology
open AlgebraicTopologyI PoincareDuality

/-- Every compact Hausdorff $n$-manifold is canonically $\mathbb{Z}/2$-oriented, since the
mod-$2$ orientation sheaf is always trivial. The basis for unconditional mod-$2$ Poincaré
duality on closed manifolds. -/
theorem isROriented_zmod2_of_compact
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [CompactSpace M] [T2Space M] :
    IsROriented (ZMod 2) n M := by sorry


/-- From the absolute cap-product iso (mod $2$), produce a fundamental class
$\mu \in H_n(M; \mathbb{Z}/2)$ for which the cup-product pairing
$H^p(M; \mathbb{Z}/2) \otimes H^q(M; \mathbb{Z}/2) \to \mathbb{Z}/2$ is a perfect pairing for
every $p + q = n$, and show uniqueness of such a class. -/
theorem capIso_to_cupPerfPair
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [TopologicalManifold n M] [CompactSpace M]
    [IsROriented (ZMod 2) n M]
    (hcap : ∀ (p q : ℕ) (hpq : p + q = n),
      IsIso (capFundamentalAbsolute (ZMod 2) n M p q hpq)) :
    ∃! (μ : HomolZMod2 (TopCat.of M) n),
      ∀ (p q : ℕ) (hpq : p + q = n),
        (cupProductPairing (TopCat.of M) n μ p q hpq).IsPerfPair := by sorry


end PoincareDualityZMod2
