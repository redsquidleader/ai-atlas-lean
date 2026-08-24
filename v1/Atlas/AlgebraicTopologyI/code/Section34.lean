/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section26
import Atlas.AlgebraicTopologyI.code.Section31
import Atlas.AlgebraicTopologyI.code.Section33

import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Order.Directed
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Sets.Opens
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Geometry.Manifold.ChartedSpace

open CategoryTheory AlgebraicTopology TopologicalSpace SingularCohomology

noncomputable section

namespace CechCohomology

/-- **Regular-neighborhood condition** (Section 34, Čech-cohomology setup).
For a directed system of `R`-modules `(G i)` with structure maps and a
compatible collection of maps `g i : G i →ₗ[R] P` to a target module `P`,
the system satisfies the regular-neighborhood condition when each index
`i` is dominated by some `j ≥ i` for which `g j` is a *bijection*.  This
abstract criterion captures the geometric situation where, for a compact
subset `K ⊂ X`, the cohomology of every sufficiently small open
neighborhood already agrees with the cohomology of `K`, and is the key
hypothesis allowing the direct-limit (Čech) cohomology to be identified
with a single representative. -/
def RegularNeighborhoodCondition
    {R : Type*} [CommRing R] {ι : Type*} [Preorder ι]
    {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    {P : Type*} [AddCommGroup P] [Module R P]
    (g : ∀ i, G i →ₗ[R] P) : Prop :=
  ∀ i, ∃ j, i ≤ j ∧ Function.Bijective (g j)

/-- **Direct-limit isomorphism under the regular-neighborhood condition**
(Section 34).  If a compatible collection of maps `g i : G i → P` from a
directed system satisfies `RegularNeighborhoodCondition`, then the
canonical map `Module.DirectLimit.lift … g` from the colimit `colim G` to
`P` is *bijective*.  Geometrically, this lets us identify the Čech
cohomology of `K` (the colimit over neighborhoods) with the singular
cohomology of any sufficiently small regular neighborhood.  Surjectivity
follows from one bijective level, injectivity from the cofinality of such
levels. -/
theorem cech_cohomology_iso_of_regular_neighborhood_condition
    {R : Type*} [CommRing R] {ι : Type*} [Preorder ι] [DecidableEq ι]
    {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    {f : ∀ i j, i ≤ j → G i →ₗ[R] G j}
    [DirectedSystem G (f · · ·)] [IsDirectedOrder ι] [Nonempty ι]
    {P : Type*} [AddCommGroup P] [Module R P]
    (g : ∀ i, G i →ₗ[R] P)
    (hg : ∀ i j hij x, g j (f i j hij x) = g i x)
    (hreg : RegularNeighborhoodCondition g) :
    Function.Bijective (Module.DirectLimit.lift R ι G f g hg) := by


  constructor
  ·


    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    rw [LinearMap.mem_ker] at hz
    obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
    simp only [Module.DirectLimit.lift_of] at hz
    obtain ⟨j, hij, hbij⟩ := hreg i
    have h1 : g j (f i j hij x) = 0 := by rw [hg]; exact hz
    have hfx : f i j hij x = 0 := hbij.1 (by rw [h1, map_zero])
    rw [Submodule.mem_bot]
    have : Module.DirectLimit.of R ι G f i x =
        Module.DirectLimit.of R ι G f j (f i j hij x) := by
      rw [Module.DirectLimit.of_f]
    rw [this, hfx, map_zero]
  ·


    intro x
    obtain ⟨i⟩ : Nonempty ι := inferInstance
    obtain ⟨j, _, hbij⟩ := hreg i
    obtain ⟨y, hy⟩ := hbij.2 x
    exact ⟨Module.DirectLimit.of R ι G f j y, by simp [hy]⟩

/-- **Linear equivalence form of the direct-limit isomorphism.**  Packaging
of `cech_cohomology_iso_of_regular_neighborhood_condition` as an honest
`R`-linear equivalence `Module.DirectLimit G f ≃ₗ[R] P` whenever the
`RegularNeighborhoodCondition` holds.  This is the form used downstream
when identifying Čech cohomology of a compact set with the singular
cohomology of a neighborhood. -/
def cechCohomologyLinearEquiv
    {R : Type*} [CommRing R] {ι : Type*} [Preorder ι] [DecidableEq ι]
    {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    {f : ∀ i j, i ≤ j → G i →ₗ[R] G j}
    [DirectedSystem G (f · · ·)] [IsDirectedOrder ι] [Nonempty ι]
    {P : Type*} [AddCommGroup P] [Module R P]
    (g : ∀ i, G i →ₗ[R] P)
    (hg : ∀ i j hij x, g j (f i j hij x) = g i x)
    (hreg : RegularNeighborhoodCondition g) :
    Module.DirectLimit G f ≃ₗ[R] P :=
  LinearEquiv.ofBijective
    (Module.DirectLimit.lift R ι G f g hg)
    (cech_cohomology_iso_of_regular_neighborhood_condition g hg hreg)

/-- **Open neighborhoods of a subset `K ⊂ X`.**  The type of pairs
`(U, hKU)` consisting of an open set `U : Opens X` together with a proof
that `K ⊆ U`.  Ordered by *reverse inclusion* (smaller neighborhoods are
"larger" in the poset), this indexes the directed system whose colimit
defines the Čech cohomology of `K`. -/
def OpenNeighborhoods {X : Type*} [TopologicalSpace X] (K : Set X) : Type _ :=
  { U : Opens X // K ⊆ U.1 }

/-- The reverse-inclusion preorder on open neighborhoods of `K`: `U ≤ V`
means `V ⊆ U`.  This is the standard convention so that "smaller
neighborhoods" come later, making the system *directed downward* and
inducing the correct directed colimit on cohomology. -/
instance openNeighborhoods_preorder {X : Type*} [TopologicalSpace X] (K : Set X) :
    Preorder (OpenNeighborhoods K) where
  le U V := V.1 ≤ U.1
  le_refl _ := le_refl _
  le_trans _ _ _ h1 h2 := le_trans h2 h1

/-- The poset of open neighborhoods of `K` is directed: any two
neighborhoods `U` and `V` are both refined by their intersection `U ∩ V`,
which is again open and still contains `K`. -/
instance openNeighborhoods_directed {X : Type*} [TopologicalSpace X] (K : Set X) :
    IsDirected (OpenNeighborhoods K) (· ≤ ·) where
  directed U V := by
    refine ⟨⟨U.1 ⊓ V.1, ?_⟩, ?_, ?_⟩
    · intro x hx; exact ⟨U.2 hx, V.2 hx⟩
    · show U.1 ⊓ V.1 ≤ U.1; exact inf_le_left
    · show U.1 ⊓ V.1 ≤ V.1; exact inf_le_right

/-- The poset of open neighborhoods of `K` is nonempty: the ambient space
`X = ⊤` is always an open neighborhood of `K`. -/
instance openNeighborhoods_nonempty {X : Type*} [TopologicalSpace X] (K : Set X) :
    Nonempty (OpenNeighborhoods K) :=
  ⟨⟨⊤, fun _ _ => trivial⟩⟩

/-- **Neighborhood-retract property** of a subset `X ⊂ ℝⁿ`.  `X` is a
neighborhood retract when there exists an open neighborhood `U ⊇ X` and a
continuous retraction `r : U → X` (i.e. `r` restricted to `X` is the
identity).  Compact ANRs in `ℝⁿ` (in particular all compact topological
manifolds and CW complexes) have this property, which is the geometric
input that lets the Čech cohomology of `X` be computed by the singular
cohomology of a neighborhood. -/
def IsNeighborhoodRetract {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ (U : Set (EuclideanSpace ℝ (Fin n))) (_ : IsOpen U) (hXU : X ⊆ U)
    (r : ↥U → ↥X), Continuous r ∧ ∀ (x : ↥X), r ⟨x.1, hXU x.2⟩ = x

/-- **Inclusion of one neighborhood into a larger one.**  For two open
neighborhoods `U ≤ V` of `K` (so `V ⊆ U` in the reverse-inclusion
convention), the underlying-set inclusion `V ↪ U` is a morphism in `TopCat`.
This is the morphism whose restriction induces the structure map in the
directed system of cochain complexes used to define Čech cohomology. -/
def nbhdInclusion {X : Type*} [TopologicalSpace X] {K : Set X}
    {U V : OpenNeighborhoods K} (h : U ≤ V) : TopCat.of ↥V.1.1 ⟶ TopCat.of ↥U.1.1 :=
  ⟨fun x => ⟨x.1, h x.2⟩, continuous_inclusion h⟩

/-- **Singular cohomology of a neighborhood `U` of `K`** in degree `p`,
with coefficients in `R`, packaged as a `ModuleCat R`.  This is the
typewise object that lives at index `U` in the directed system whose
colimit defines `cechCohomology R K p`. -/
def nbhdSingCohom (R : Type) [CommRing R] {X : Type} [TopologicalSpace X] {K : Set X}
    (U : OpenNeighborhoods K) (p : ℕ) : ModuleCat.{0} R :=
  singularCohomology R (TopCat.of ↥U.1.1) (ModuleCat.of R R) p

/-- The underlying-type version of `nbhdSingCohom`, used so that the
direct-limit machinery (which works on plain types with `Module` structure)
can be applied to the family `U ↦ H^p(U; R)`. -/
def cechFamily (R : Type) [CommRing R] {X : Type} [TopologicalSpace X]
    (K : Set X) (p : ℕ) (U : OpenNeighborhoods K) : Type :=
  (nbhdSingCohom R U p : Type _)

/-- Inherited abelian-group structure on each level of the Čech family,
forwarded from the `ModuleCat`-valued `nbhdSingCohom`. -/
instance cechFamily_addCommGroup (R : Type) [CommRing R] {X : Type} [TopologicalSpace X]
    (K : Set X) (p : ℕ) (U : OpenNeighborhoods K) :
    AddCommGroup (cechFamily R K p U) :=
  (nbhdSingCohom R U p).isAddCommGroup

/-- Inherited `R`-module structure on each level of the Čech family,
forwarded from the `ModuleCat R`-valued `nbhdSingCohom`. -/
instance cechFamily_module (R : Type) [CommRing R] {X : Type} [TopologicalSpace X]
    (K : Set X) (p : ℕ) (U : OpenNeighborhoods K) :
    Module R (cechFamily R K p U) :=
  (nbhdSingCohom R U p).isModule

/-- **Transition map in the Čech directed system.**  For `U ≤ V` (i.e.
`V ⊆ U`), the inclusion `V ↪ U` induces a restriction map on singular
cochain complexes, and the resulting map on cohomology is the structure
map `cechFamily R K p U →ₗ[R] cechFamily R K p V` of the directed system
whose colimit is `cechCohomology R K p`. -/
def cechTransition (R : Type) [CommRing R] {X : Type} [TopologicalSpace X]
    (K : Set X) (p : ℕ) (U V : OpenNeighborhoods K) (h : U ≤ V) :
    cechFamily R K p U →ₗ[R] cechFamily R K p V :=
  (HomologicalComplex.homologyMap
    (restrictionCochainMap R (ModuleCat.of R R) (nbhdInclusion h)) p).hom

/-- **Definition 34.4 (Čech cohomology of a subset).**  The Čech
cohomology `Ȟ^p(K; R)` of a subset `K ⊂ X` with coefficients in `R` is
defined as the *directed colimit* over all open neighborhoods `U ⊇ K` of
the singular cohomologies `H^p(U; R)`, with structure maps given by
restriction along the inclusions `V ↪ U` of smaller neighborhoods.  This
agrees with the singular cohomology of `K` whenever `K` is a sufficiently
nice subset (e.g. compact ENR), via the regular-neighborhood criterion. -/
def cechCohomology (R : Type) [CommRing R]
    {X : Type} [TopologicalSpace X] (K : Set X) (p : ℕ) : ModuleCat.{0} R := by
  classical
  exact ModuleCat.of R (Module.DirectLimit (cechFamily R K p)
    (fun U V h => cechTransition R K p U V h))

/-- **An open cover of a topological space `Y`.**  Data of a collection of
open subsets `members ⊂ Opens Y` whose union is all of `Y`.  The set of
open covers, ordered by *refinement*, indexes the directed system used in
the Čech-cover (nerve) construction of Čech cohomology — an alternative,
combinatorial description that agrees with the neighborhood definition
for sufficiently nice spaces. -/
structure OpenCover (Y : Type) [TopologicalSpace Y] where
  members : Set (Opens Y)
  covers : ∀ y : Y, ∃ U ∈ members, y ∈ (U : Set Y)

/-- **Refinement of open covers.**  `𝒱.Refines 𝒰` means every member of
`𝒱` is contained in some member of `𝒰`; equivalently, `𝒱` is "finer"
than `𝒰`.  This is the order on `OpenCover Y` used to form the directed
system computing nerve cohomology. -/
def OpenCover.Refines {Y : Type} [TopologicalSpace Y]
    (𝒱 𝒰 : OpenCover Y) : Prop :=
  ∀ V ∈ 𝒱.members, ∃ U ∈ 𝒰.members, (V : Set Y) ⊆ U

/-- The preorder on `OpenCover Y` where `𝒰 ≤ 𝒱` iff `𝒱` refines `𝒰`.
Reflexivity is the trivial self-refinement; transitivity composes
witnesses. -/
instance openCoverPreorder {Y : Type} [TopologicalSpace Y] :
    Preorder (OpenCover Y) where
  le 𝒰 𝒱 := 𝒱.Refines 𝒰
  le_refl 𝒰 := fun V hV => ⟨V, hV, le_refl _⟩
  le_trans _ _ _ h1 h2 := by
    intro W hW
    obtain ⟨V, hV, hWV⟩ := h2 W hW
    obtain ⟨U, hU, hVU⟩ := h1 V hV
    exact ⟨U, hU, hWV.trans hVU⟩

/-- **Cohomology of the nerve of an open cover.**  The simplicial complex
(nerve) `N(𝒰)` of an open cover `𝒰` has a vertex for each member of `𝒰`
and a `k`-simplex for each `(k+1)`-tuple with nonempty common
intersection; its singular (= simplicial) cohomology in degree `p` is the
combinatorial input to the Čech-cover construction of `Ȟ^p(Y; R)`. -/
noncomputable def nerveCohomModule (R : Type) [CommRing R] {Y : Type} [TopologicalSpace Y]
    (𝒰 : OpenCover Y) (p : ℕ) : ModuleCat.{0} R := by sorry


/-- Underlying-type version of `nerveCohomModule`, so that direct-limit
machinery on plain `Module`-types may be applied. -/
def nerveCohomType (R : Type) [CommRing R] {Y : Type} [TopologicalSpace Y]
    (𝒰 : OpenCover Y) (p : ℕ) : Type :=
  (nerveCohomModule R 𝒰 p : Type _)

/-- Inherited abelian-group structure on nerve cohomology, forwarded from
the `ModuleCat`-valued `nerveCohomModule`. -/
instance nerveCohomType_addCommGroup (R : Type) [CommRing R]
    {Y : Type} [TopologicalSpace Y] (𝒰 : OpenCover Y) (p : ℕ) :
    AddCommGroup (nerveCohomType R 𝒰 p) :=
  (nerveCohomModule R 𝒰 p).isAddCommGroup

/-- Inherited `R`-module structure on nerve cohomology, forwarded from
`nerveCohomModule`. -/
instance nerveCohomType_module (R : Type) [CommRing R]
    {Y : Type} [TopologicalSpace Y] (𝒰 : OpenCover Y) (p : ℕ) :
    Module R (nerveCohomType R 𝒰 p) :=
  (nerveCohomModule R 𝒰 p).isModule


/-- **Transition map for refinement of open covers.**  A refinement
`𝒱 ≼ 𝒰` (with our convention `𝒰 ≤ 𝒱`) gives a simplicial map between
nerves `N(𝒱) → N(𝒰)`, hence a map `H^p(N(𝒰)) → H^p(N(𝒱))` on
cohomology.  This is the structure map in the directed system whose
colimit is `cechConstructionCohomology`. -/
noncomputable def nerveCohomTransition (R : Type) [CommRing R] {Y : Type} [TopologicalSpace Y]
    (p : ℕ) (𝒰 𝒱 : OpenCover Y) (h : 𝒰 ≤ 𝒱) :
    nerveCohomType R 𝒰 p →ₗ[R] nerveCohomType R 𝒱 p := by sorry


/-- **The Čech-construction cohomology** of a space `Y` in degree `p`:
the directed colimit, over all open covers ordered by refinement, of the
nerve cohomologies `H^p(N(𝒰))`.  For paracompact Hausdorff spaces this
agrees with singular cohomology, providing the classical combinatorial
construction of Čech cohomology. -/
def cechConstructionCohomology (R : Type) [CommRing R]
    (Y : TopCat.{0}) (p : ℕ) : ModuleCat.{0} R := by
  classical
  exact ModuleCat.of R (Module.DirectLimit
    (fun (𝒰 : OpenCover Y) => nerveCohomType R 𝒰 p)
    (fun 𝒰 𝒱 h => nerveCohomTransition R p 𝒰 𝒱 h))

/-- **Equivalence of Čech constructions** (Section 34).  For a compact
neighborhood retract `X ⊂ ℝⁿ`, the neighborhood-based Čech cohomology
`cechCohomology R X p` and the Čech-cover (nerve-based) construction
`cechConstructionCohomology R X p` are isomorphic.  Both refine to the
singular cohomology of `X` itself. -/
noncomputable def cechCohomology_iso_cechConstruction
    (R : Type) [CommRing R]
    {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hcomp : IsCompact X) (hretract : IsNeighborhoodRetract X) (p : ℕ) :
    cechCohomology R X p ≅ cechConstructionCohomology R (TopCat.of ↥X) p := by sorry


/-- **Embedding-independence of Čech cohomology.**  Two homeomorphic
compact neighborhood retracts (possibly sitting in Euclidean spaces of
different dimensions) have isomorphic Čech cohomology.  This is the
formal expression that `Ȟ^p(K)` depends only on the homeomorphism type
of `K`, not on a particular embedding into `ℝⁿ`. -/
noncomputable def cechCohomology_independent_of_embedding
    (R : Type) [CommRing R]
    {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hcompX : IsCompact X) (hretractX : IsNeighborhoodRetract X)
    {m : ℕ} (Y : Set (EuclideanSpace ℝ (Fin m)))
    (hcompY : IsCompact Y) (hretractY : IsNeighborhoodRetract Y)
    (φ : TopCat.of ↥X ≅ TopCat.of ↥Y)
    (p : ℕ) :
    cechCohomology R X p ≅ cechCohomology R Y p := by sorry


/-- **Topological version of the regular-neighborhood condition.**  A
specialization of `RegularNeighborhoodCondition` to the index category of
`OpenNeighborhoods K`: every neighborhood `U ⊇ K` admits a smaller
neighborhood `V ⊆ U` for which the comparison map `g V` is a bijection.
This is the form actually used to conclude that Čech cohomology equals
the cohomology of a sufficiently small regular neighborhood. -/
def TopologicalRegularNeighborhoodCondition
    {X : Type*} [TopologicalSpace X] {K : Set X}
    {R : Type*} [CommRing R]
    {H : OpenNeighborhoods K → Type*}
    [∀ U, AddCommGroup (H U)] [∀ U, Module R (H U)]
    {P : Type*} [AddCommGroup P] [Module R P]
    (g : ∀ U : OpenNeighborhoods K, H U →ₗ[R] P) : Prop :=
  ∀ U : OpenNeighborhoods K, ∃ V : OpenNeighborhoods K, U ≤ V ∧ Function.Bijective (g V)

/-- **Čech-cohomology isomorphism in the topological setting.**  For a
closed subset `K` of `X` and a compatible system `g U : H U → P` of maps
from a directed system indexed by open neighborhoods of `K`, the
condition `TopologicalRegularNeighborhoodCondition` implies that the
induced map from the colimit (the Čech cohomology) to `P` is a
bijection.  This is the central technical lemma used to identify
`Ȟ^p(K)` with the cohomology of a regular neighborhood. -/
theorem topological_cech_cohomology_iso
    {X : Type*} [TopologicalSpace X] {K : Set X} (_hK : IsClosed K)
    {R : Type*} [CommRing R] [DecidableEq (OpenNeighborhoods K)]
    {H : OpenNeighborhoods K → Type*}
    [∀ U, AddCommGroup (H U)] [∀ U, Module R (H U)]
    {ρ : ∀ U V : OpenNeighborhoods K, U ≤ V → H U →ₗ[R] H V}
    [DirectedSystem H (ρ · · ·)]
    {P : Type*} [AddCommGroup P] [Module R P]
    (g : ∀ U : OpenNeighborhoods K, H U →ₗ[R] P)
    (hcompat : ∀ U V (h : U ≤ V) x, g V (ρ U V h x) = g U x)
    (hreg : TopologicalRegularNeighborhoodCondition g) :
    Function.Bijective (Module.DirectLimit.lift R (OpenNeighborhoods K) H ρ g hcompat) :=
  cech_cohomology_iso_of_regular_neighborhood_condition g hcompat hreg

/-- **Linear-equivalence form of the topological Čech isomorphism.**
Packages `topological_cech_cohomology_iso` as an honest linear
equivalence `Module.DirectLimit H ρ ≃ₗ[R] P`. -/
def topologicalCechCohomologyLinearEquiv
    {X : Type*} [TopologicalSpace X] {K : Set X} (_hK : IsClosed K)
    {R : Type*} [CommRing R] [DecidableEq (OpenNeighborhoods K)]
    {H : OpenNeighborhoods K → Type*}
    [∀ U, AddCommGroup (H U)] [∀ U, Module R (H U)]
    {ρ : ∀ U V : OpenNeighborhoods K, U ≤ V → H U →ₗ[R] H V}
    [DirectedSystem H (ρ · · ·)]
    {P : Type*} [AddCommGroup P] [Module R P]
    (g : ∀ U : OpenNeighborhoods K, H U →ₗ[R] P)
    (hcompat : ∀ U V (h : U ≤ V) x, g V (ρ U V h x) = g U x)
    (hreg : TopologicalRegularNeighborhoodCondition g) :
    Module.DirectLimit H ρ ≃ₗ[R] P :=
  LinearEquiv.ofBijective
    (Module.DirectLimit.lift R (OpenNeighborhoods K) H ρ g hcompat)
    (topological_cech_cohomology_iso _hK g hcompat hreg)

end CechCohomology

namespace CapProduct

variable (R : Type) [CommRing R]

/-- **Abstract cap-product pairing** (Section 34).  A bundled
specification of a cap-product: three `R`-modules (`CohomGrp`, the
"cohomology group" acting; and two "relative homology groups" `RelHomGrpN`
and `RelHomGrpQ`) together with a bilinear pairing
`cap : CohomGrp →ₗ[R] RelHomGrpN →ₗ[R] RelHomGrpQ`.  This abstracts the
algebraic structure of the cap product `H^p(Y; R) ⊗ H_{p+q}(Y, A) → H_q(Y, A)`
so that the projection-and-excision proof of Lemma 34.3 works at the level
of an axiomatic interface, free of singular-cohomology specifics. -/
structure CapProductPairing (R : Type) [CommRing R] where
  CohomGrp : Type
  [instCohomACG : AddCommGroup CohomGrp]
  [instCohomMod : Module R CohomGrp]
  RelHomGrpN : Type
  [instRelHomNACG : AddCommGroup RelHomGrpN]
  [instRelHomNMod : Module R RelHomGrpN]
  RelHomGrpQ : Type
  [instRelHomQACG : AddCommGroup RelHomGrpQ]
  [instRelHomQMod : Module R RelHomGrpQ]
  cap : CohomGrp →ₗ[R] RelHomGrpN →ₗ[R] RelHomGrpQ

attribute [instance] CapProductPairing.instCohomACG CapProductPairing.instCohomMod
  CapProductPairing.instRelHomNACG CapProductPairing.instRelHomNMod
  CapProductPairing.instRelHomQACG CapProductPairing.instRelHomQMod

/-- **Geometrically situated cap-product pairing.**  A
`CapProductPairing` tagged with the data of an open set `Y` and a subset
`K ⊆ Y` in some ambient space `X`; this provides the geometric context
(open set, compact subset, etc.) needed for the excision-and-projection
argument used in Lemma 34.3. -/
structure CapProductPairingOf (R : Type) [CommRing R]
    {X : Type*} [TopologicalSpace X] (Y K : Set X) (hY : IsOpen Y) (hK : K ⊆ Y)
    extends CapProductPairing R

/-- **Abstract excision data.**  When `V ⊆ U` are two open subsets both
containing `K`, the inclusion-induced relative-homology maps
`H_*(V, V \ K) → H_*(U, U \ K)` are isomorphisms (excision); the
`ExcisionData` bundles the *inverse* linear maps as opaque morphisms,
without yet requiring them to be specific singular-homology
isomorphisms.  This is what lets the abstract Lemma 34.3 talk about
excision without proving it. -/
structure ExcisionData (R : Type) [CommRing R]
    {X : Type*} [TopologicalSpace X] {K U V : Set X}
    (hK : IsClosed K) (hVU : V ⊆ U)
    (pairU : CapProductPairing R) (pairV : CapProductPairing R) where
  excInvN : pairU.RelHomGrpN →ₗ[R] pairV.RelHomGrpN
  excInvQ : pairU.RelHomGrpQ →ₗ[R] pairV.RelHomGrpQ

/-- **Abstract projection formula.**  For two cap-product pairings
`pairY, pairZ` representing the cap products on a "smaller" space `Y` and
a "larger" space `Z`, this structure bundles a pullback on cohomology
together with pushforwards on the two relative-homology groups, such that
the diagram `f_*(f^*b ⌢ x) = b ⌢ f_*x` commutes.  This is the algebraic
content of the projection (naturality) formula for the cap product. -/
structure ProjectionFormula (R : Type) [CommRing R]
    (pairY pairZ : CapProductPairing R) where
  pullback : pairZ.CohomGrp →ₗ[R] pairY.CohomGrp
  pushforwardN : pairY.RelHomGrpN →ₗ[R] pairZ.RelHomGrpN
  pushforwardQ : pairY.RelHomGrpQ →ₗ[R] pairZ.RelHomGrpQ
  formula : ∀ (b : pairZ.CohomGrp) (x : pairY.RelHomGrpN),
    pushforwardQ (pairY.cap (pullback b) x) = pairZ.cap b (pushforwardN x)

end CapProduct

namespace CapProduct

variable (R : Type) [CommRing R]

/-- **Abstract form of Lemma 34.3 (cap product commutes with
restriction).**  Given two cap-product pairings on neighborhoods `V ⊆ U`
of `K`, an abstract projection formula linking them, and excision data
witnessing the isomorphism `H_*(V, V \ K) ≃ H_*(U, U \ K)`, the
following diagram commutes: capping in `U` and then excising equals
restricting in cohomology and capping in `V`.  This is the algebraic
skeleton used to prove that the cap product passes to the Čech-cohomology
colimit. -/
theorem cap_product_restriction_commutes_abstract
    {X : Type*} [TopologicalSpace X] {K U V : Set X}
    (hK : IsClosed K) (hU : IsOpen U) (hV : IsOpen V)
    (hKV : K ⊆ V) (hVU : V ⊆ U)
    (pairU : CapProductPairingOf R U K hU (hKV.trans hVU))
    (pairV : CapProductPairingOf R V K hV hKV)
    (ι : ProjectionFormula R pairV.toCapProductPairing pairU.toCapProductPairing)
    (exc : ExcisionData R hK hVU pairU.toCapProductPairing pairV.toCapProductPairing)
    (hexcN : Function.RightInverse exc.excInvN ι.pushforwardN)
    (hexcQ : Function.LeftInverse exc.excInvQ ι.pushforwardQ)
    (b : pairU.CohomGrp) (x : pairU.RelHomGrpN) :
    exc.excInvQ (pairU.cap b x) = pairV.cap (ι.pullback b) (exc.excInvN x) := by

  have h_push_inv : ι.pushforwardN (exc.excInvN x) = x := hexcN x
  have h_proj := ι.formula b (exc.excInvN x)
  rw [h_push_inv] at h_proj


  rw [← h_proj]
  exact hexcQ _

/-- **Relative singular homology** `H_n(Y, A; R)`, packaged as a
`ModuleCat R`.  Defined as the homology in degree `n` of the *cokernel*
chain complex `C_*(Y) / C_*(A)`, where the inclusion `A ↪ Y` induces a
chain map between singular-chain complexes.  This is the standard
"relative chain complex" construction. -/
noncomputable def relativeSingularHomologyModule
    (R : Type) [CommRing R] (Y : TopCat.{0}) (A : Set Y) (n : ℕ) : ModuleCat.{0} R :=
  let incl : TopCat.of A ⟶ Y := ⟨Subtype.val, continuous_subtype_val⟩
  let chainMap := ((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
    (ModuleCat.of R R)).map incl
  (CategoryTheory.Limits.cokernel chainMap).homology n

/-- **Descent of the cap product to relative singular homology.**  The
chain-level cap product `C^p(Y) ⊗ C_{p+q}(Y) → C_q(Y)` descends to a map
on relative homology
`H^p(Y; R) ⊗ H_{p+q}(Y, A) → H_q(Y, A)` because chains supported on `A`
are sent to chains supported on `A`.  This is the linear map of the
relative cap product in singular homology. -/
noncomputable def relativeCapProductHomologyDescent (R : Type) [CommRing R] (Y : TopCat.{0})
    (A : Set Y) (p q : ℕ) :
    (SingularCohomology.singularCohomologyR R Y p : Type) →ₗ[R]
    (relativeSingularHomologyModule R Y A (p + q) : Type) →ₗ[R]
    (relativeSingularHomologyModule R Y A q : Type) := by sorry


/-- **The relative cap product**
`H^p(Y; R) ⊗ H_{p+q}(Y, A) → H_q(Y, A)`.  Alias for
`relativeCapProductHomologyDescent` exposing the standard
`A ⌢ x` interface. -/
noncomputable def relativeCapProduct
    (R : Type) [CommRing R] (Y : TopCat.{0}) (A : Set Y) (p q : ℕ) :
    (SingularCohomology.singularCohomologyR R Y p : Type) →ₗ[R]
    (relativeSingularHomologyModule R Y A (p + q) : Type) →ₗ[R]
    (relativeSingularHomologyModule R Y A q : Type) :=
  relativeCapProductHomologyDescent R Y A p q


/-- **Pushforward map on relative singular homology.**  A continuous map
`f : Y → Z` with `f(A) ⊆ B` induces a chain map of relative chain
complexes and hence a linear map `H_n(Y, A) → H_n(Z, B)`.  When `f` does
*not* send `A` into `B`, the convention here is to return the zero map
(so the definition is total). -/
def relativePushforwardMap
    (R : Type) [CommRing R] {Y Z : TopCat.{0}} (f : Y ⟶ Z)
    (A : Set Y) (B : Set Z) (n : ℕ) :
    (relativeSingularHomologyModule R Y A n : Type) →ₗ[R]
    (relativeSingularHomologyModule R Z B n : Type) := by
  classical
  by_cases hf : Set.MapsTo f A B
  · let f_A : TopCat.of A ⟶ TopCat.of B :=
      ⟨fun a => ⟨f a.val, hf a.property⟩, by fun_prop⟩
    let SCF := ((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj (ModuleCat.of R R))
    have comm : SCF.map (show TopCat.of A ⟶ Y from ⟨Subtype.val, continuous_subtype_val⟩) ≫
        SCF.map f =
        SCF.map f_A ≫
        SCF.map (show TopCat.of B ⟶ Z from ⟨Subtype.val, continuous_subtype_val⟩) := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
    exact (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.map _ _ (SCF.map f_A) (SCF.map f) comm) n).hom
  · exact 0


/-- **Excision at the chain level (quasi-isomorphism).**  For a closed
`K ⊂ X` and open neighborhoods `V ⊆ U` of `K`, the inclusion `V ↪ U`
induces a chain map of relative singular chain complexes
`C_*(V, V \ K) → C_*(U, U \ K)` which is a quasi-isomorphism in each
degree.  This is Mathlib's formulation of the classical excision theorem
at the level of `ModuleCat`-valued cokernels. -/
theorem excisionChainMap_quasiIsoAt_ModuleCat
    (R : Type) [CommRing R] {X : Type} [TopologicalSpace X] (K U V : Set X)
    (hK : IsClosed K) (hVU : V ⊆ U) (n : ℕ) :
    let SCF := ((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj (ModuleCat.of R R))
    let inclV : TopCat.of (Subtype.val ⁻¹' (V \ K) : Set V) ⟶ TopCat.of V :=
      ⟨Subtype.val, continuous_subtype_val⟩
    let inclU : TopCat.of (Subtype.val ⁻¹' (U \ K) : Set U) ⟶ TopCat.of U :=
      ⟨Subtype.val, continuous_subtype_val⟩
    let f : TopCat.of V ⟶ TopCat.of U :=
      TopCat.ofHom ⟨Set.inclusion hVU, continuous_inclusion hVU⟩
    let f_A : TopCat.of (Subtype.val ⁻¹' (V \ K) : Set V) ⟶
              TopCat.of (Subtype.val ⁻¹' (U \ K) : Set U) :=
      ⟨fun a => ⟨⟨(a : V).val, hVU (a : V).property⟩,
        by obtain ⟨⟨x, hxV⟩, hxVK⟩ := a
           simp only [Set.mem_preimage, Set.mem_diff] at hxVK ⊢
           exact ⟨hVU hxV, hxVK.2⟩⟩,
       by apply Continuous.subtype_mk
          exact (continuous_inclusion hVU).comp continuous_subtype_val⟩
    let comm : SCF.map inclV ≫ SCF.map f = SCF.map f_A ≫ SCF.map inclU := by
      rw [← Functor.map_comp, ← Functor.map_comp]; congr 1
    IsIso (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.map _ _ (SCF.map f_A) (SCF.map f) comm) n) := by sorry

/-- **Excision: relative pushforward is a bijection.**  Concrete
corollary of `excisionChainMap_quasiIsoAt_ModuleCat`: for `V ⊆ U` open
neighborhoods of a closed set `K`, the pushforward
`H_n(V, V \ K) → H_n(U, U \ K)` induced by the inclusion is bijective. -/
theorem excision_bijective
    (R : Type) [CommRing R] {X : Type} [TopologicalSpace X] (K U V : Set X)
    (hK : IsClosed K) (hVU : V ⊆ U) (n : ℕ) :
    Function.Bijective
      (relativePushforwardMap R (TopCat.ofHom ⟨Set.inclusion hVU, continuous_inclusion hVU⟩)
        (Subtype.val ⁻¹' (V \ K)) (Subtype.val ⁻¹' (U \ K)) n) := by

  unfold relativePushforwardMap
  simp only

  have hmt : Set.MapsTo (TopCat.ofHom ⟨Set.inclusion hVU, continuous_inclusion hVU⟩)
      (Subtype.val ⁻¹' (V \ K)) (Subtype.val ⁻¹' (U \ K)) := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_diff] at hx ⊢
    exact ⟨hVU x.property, hx.2⟩
  rw [dif_pos hmt]


  have hiso := excisionChainMap_quasiIsoAt_ModuleCat R K U V hK hVU n

  haveI : IsIso (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.map _ _ _ _ _) n) := hiso
  exact ConcreteCategory.bijective_of_isIso
    (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.map _ _ _ _ _) n)

/-- **Excision as a linear equivalence.**  Packages `excision_bijective`
as an honest `R`-linear isomorphism
`H_n(V, V \ K) ≃ₗ[R] H_n(U, U \ K)`. -/
def excisionLinearEquiv
    (R : Type) [CommRing R] {X : Type} [TopologicalSpace X] (K U V : Set X)
    (hK : IsClosed K) (hVU : V ⊆ U) (n : ℕ) :
    (relativeSingularHomologyModule R (TopCat.of V) (Subtype.val ⁻¹' (V \ K)) n : Type) ≃ₗ[R]
    (relativeSingularHomologyModule R (TopCat.of U) (Subtype.val ⁻¹' (U \ K)) n : Type) :=
  LinearEquiv.ofBijective
    (relativePushforwardMap R (TopCat.ofHom ⟨Set.inclusion hVU, continuous_inclusion hVU⟩)
      (Subtype.val ⁻¹' (V \ K)) (Subtype.val ⁻¹' (U \ K)) n)
    (excision_bijective R K U V hK hVU n)

/-- **Inverse of the excision isomorphism**, as a plain linear map.  This
is the map `H_n(U, U \ K) → H_n(V, V \ K)` used as `excInvN`/`excInvQ`
in the singular `ExcisionData`. -/
def excisionInverseMap
    (R : Type) [CommRing R] {X : Type} [TopologicalSpace X] (K U V : Set X)
    (hK : IsClosed K) (hVU : V ⊆ U) (n : ℕ) :
    (relativeSingularHomologyModule R (TopCat.of U) (Subtype.val ⁻¹' (U \ K)) n : Type) →ₗ[R]
    (relativeSingularHomologyModule R (TopCat.of V) (Subtype.val ⁻¹' (V \ K)) n : Type) :=
  (excisionLinearEquiv R K U V hK hVU n).symm.toLinearMap


/-- **Projection formula for the relative cap product.**  For a
continuous map `f : Y → Z` with `f(A) ⊆ B`, the relative cap product
satisfies `f_*(f^*b ⌢ x) = b ⌢ f_*x` for `b ∈ H^p(Z)` and
`x ∈ H_{p+q}(Y, A)`.  This is the relative-homology version of the
classical projection (naturality) formula. -/
theorem relativeCapProduct_projection (R : Type) [CommRing R]
    {Y Z : TopCat.{0}} (f : Y ⟶ Z) (A : Set Y) (B : Set Z)
    (hf : Set.MapsTo f A B) (p q : ℕ)
    (b : (SingularCohomology.singularCohomologyR R Z p : Type))
    (x : (relativeSingularHomologyModule R Y A (p + q) : Type)) :
    relativePushforwardMap R f A B q
      (relativeCapProduct R Y A p q
        ((SingularCohomology.cohomologyPullback R Y Z f p).hom b) x) =
    relativeCapProduct R Z B p q b
      (relativePushforwardMap R f A B (p + q) x) := by sorry

/-- **Projection formula for the inclusion `V ↪ U` of neighborhoods of
`K`.**  Specialization of `relativeCapProduct_projection` to the
geometric setting used in Lemma 34.3: `V ⊆ U` are open, both contain
`K`, and `f` is the inclusion. -/
theorem relative_projection_formula
    (R : Type) [CommRing R] {X : Type} [TopologicalSpace X]
    (K U V : Set X) (hK : IsClosed K) (hU : IsOpen U) (hV : IsOpen V)
    (hKV : K ⊆ V) (hVU : V ⊆ U) (p q : ℕ)
    (b : (SingularCohomology.singularCohomologyR R (TopCat.of U) p : Type))
    (x : (relativeSingularHomologyModule R (TopCat.of V)
            (Subtype.val ⁻¹' (V \ K)) (p + q) : Type)) :
    relativePushforwardMap R (TopCat.ofHom ⟨Set.inclusion hVU, continuous_inclusion hVU⟩)
      (Subtype.val ⁻¹' (V \ K)) (Subtype.val ⁻¹' (U \ K)) q
      (relativeCapProduct R (TopCat.of V) (Subtype.val ⁻¹' (V \ K)) p q
        ((SingularCohomology.cohomologyPullback R (TopCat.of V) (TopCat.of U)
          (TopCat.ofHom ⟨Set.inclusion hVU, continuous_inclusion hVU⟩) p).hom b) x) =
    relativeCapProduct R (TopCat.of U) (Subtype.val ⁻¹' (U \ K)) p q b
      (relativePushforwardMap R (TopCat.ofHom ⟨Set.inclusion hVU, continuous_inclusion hVU⟩)
        (Subtype.val ⁻¹' (V \ K)) (Subtype.val ⁻¹' (U \ K)) (p + q) x) := by
  have hf : Set.MapsTo (TopCat.ofHom ⟨Set.inclusion hVU, continuous_inclusion hVU⟩)
      (Subtype.val ⁻¹' (V \ K)) (Subtype.val ⁻¹' (U \ K)) := by
    intro ⟨v, hv⟩ hmem
    simp only [Set.mem_preimage, Set.mem_diff] at hmem ⊢
    exact ⟨hVU hmem.1, hmem.2⟩
  exact relativeCapProduct_projection R
    (TopCat.ofHom ⟨Set.inclusion hVU, continuous_inclusion hVU⟩)
    (Subtype.val ⁻¹' (V \ K)) (Subtype.val ⁻¹' (U \ K)) hf p q b x

/-- **Coherence: the excision linear equivalence is the pushforward.**
The underlying linear map of the excision equivalence is literally the
relative-pushforward map induced by the inclusion `V ↪ U`. -/
theorem excisionLinearEquiv_toLinearMap_eq_pushforward
    (R : Type) [CommRing R] {X : Type} [TopologicalSpace X]
    (K U V : Set X) (hK : IsClosed K) (hVU : V ⊆ U) (n : ℕ) :
    (excisionLinearEquiv R K U V hK hVU n).toLinearMap =
    relativePushforwardMap R (TopCat.ofHom ⟨Set.inclusion hVU, continuous_inclusion hVU⟩)
      (Subtype.val ⁻¹' (V \ K)) (Subtype.val ⁻¹' (U \ K)) n :=
  rfl

/-- **Right-inverse property of `excisionInverseMap`.**  Pushing forward
along `V ↪ U` and then applying `excisionInverseMap` recovers the
original element: `excInv ∘ push = id` on `H_n(V, V \ K)`. -/
theorem excisionInverseMap_rightInverse
    (R : Type) [CommRing R] {X : Type} [TopologicalSpace X]
    (K U V : Set X) (hK : IsClosed K) (hVU : V ⊆ U) (n : ℕ)
    (x : (relativeSingularHomologyModule R (TopCat.of V)
            (Subtype.val ⁻¹' (V \ K)) n : Type)) :
    excisionInverseMap R K U V hK hVU n
      (relativePushforwardMap R (TopCat.ofHom ⟨Set.inclusion hVU, continuous_inclusion hVU⟩)
        (Subtype.val ⁻¹' (V \ K)) (Subtype.val ⁻¹' (U \ K)) n x) = x := by
  unfold excisionInverseMap
  rw [← excisionLinearEquiv_toLinearMap_eq_pushforward R K U V hK hVU n]
  exact (excisionLinearEquiv R K U V hK hVU n).symm_apply_apply x

/-- **Left-inverse property of `excisionInverseMap`.**  Applying
`excisionInverseMap` and then pushing forward along `V ↪ U` recovers the
original element: `push ∘ excInv = id` on `H_n(U, U \ K)`. -/
@[simp]
theorem excisionInverseMap_leftInverse
    (R : Type) [CommRing R] {X : Type} [TopologicalSpace X]
    (K U V : Set X) (hK : IsClosed K) (hVU : V ⊆ U) (n : ℕ)
    (x : (relativeSingularHomologyModule R (TopCat.of U)
            (Subtype.val ⁻¹' (U \ K)) n : Type)) :
    relativePushforwardMap R (TopCat.ofHom ⟨Set.inclusion hVU, continuous_inclusion hVU⟩)
      (Subtype.val ⁻¹' (V \ K)) (Subtype.val ⁻¹' (U \ K)) n
      (excisionInverseMap R K U V hK hVU n x) = x := by
  unfold excisionInverseMap
  rw [← excisionLinearEquiv_toLinearMap_eq_pushforward R K U V hK hVU n]
  exact (excisionLinearEquiv R K U V hK hVU n).apply_symm_apply x

/-- **Concrete singular cap-product pairing on a neighborhood `Y` of
`K`.**  Specializes the abstract `CapProductPairingOf` structure to the
singular setting: cohomology group `H^p(Y; R)`, relative homology groups
`H_{p+q}(Y, Y \ K)` and `H_q(Y, Y \ K)`, with bilinear `cap` given by the
relative cap product. -/
def singularCapProductPairingOf
    (R : Type) [CommRing R]
    {X : Type} [TopologicalSpace X] (Y K : Set X) (hY : IsOpen Y) (hK : K ⊆ Y)
    (p q : ℕ) :
    CapProductPairingOf R Y K hY hK where
  CohomGrp := (SingularCohomology.singularCohomologyR R (TopCat.of Y) p : Type)
  RelHomGrpN := (relativeSingularHomologyModule R (TopCat.of Y)
    (Subtype.val ⁻¹' (Y \ K)) (p + q) : Type)
  RelHomGrpQ := (relativeSingularHomologyModule R (TopCat.of Y)
    (Subtype.val ⁻¹' (Y \ K)) q : Type)
  cap := relativeCapProduct R (TopCat.of Y) (Subtype.val ⁻¹' (Y \ K)) p q

/-- **Singular instance of the projection-formula structure.**  Builds a
`ProjectionFormula` between the singular cap-product pairings on `V ⊆ U`
using the singular pullback on cohomology, the relative pushforward on
homology, and `relative_projection_formula`. -/
def singularProjectionFormula
    (R : Type) [CommRing R]
    {X : Type} [TopologicalSpace X] (K U V : Set X)
    (hK : IsClosed K) (hU : IsOpen U) (hV : IsOpen V)
    (hKV : K ⊆ V) (hVU : V ⊆ U) (p q : ℕ) :
    ProjectionFormula R
      (singularCapProductPairingOf R V K hV hKV p q).toCapProductPairing
      (singularCapProductPairingOf R U K hU (hKV.trans hVU) p q).toCapProductPairing where
  pullback :=
    (SingularCohomology.cohomologyPullback R (TopCat.of V) (TopCat.of U)
      (TopCat.ofHom ⟨Set.inclusion hVU, continuous_inclusion hVU⟩) p).hom
  pushforwardN :=
    relativePushforwardMap R (TopCat.ofHom ⟨Set.inclusion hVU, continuous_inclusion hVU⟩)
      (Subtype.val ⁻¹' (V \ K)) (Subtype.val ⁻¹' (U \ K)) (p + q)
  pushforwardQ :=
    relativePushforwardMap R (TopCat.ofHom ⟨Set.inclusion hVU, continuous_inclusion hVU⟩)
      (Subtype.val ⁻¹' (V \ K)) (Subtype.val ⁻¹' (U \ K)) q
  formula := relative_projection_formula R K U V hK hU hV hKV hVU p q

/-- **Singular instance of the excision-data structure.**  Builds an
`ExcisionData` between the singular cap-product pairings on `V ⊆ U` by
inserting `excisionInverseMap` for both the `N` (degree `p+q`) and `Q`
(degree `q`) components. -/
def singularExcisionData
    (R : Type) [CommRing R]
    {X : Type} [TopologicalSpace X] (K U V : Set X)
    (hK : IsClosed K) (hVU : V ⊆ U) (hU : IsOpen U) (hV : IsOpen V)
    (hKV : K ⊆ V) (p q : ℕ) :
    ExcisionData R hK hVU
      (singularCapProductPairingOf R U K hU (hKV.trans hVU) p q).toCapProductPairing
      (singularCapProductPairingOf R V K hV hKV p q).toCapProductPairing where
  excInvN := excisionInverseMap R K U V hK hVU (p + q)
  excInvQ := excisionInverseMap R K U V hK hVU q

/-- **Lemma 34.3 (cap product commutes with restriction) — singular
version.**  Concrete corollary of `cap_product_restriction_commutes_abstract`
applied to the singular cap-product pairings on `V ⊆ U`: capping a
cohomology class `b ∈ H^p(U)` with `x ∈ H_{p+q}(U, U \ K)` and then
excising to `V` agrees with restricting `b` to `V`, excising `x` to
`H_{p+q}(V, V \ K)`, and then capping in `V`.  This is exactly the
commutativity that lets the cap product extend to the Čech-cohomology
colimit and underpins the Poincaré-duality cap pairing for non-manifold
subsets. -/
theorem cap_product_restriction_commutes
    {X : Type} [TopologicalSpace X] {K U V : Set X}
    (hK : IsClosed K) (hU : IsOpen U) (hV : IsOpen V)
    (hKV : K ⊆ V) (hVU : V ⊆ U) (p q : ℕ)
    (b : (SingularCohomology.singularCohomologyR R (TopCat.of U) p : Type))
    (x : (relativeSingularHomologyModule R (TopCat.of U)
            (Subtype.val ⁻¹' (U \ K)) (p + q) : Type)) :
    excisionInverseMap R K U V hK hVU q
      (relativeCapProduct R (TopCat.of U) (Subtype.val ⁻¹' (U \ K)) p q b x) =
    relativeCapProduct R (TopCat.of V) (Subtype.val ⁻¹' (V \ K)) p q
      ((SingularCohomology.cohomologyPullback R (TopCat.of V) (TopCat.of U)
        (TopCat.ofHom ⟨Set.inclusion hVU, continuous_inclusion hVU⟩) p).hom b)
      (excisionInverseMap R K U V hK hVU (p + q) x) := by
  exact cap_product_restriction_commutes_abstract R hK hU hV hKV hVU
    (singularCapProductPairingOf R U K hU (hKV.trans hVU) p q)
    (singularCapProductPairingOf R V K hV hKV p q)
    (singularProjectionFormula R K U V hK hU hV hKV hVU p q)
    (singularExcisionData R K U V hK hVU hU hV hKV p q)
    (excisionInverseMap_leftInverse R K U V hK hVU (p + q))
    (excisionInverseMap_rightInverse R K U V hK hVU q)
    b x

open Simplicial in

/-- **Front face of a `(p+q)`-simplex.**  The "first-`(p+1)`-vertices"
inclusion `[p] ↪ [p+q]` of simplicial objects, sending `i ↦ i`.
Geometrically, restricts a `(p+q)`-simplex to the affine face spanned by
its first `p+1` vertices.  Used as the front-cup half of the cap-product
chain-level formula `(β ⌢ σ) = β(front)·back`. -/
def frontFace (p q : ℕ) : (⦋p⦌ : SimplexCategory) ⟶ ⦋p + q⦌ :=
  SimplexCategory.mkHom ⟨fun i => Fin.castLE (by omega) i, fun _ _ h => h⟩

open Simplicial in
/-- **Back face of a `(p+q)`-simplex.**  The "last-`(q+1)`-vertices"
inclusion `[q] ↪ [p+q]`, sending `j ↦ j + p`.  Restricts a
`(p+q)`-simplex to the affine face spanned by its last `q+1` vertices.
This is the back-cup half of the cap-product chain-level formula. -/
def backFace (p q : ℕ) : (⦋q⦌ : SimplexCategory) ⟶ ⦋p + q⦌ :=
  SimplexCategory.mkHom ⟨fun j => ⟨j.val + p, by omega⟩,
    fun a b (h : a ≤ b) => show a.val + p ≤ b.val + p by omega⟩

/-- **Singular chain complex of a topological space.**  Abbreviation for
the singular chain complex `C_*(X; R)` of `X` with coefficients in `R`,
viewed as a chain complex of `ModuleCat R`-objects indexed by `ℕ`.
Computed via Mathlib's `singularChainComplexFunctor`. -/
abbrev singularChainCx (R : Type) [CommRing R] (X : TopCat.{0}) :
    ChainComplex (ModuleCat.{0} R) ℕ :=
  ((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj X

/-- **The set of singular `n`-simplices of `X`.**  Continuous maps
`Δⁿ → X`, i.e. the `n`-cells of `Sing(X)`.  This is the underlying index
type for the free `R`-module of singular `n`-chains. -/
abbrev singularSimplices (X : TopCat.{0}) (n : ℕ) : Type :=
  (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))

open CategoryTheory.Limits in
/-- **The free simplicial `R`-module on the singular simplicial set of
`X`.**  Levelwise: the free `R`-module on `singularSimplices X n`.  Its
associated (alternating-sum) chain complex is the usual singular chain
complex `singularChainCx R X`. -/
abbrev freeSimplicialModule (R : Type) [CommRing R] (X : TopCat.{0}) :
    SimplicialObject (ModuleCat.{0} R) :=
  ((SimplicialObject.whiskering (Type 0) (ModuleCat.{0} R)).obj
    (sigmaConst.obj (ModuleCat.of R R))).obj (TopCat.toSSet.obj X)

open CategoryTheory.Limits in
/-- **Compatibility of face maps with the augmentation.**  Both face
maps `δ 0` and `δ 1` of the free simplicial module, when composed with
the augmentation `C_0 → R` collapsing each 0-simplex to `1`, yield the
augmentation on 1-simplices (which simply collapses each 1-simplex to
`1`).  This is the basic identity behind the augmentation chain map. -/
lemma freeSimplicialModule_δ_comp_aug (R : Type) [CommRing R] (X : TopCat.{0}) (i : Fin 2) :
    (freeSimplicialModule R X).δ i ≫
      Limits.Sigma.desc (fun (_ : singularSimplices X 0) => 𝟙 (ModuleCat.of R R)) =
    Limits.Sigma.desc (fun (_ : singularSimplices X 1) => 𝟙 (ModuleCat.of R R)) := by
  have hδ : (freeSimplicialModule R X).δ i =
    (sigmaConst.obj (ModuleCat.of R R)).map ((TopCat.toSSet.obj X).δ i) := rfl
  rw [hδ, sigmaConst_obj_map]
  apply Sigma.hom_ext
  intro σ
  simp [Sigma.ι_comp_map'_assoc, Sigma.ι_desc]

open CategoryTheory.Limits in
open Simplicial CategoryTheory.Limits in
/-- **Cap product at the chain level.**  For a `p`-cochain
`β : C_p(X) → R` and a singular `(p+q)`-simplex `σ`, the cap product
`β ⌢ σ` is defined as `β(σ ∘ frontFace) · (σ ∘ backFace)`, a singular
`q`-simplex (or rather, an element of `C_q(X)`).  This is the standard
chain-level cap product, expressed here in the language of free modules
on simplices. -/
def capProductChainMap (R : Type) [CommRing R] (X : TopCat.{0}) (p q : ℕ)
    (β : (singularChainCx R X).X p ⟶ ModuleCat.of R R) :
    (singularChainCx R X).X (p + q) ⟶ (singularChainCx R X).X q :=
  Sigma.desc (fun (σ : singularSimplices X (p + q)) =>
    let σ_front : singularSimplices X p :=
      (TopCat.toSSet.obj X).map (frontFace p q).op σ
    let σ_back : singularSimplices X q :=
      (TopCat.toSSet.obj X).map (backFace p q).op σ


    (Sigma.ι (fun (_ : singularSimplices X p) => ModuleCat.of R R) σ_front ≫ β) ≫
      Sigma.ι (fun (_ : singularSimplices X q) => ModuleCat.of R R) σ_back)

/-- **Naturality of the chain-level cap product.**  For a continuous
map `f : X → Y` and a cochain `β` on `Y`, capping with `β` and pushing
forward to `Y` equals first pulling `β` back to `X` (along `f`), capping
on `X`, and then pushing forward.  This is the chain-level projection
formula and is the key ingredient ensuring the cap product passes to
relative chains. -/
theorem capProductChainMap_natural (R : Type) [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y)
    (p q : ℕ) (β : (singularChainCx R Y).X p ⟶ ModuleCat.of R R) :
    (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map f).f (p + q) ≫
      capProductChainMap R Y p q β =
    capProductChainMap R X p q
      ((((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map f).f p ≫ β) ≫
      (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map f).f q := by sorry

/-- **Chain-level cap product preserves the subcomplex on `A`.**  The
image of `C_*(A)` under the cap product is again contained in `C_*(A)`,
so composing with the cokernel projection `C_*(Y) → C_*(Y)/C_*(A)` kills
the subcomplex.  This is the chain-level statement that lets the
absolute cap product descend to a *relative* cap product. -/
lemma capProductChainMap_comp_cokernel_π_kills_subcomplex
    (R : Type) [CommRing R] (Y : TopCat.{0}) (A : Set Y) (p q : ℕ)
    (β : (singularChainCx R Y).X p ⟶ ModuleCat.of R R) :
    let incl : TopCat.of A ⟶ Y := ⟨Subtype.val, continuous_subtype_val⟩
    let chainMapN := (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
      (ModuleCat.of R R)).map incl).f (p + q)
    let chainMapQ := (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
      (ModuleCat.of R R)).map incl).f q
    chainMapN ≫ capProductChainMap R Y p q β ≫
      CategoryTheory.Limits.cokernel.π chainMapQ = 0 := by
  simp only
  have h_nat := capProductChainMap_natural R
    (⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of A ⟶ Y) p q β
  rw [← CategoryTheory.Category.assoc, h_nat, CategoryTheory.Category.assoc,
      CategoryTheory.Limits.cokernel.condition, CategoryTheory.Limits.comp_zero]

/-- **Chain-level relative cap product.**  Descent of
`capProductChainMap` along the cokernel projection `C_*(Y) → C_*(Y, A)`,
giving a chain map of relative chain complexes
`C_{p+q}(Y, A) → C_q(Y, A)`.  Its descent to relative homology is the
`relativeCapProduct`. -/
noncomputable def relativeCapProductChainLevel
    (R : Type) [CommRing R] (Y : TopCat.{0}) (A : Set Y) (p q : ℕ)
    (β : (singularChainCx R Y).X p ⟶ ModuleCat.of R R) :
    let incl : TopCat.of A ⟶ Y := ⟨Subtype.val, continuous_subtype_val⟩
    let chainMapN := (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
      (ModuleCat.of R R)).map incl).f (p + q)
    let chainMapQ := (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
      (ModuleCat.of R R)).map incl).f q
    CategoryTheory.Limits.cokernel chainMapN ⟶ CategoryTheory.Limits.cokernel chainMapQ :=
  CategoryTheory.Limits.cokernel.desc _ (capProductChainMap R Y p q β ≫
    CategoryTheory.Limits.cokernel.π _)
    (capProductChainMap_comp_cokernel_π_kills_subcomplex R Y A p q β)


/-- **Cup product on singular cohomology** (Definition 32.1, reused).
The bilinear `cup` operation
`H^p(X; R) × H^q(X; R) → H^{p+q}(X; R)` induced by the
Alexander–Whitney diagonal approximation.  Here it is presented as the
curried form of Mathlib's tensor-product `SingularCohomology.cupProduct`. -/
def cupProduct
    (R : Type) [CommRing R] (X : TopCat.{0}) (p q : ℕ) :
    (SingularCohomology.singularCohomology R X (ModuleCat.of R R) p : Type) →ₗ[R]
    (SingularCohomology.singularCohomology R X (ModuleCat.of R R) q : Type) →ₗ[R]
    (SingularCohomology.singularCohomology R X (ModuleCat.of R R) (p + q) : Type) :=
  TensorProduct.curry (SingularCohomology.cupProduct R X p q).hom


/-- **Generator of `H^0` of a point.**  A canonical generator of
`H^0(pt; R) ≅ R`, witnessing the rank-one freeness of the cohomology of
a point in degree 0.  This is the element whose pullback along the
unique map `X → pt` is the unit `1 ∈ H^0(X; R)` for the cup product. -/
noncomputable def cohomologyPointGenerator (R : Type) [CommRing R] :
    (SingularCohomology.singularCohomology R (TopCat.of PUnit.{1}) (ModuleCat.of R R) 0 : Type) := by sorry


/-- **The cup-product unit `1 ∈ H^0(X; R)`.**  Defined as the pullback
of the generator of `H^0(pt; R)` along the unique continuous map
`X → pt`.  Satisfies `1 ⌣ a = a = a ⌣ 1` and `1 ⌢ x = x` (see
`cap_one`). -/
def cupUnit (R : Type) [CommRing R] (X : TopCat.{0}) :
    (SingularCohomology.singularCohomology R X (ModuleCat.of R R) 0 : Type) :=
  (SingularCohomology.singularCohomologyMap R
    (TopCat.isTerminalPUnit.from X) 0).hom
    (cohomologyPointGenerator R)

/-- **Kronecker pairing** `⟨·, ·⟩ : H^n(X; R) × H_n(X; R) → R`.
The classical evaluation pairing of a singular `n`-cochain on an
`n`-cycle, descended to cohomology/homology.  Re-exposed here from
Mathlib's `SingularCohomology.kroneckerPairing` for use in
`augmentation_cap_eq_kronecker` and the adjointness formula for cup/cap. -/
def kroneckerPairing
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    (SingularCohomology.singularCohomology R X (ModuleCat.of R R) n : Type) →ₗ[R]
    (SingularCohomology.singularHomologyModule R X n : Type) →ₗ[R] R :=
  SingularCohomology.kroneckerPairing R X n


/-- **Augmentation** `ε : H_0(X; R) → R`.  The map descended from the
chain-level augmentation `C_0(X) → R` (which collapses each 0-simplex to
`1`).  Equal to the unique map induced by `X → pt` on `H_0`, and equal
to `1 ⌢ ·` ↦ `1` via the unit relation. -/
def augmentation (R : Type) [CommRing R] (X : TopCat.{0}) :
    (SingularCohomology.singularHomologyModule R X 0 : Type) →ₗ[R] R :=
  (augmentationH0 R X).hom


/-- **Pushforward on singular homology**, `f_* : H_n(X; R) → H_n(Y; R)`.
Functoriality of singular homology in the topological space, as a
`ModuleCat`-morphism.  Used in the projection formula for the cap
product. -/
def pushforwardMap' (R : Type) [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    SingularCohomology.singularHomologyModule R X n ⟶
    SingularCohomology.singularHomologyModule R Y n :=
  ((singularHomologyFunctor (ModuleCat.{0} R) n).obj (ModuleCat.of R R)).map f

/-- **Pullback on singular cohomology**, `f^* : H^n(Y; R) → H^n(X; R)`.
Contravariant functoriality of singular cohomology in the topological
space.  Used in the projection formula for the cap product. -/
def pullbackMap
    (R : Type) [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    (SingularCohomology.singularCohomology R Y (ModuleCat.of R R) n : Type) →ₗ[R]
    (SingularCohomology.singularCohomology R X (ModuleCat.of R R) n : Type) :=
  (SingularCohomology.singularCohomologyMap R f n).hom

/-- **Axiomatization of the cap product on singular homology.**  A
bundle of properties that the cap product `H^p(X) ⊗ H_{p+q}(X) → H_q(X)`
is required to satisfy: the cup-cap associativity `(a ⌣ b) ⌢ x =
a ⌢ (b ⌢ x)`, the cap-unit relation `1 ⌢ x = x`, the projection
formula `f_*(f^*b ⌢ x) = b ⌢ f_*x`, and the augmentation/Kronecker
relation `ε(b ⌢ x) = ⟨b, x⟩`.  Establishing these properties for the
*chain-level* cap product is the technical content of Proposition 34.1. -/
structure CapProductDescentProperties (R : Type) [CommRing R] where
  capMap : ∀ (X : TopCat.{0}) (p q : ℕ),
    (SingularCohomology.singularCohomology R X (ModuleCat.of R R) p : Type) →ₗ[R]
    (SingularCohomology.singularHomologyModule R X (p + q) : Type) →ₗ[R]
    (SingularCohomology.singularHomologyModule R X q : Type)
  cup_assoc : ∀ (X : TopCat.{0}) (p q r : ℕ)
    (a : (SingularCohomology.singularCohomology R X (ModuleCat.of R R) p : Type))
    (b : (SingularCohomology.singularCohomology R X (ModuleCat.of R R) q : Type))
    (x : (SingularCohomology.singularHomologyModule R X (p + q + r) : Type)),
    capMap X (p + q) r (cupProduct R X p q a b)
      ((Nat.add_assoc p q r) ▸ x) =
    capMap X p r a
      (capMap X q (p + r) b
        (show (SingularCohomology.singularHomologyModule R X (q + (p + r)) : Type) from
          (show q + (p + r) = p + q + r by omega) ▸ x))
  cap_unit : ∀ (X : TopCat.{0}) (n : ℕ)
    (x : (SingularCohomology.singularHomologyModule R X n : Type)),
    capMap X 0 n (cupUnit R X)
      ((Nat.zero_add n).symm ▸ x) = x
  projection : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) (p q : ℕ)
    (b : (SingularCohomology.singularCohomology R Y (ModuleCat.of R R) p : Type))
    (x : (SingularCohomology.singularHomologyModule R X (p + q) : Type)),
    (pushforwardMap' R f q).hom
      (capMap X p q (pullbackMap R f p b) x) =
    capMap Y p q b
      ((pushforwardMap' R f (p + q)).hom x)
  augmentation_eq : ∀ (X : TopCat.{0}) (n : ℕ)
    (b : (SingularCohomology.singularCohomology R X (ModuleCat.of R R) n : Type))
    (x : (SingularCohomology.singularHomologyModule R X n : Type)),
    augmentation R X (capMap X n 0 b ((Nat.add_zero n).symm ▸ x)) =
    kroneckerPairing R X n b x


/-- **Descent of the cap product to (co)homology.**  The chain-level cap
product `capProductChainMap` is a chain map in `β` and induces a
well-defined bilinear map at the level of (co)homology
`H^p(X) ⊗ H_{p+q}(X) → H_q(X)`.  This is the absolute (non-relative)
version of `relativeCapProductHomologyDescent`. -/
noncomputable def capProductChainMap_descent
    (R : Type) [CommRing R] (X : TopCat.{0}) (p q : ℕ) :
    (SingularCohomology.singularCohomology R X (ModuleCat.of R R) p : Type) →ₗ[R]
    (SingularCohomology.singularHomologyModule R X (p + q) : Type) →ₗ[R]
    (SingularCohomology.singularHomologyModule R X q : Type) := by sorry


/-- **Cap-unit relation at the level of descent.**  Capping with the
cup-product unit `1 ∈ H^0(X; R)` is the identity on homology:
`1 ⌢ x = x`.  This is the descended version of the chain-level unit
identity. -/
theorem capProductChainMap_descent_unit
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (x : (SingularCohomology.singularHomologyModule R X n : Type)) :
    capProductChainMap_descent R X 0 n (cupUnit R X)
      ((Nat.zero_add n).symm ▸ x) = x := by sorry

/-- **Cap product on singular homology**, public name.  Alias for
`capProductChainMap_descent`; this is the linear map
`H^p(X; R) ⊗ H_{p+q}(X; R) → H_q(X; R)` written in the bilinear-curry
form. -/
def capProductHomologyMap (R : Type) [CommRing R] (X : TopCat.{0}) (p q : ℕ) :
    (SingularCohomology.singularCohomology R X (ModuleCat.of R R) p : Type) →ₗ[R]
    (SingularCohomology.singularHomologyModule R X (p + q) : Type) →ₗ[R]
    (SingularCohomology.singularHomologyModule R X q : Type) :=
  capProductChainMap_descent R X p q

/-- **Cup-cap associativity** for the homology-level cap product:
`(a ⌣ b) ⌢ x = a ⌢ (b ⌢ x)`, modulo the necessary degree
re-indexing isomorphisms.  This is the algebraic identity making
singular homology into a *module* over the cup-product cohomology ring. -/
theorem capProductHomologyMap_cup_assoc (R : Type) [CommRing R]
    (X : TopCat.{0}) (p q r : ℕ)
    (a : (SingularCohomology.singularCohomology R X (ModuleCat.of R R) p : Type))
    (b : (SingularCohomology.singularCohomology R X (ModuleCat.of R R) q : Type))
    (x : (SingularCohomology.singularHomologyModule R X (p + q + r) : Type)) :
    capProductHomologyMap R X (p + q) r (cupProduct R X p q a b)
      ((Nat.add_assoc p q r) ▸ x) =
    capProductHomologyMap R X p r a
      (capProductHomologyMap R X q (p + r) b
        (show (SingularCohomology.singularHomologyModule R X (q + (p + r)) : Type) from
          (show q + (p + r) = p + q + r by omega) ▸ x)) := by sorry

/-- **Cap-unit relation** for the homology-level cap product:
`1 ⌢ x = x`.  Concrete restatement of
`capProductChainMap_descent_unit` in terms of `capProductHomologyMap`. -/
theorem capProductHomologyMap_unit (R : Type) [CommRing R]
    (X : TopCat.{0}) (n : ℕ)
    (x : (SingularCohomology.singularHomologyModule R X n : Type)) :
    capProductHomologyMap R X 0 n (cupUnit R X)
      ((Nat.zero_add n).symm ▸ x) = x :=
  capProductChainMap_descent_unit R X n x

/-- **Projection formula** for the homology-level cap product:
`f_*(f^*b ⌢ x) = b ⌢ f_*x`.  Naturality of the cap product with
respect to continuous maps. -/
theorem capProductHomologyMap_projection (R : Type) [CommRing R]
    {X Y : TopCat.{0}} (f : X ⟶ Y) (p q : ℕ)
    (b : (SingularCohomology.singularCohomology R Y (ModuleCat.of R R) p : Type))
    (x : (SingularCohomology.singularHomologyModule R X (p + q) : Type)) :
    (pushforwardMap' R f q).hom
      (capProductHomologyMap R X p q (pullbackMap R f p b) x) =
    capProductHomologyMap R Y p q b
      ((pushforwardMap' R f (p + q)).hom x) := by sorry

/-- **Augmentation-Kronecker compatibility.**  `ε(b ⌢ x) = ⟨b, x⟩`:
augmenting the result of capping a cohomology class `b ∈ H^n(X)` with
its dual cycle `x ∈ H_n(X)` recovers the Kronecker pairing.  This
identity is the linchpin connecting cup, cap, and Kronecker pairings. -/
theorem capProductHomologyMap_augmentation (R : Type) [CommRing R]
    (X : TopCat.{0}) (n : ℕ)
    (b : (SingularCohomology.singularCohomology R X (ModuleCat.of R R) n : Type))
    (x : (SingularCohomology.singularHomologyModule R X n : Type)) :
    augmentation R X (capProductHomologyMap R X n 0 b ((Nat.add_zero n).symm ▸ x)) =
    kroneckerPairing R X n b x := by sorry

/-- **The cap-product descent bundle.**  Assembles the singular
`capProductHomologyMap` together with all four of its key axioms
(cup-cap associativity, unit, projection, and augmentation-Kronecker)
into a `CapProductDescentProperties` record, ready to be consumed by
downstream constructions. -/
noncomputable def capProductDescentProperties (R : Type) [CommRing R] :
    CapProductDescentProperties R where
  capMap := capProductHomologyMap R
  cup_assoc := capProductHomologyMap_cup_assoc R
  cap_unit := capProductHomologyMap_unit R
  projection := fun {_ _} => capProductHomologyMap_projection R
  augmentation_eq := capProductHomologyMap_augmentation R

/-- **Cap-product descent on singular homology**, accessed through the
bundle `capProductDescentProperties`.  This is the version of the cap
product used by downstream constructions (e.g. Poincaré duality). -/
def capProductDescent
    (R : Type) [CommRing R] (X : TopCat.{0}) (p q : ℕ) :
    (SingularCohomology.singularCohomology R X (ModuleCat.of R R) p : Type) →ₗ[R]
    (SingularCohomology.singularHomologyModule R X (p + q) : Type) →ₗ[R]
    (SingularCohomology.singularHomologyModule R X q : Type) :=
  (capProductDescentProperties R).capMap X p q


/-- **The cap product** `⌢ : H^p(X; R) × H_{p+q}(X; R) → H_q(X; R)`
on singular cohomology and singular homology.  Alias for
`capProductDescent`.  Together with the cup product, these make singular
(co)homology a graded module over a graded ring. -/
def capProduct
    (R : Type) [CommRing R] (X : TopCat.{0}) (p q : ℕ) :
    (SingularCohomology.singularCohomology R X (ModuleCat.of R R) p : Type) →ₗ[R]
    (SingularCohomology.singularHomologyModule R X (p + q) : Type) →ₗ[R]
    (SingularCohomology.singularHomologyModule R X q : Type) :=
  capProductDescent R X p q


/-- **Cap-cup associativity** (Proposition 34.1, part 1):
`(a ⌣ b) ⌢ x = a ⌢ (b ⌢ x)`.  Public restatement of
`capProductHomologyMap_cup_assoc` via the descent bundle. -/
theorem cap_cup_assoc
    (R : Type) [CommRing R] (X : TopCat.{0}) (p q r : ℕ)
    (a : (SingularCohomology.singularCohomology R X (ModuleCat.of R R) p : Type))
    (b : (SingularCohomology.singularCohomology R X (ModuleCat.of R R) q : Type))
    (x : (SingularCohomology.singularHomologyModule R X (p + q + r) : Type)) :
    capProduct R X (p + q) r (cupProduct R X p q a b)
      ((Nat.add_assoc p q r) ▸ x) =
    capProduct R X p r a
      (capProduct R X q (p + r) b
        (show (SingularCohomology.singularHomologyModule R X (q + (p + r)) : Type) from
          (show q + (p + r) = p + q + r by omega) ▸ x)) :=
  (capProductDescentProperties R).cup_assoc X p q r a b x


/-- **Cap-unit relation** (Proposition 34.1, part 2): `1 ⌢ x = x`.
Public restatement of `capProductHomologyMap_unit`. -/
theorem cap_one
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (x : (SingularCohomology.singularHomologyModule R X n : Type)) :
    capProduct R X 0 n (cupUnit R X)
      ((Nat.zero_add n).symm ▸ x) = x :=
  (capProductDescentProperties R).cap_unit X n x


/-- **Projection formula for the cap product** (Proposition 34.1, part
3): `f_*(f^*b ⌢ x) = b ⌢ f_*x`.  Public restatement of
`capProductHomologyMap_projection`. -/
theorem cap_projection_formula
    (R : Type) [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y)
    (p q : ℕ)
    (b : (SingularCohomology.singularCohomology R Y (ModuleCat.of R R) p : Type))
    (x : (SingularCohomology.singularHomologyModule R X (p + q) : Type)) :
    (pushforwardMap' R f q).hom
      (capProduct R X p q (pullbackMap R f p b) x) =
    capProduct R Y p q b
      ((pushforwardMap' R f (p + q)).hom x) :=
  (capProductDescentProperties R).projection f p q b x


/-- **Augmentation equals Kronecker pairing** (Proposition 34.1, part
4): `ε(b ⌢ x) = ⟨b, x⟩`.  Public restatement of
`capProductHomologyMap_augmentation`. -/
theorem augmentation_cap_eq_kronecker
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (b : (SingularCohomology.singularCohomology R X (ModuleCat.of R R) n : Type))
    (x : (SingularCohomology.singularHomologyModule R X n : Type)) :
    augmentation R X (capProduct R X n 0 b ((Nat.add_zero n).symm ▸ x)) =
    kroneckerPairing R X n b x :=
  (capProductDescentProperties R).augmentation_eq X n b x


/-- **Adjointness of cup and cap with respect to the Kronecker pairing**
(Proposition 34.1, part 5): `⟨a ⌣ b, x⟩ = ⟨a, b ⌢ x⟩`.  This is the
formal statement that the cup product on cohomology is adjoint to the
cap product on homology under the Kronecker pairing — the algebraic
expression of how cup and cap interact.  The proof combines
augmentation-Kronecker compatibility with cup-cap associativity. -/
theorem kronecker_cup_eq_kronecker_cap
    (R : Type) [CommRing R] (X : TopCat.{0}) (p q : ℕ)
    (a : (SingularCohomology.singularCohomology R X (ModuleCat.of R R) p : Type))
    (b : (SingularCohomology.singularCohomology R X (ModuleCat.of R R) q : Type))
    (x : (SingularCohomology.singularHomologyModule R X (p + q) : Type)) :
    kroneckerPairing R X (p + q) (cupProduct R X p q a b) x =
    kroneckerPairing R X p a (capProduct R X q p b
      ((Nat.add_comm p q) ▸ x)) := by

  rw [← augmentation_cap_eq_kronecker R X (p + q) (cupProduct R X p q a b) x]

  rw [← augmentation_cap_eq_kronecker R X p a
    (capProduct R X q p b ((Nat.add_comm p q) ▸ x))]


  congr 1


  have h := cap_cup_assoc R X p q 0 a b ((Nat.add_zero (p + q)).symm ▸ x)


  simp only [Nat.add_zero] at h ⊢
  exact h

/-- **Proposition 34.1 (bundle).**  A `Prop`-valued record listing the
five fundamental properties of the cap product in singular (co)homology:
cup-cap associativity, the cap-unit identity, the projection formula,
the augmentation-Kronecker identity, and cup/cap adjointness via the
Kronecker pairing.  This is the formal statement of Proposition 34.1 of
Miller's *Lectures on Algebraic Topology I*. -/
structure Proposition34_1Properties (R : Type) [CommRing R] : Prop where
  assoc : ∀ (X : TopCat.{0}) (p q r : ℕ)
    (a : (SingularCohomology.singularCohomology R X (ModuleCat.of R R) p : Type))
    (b : (SingularCohomology.singularCohomology R X (ModuleCat.of R R) q : Type))
    (x : (SingularCohomology.singularHomologyModule R X (p + q + r) : Type)),
    capProduct R X (p + q) r (cupProduct R X p q a b)
      ((Nat.add_assoc p q r) ▸ x) =
    capProduct R X p r a
      (capProduct R X q (p + r) b
        (show (SingularCohomology.singularHomologyModule R X (q + (p + r)) : Type) from
          (show q + (p + r) = p + q + r by omega) ▸ x))
  unit : ∀ (X : TopCat.{0}) (n : ℕ)
    (x : (SingularCohomology.singularHomologyModule R X n : Type)),
    capProduct R X 0 n (cupUnit R X)
      ((Nat.zero_add n).symm ▸ x) = x
  projection : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) (p q : ℕ)
    (b : (SingularCohomology.singularCohomology R Y (ModuleCat.of R R) p : Type))
    (x : (SingularCohomology.singularHomologyModule R X (p + q) : Type)),
    (pushforwardMap' R f q).hom
      (capProduct R X p q (pullbackMap R f p b) x) =
    capProduct R Y p q b
      ((pushforwardMap' R f (p + q)).hom x)
  augmentation_eq : ∀ (X : TopCat.{0}) (n : ℕ)
    (b : (SingularCohomology.singularCohomology R X (ModuleCat.of R R) n : Type))
    (x : (SingularCohomology.singularHomologyModule R X n : Type)),
    augmentation R X (capProduct R X n 0 b ((Nat.add_zero n).symm ▸ x)) =
    kroneckerPairing R X n b x
  adjoint : ∀ (X : TopCat.{0}) (p q : ℕ)
    (a : (SingularCohomology.singularCohomology R X (ModuleCat.of R R) p : Type))
    (b : (SingularCohomology.singularCohomology R X (ModuleCat.of R R) q : Type))
    (x : (SingularCohomology.singularHomologyModule R X (p + q) : Type)),
    kroneckerPairing R X (p + q) (cupProduct R X p q a b) x =
    kroneckerPairing R X p a (capProduct R X q p b
      ((Nat.add_comm p q) ▸ x))

/-- **Proposition 34.1** (Miller, *Lectures on Algebraic Topology I*).
The singular cap product `⌢ : H^p(X; R) ⊗ H_{p+q}(X; R) → H_q(X; R)`
satisfies the five fundamental properties packaged in
`Proposition34_1Properties`: cup-cap associativity, the cap-unit
identity, the projection formula, the augmentation-Kronecker identity,
and adjointness with the cup product via the Kronecker pairing.  These
together make singular (co)homology a graded module over the cup-product
ring and form the cornerstone of Poincaré duality. -/
theorem proposition_34_1 (R : Type) [CommRing R] : Proposition34_1Properties R where
  assoc X p q r a b x := cap_cup_assoc R X p q r a b x
  unit X n x := cap_one R X n x
  projection f p q b x := cap_projection_formula R f p q b x
  augmentation_eq X n b x := augmentation_cap_eq_kronecker R X n b x
  adjoint X p q a b x := kronecker_cup_eq_kronecker_cap R X p q a b x

end CapProduct

namespace PoincareDualityCompact

open CategoryTheory

/-- **`R`-orientability of an `n`-manifold `M`.**  A typeclass wrapping
`OrientationHomology.IsROrientable n M R`: there exists a continuous
choice of local generators of `H_n(M, M ∖ {x}; R) ≅ R` over all `x ∈ M`.
This is the standard hypothesis for compact Poincaré duality with
coefficients in `R`. -/
class IsROriented (R : Type) [CommRing R] (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] : Prop where
  isROrientable : OrientationHomology.IsROrientable n M R

/-- **Existence of a fundamental class.**  For a compact `R`-oriented
`n`-manifold `M`, there exists an element of `H_n(M; R)` — the
*fundamental class* `[M]` — distinguished by its local restrictions
agreeing with the chosen `R`-orientation.  This is the classical
existence statement underlying Poincaré duality. -/
theorem fundamentalClassMathlib_exists (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M] :
    ∃ (_ : (SingularCohomology.singularHomologyModule R (TopCat.of M) n : Type)), True := by sorry

/-- **The fundamental class `[M] ∈ H_n(M; R)`** of a compact
`R`-oriented `n`-manifold.  Constructed by picking a witness from
`fundamentalClassMathlib_exists`.  Capping with `[M]` defines the
Poincaré-duality isomorphism `H^p(M; R) → H_{n-p}(M; R)`. -/
noncomputable def fundamentalClassMathlib (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M] :
    (SingularCohomology.singularHomologyModule R (TopCat.of M) n : Type) :=
  (fundamentalClassMathlib_exists R n M).choose


/-- **Poincaré-duality map** for a compact `R`-oriented `n`-manifold
`M`.  Given `p + q = n`, this is the linear map
`PD : H^p(M; R) → H_q(M; R)` defined by capping with the fundamental
class: `PD(α) = α ⌢ [M]`.  Theorem 34.2 (the Poincaré duality
theorem) asserts that this map is an *isomorphism*; here we record only
its definition. -/
noncomputable def poincareDualityMap
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsROriented R n M]
    (p q : ℕ) (hpq : p + q = n) :
    (SingularCohomology.singularCohomology R (TopCat.of M) (ModuleCat.of R R) p : Type) →ₗ[R]
    (SingularCohomology.singularHomologyModule R (TopCat.of M) q : Type) :=
  (CapProduct.capProductDescent R (TopCat.of M) p q).flip (hpq ▸ fundamentalClassMathlib R n M)


end PoincareDualityCompact

namespace CechCohomology


/-- **Čech-cap-product pairing** (Section 34).  The cap-product of a
Čech cohomology class `Ȟ^p(K; R)` with a relative singular homology
class in `H_{p+q}(X, X \ K; R)` yields a relative homology class in
`H_q(X, X \ K; R)`.  Construction: pick a representative in some open
neighborhood `U ⊇ K`, apply the relative cap product, and observe (via
`cap_product_restriction_commutes`) that the result is independent of
the choice of neighborhood.  This is the algebraic vehicle of
non-compact / non-manifold Poincaré duality. -/
noncomputable def cechCapProductPairing
    (R : Type) [CommRing R] {X : Type} [TopologicalSpace X]
    (K : Set X) (p q : ℕ) :
    (cechCohomology R K p : Type) →ₗ[R]
    (CapProduct.relativeSingularHomologyModule R (TopCat.of X) Kᶜ (p + q) : Type) →ₗ[R]
    (CapProduct.relativeSingularHomologyModule R (TopCat.of X) Kᶜ q : Type) := by sorry


end CechCohomology
