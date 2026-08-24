/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.Algebra.Category.Grp.Colimits

noncomputable section

open CategoryTheory AlgebraicTopology Limits

namespace BarycentricSubdivision

/-- The singular chain complex functor with integer coefficients, `X ↦ S_*(X; ℤ)`,
as a functor from topological spaces to non-negatively graded chain complexes of
abelian groups. This is the ambient functor on which the subdivision operator acts. -/
abbrev singularChainFunctorZ : TopCat.{0} ⥤ ChainComplex AddCommGrpCat ℕ :=
  (singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)

/-- The barycenter of the standard `n`-simplex `Δ^n`: the point all of whose
barycentric coordinates equal `1/(n+1)`. This is the cone point used in the
subdivision construction of Section 12. -/
def barycenter (n : ℕ) : stdSimplex ℝ (Fin (n + 1)) :=
  ⟨fun _ => 1 / (n + 1 : ℝ), by
    constructor
    · intro i; positivity
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
      push_cast
      ring⟩

/-- Each barycentric coordinate of the barycenter of `Δ^n` is `1/(n+1)`. -/
@[simp]
theorem barycenter_coord (n : ℕ) (i : Fin (n + 1)) :
    (barycenter n).val i = 1 / (n + 1 : ℝ) :=
  rfl

/-- The standard topological `n`-simplex `Δ^n`, viewed as an object of `TopCat`. -/
def stdSimplexTop (n : ℕ) : TopCat.{0} :=
  SimplexCategory.toTop.{0}.obj (SimplexCategory.mk n)

/-- The type of singular `n`-simplices of `X`, i.e. `Sin_n(X)`, accessed via the
underlying simplicial set of `X`. -/
def SingType (X : TopCat.{0}) (n : ℕ) : Type :=
  (TopCat.toSSet.{0}.obj X).obj (Opposite.op (SimplexCategory.mk n))

/-- The chain group `S_n(X; ℤ)` is definitionally the coproduct of copies of `ℤ`
indexed by singular `n`-simplices, exhibiting it as the free abelian group on
`Sin_n(X)` (Definition 1.3). -/
lemma chainGroup_eq_coprod (X : TopCat.{0}) (n : ℕ) :
    (singularChainFunctorZ.obj X).X n =
    ∐ (fun (_ : SingType X n) => AddCommGrpCat.of ℤ) := rfl

/-- The identity map `Δ^n → Δ^n` viewed as a singular `n`-simplex of `Δ^n`. This is
the universal `n`-simplex `ι_n` on which the subdivision construction is built. -/
def identitySimplex (n : ℕ) : SingType (stdSimplexTop n) n :=
  ULift.up (𝟙 (stdSimplexTop n))

/-- The set-level cone construction `b * τ` taking a `(k+1)`-simplex of `Δ^n`. Given
a cone point `b ∈ Δ^n` and a `k`-simplex `τ : Δ^k → Δ^n`, this sends a point
`x = (t₀, t₁, …, t_{k+1})` of `Δ^{k+1}` to the linear interpolation
`t₀ · b + (1 - t₀) · τ(x₁, …, x_{k+1})` after renormalizing the tail. -/
def coneSingularSimplexFun {n k : ℕ} (b : stdSimplex ℝ (Fin (n + 1)))
    (τ : stdSimplexTop k ⟶ stdSimplexTop n)
    (x : ↑(stdSimplexTop (k + 1))) : ↑(stdSimplexTop n) := by
  have hnn := x.down.2.1
  have hsum := x.down.2.2
  let t₀ := x.down.val 0
  have ht₀_le : t₀ ≤ 1 := by
    have h1 : t₀ ≤ ∑ i, x.down.val i :=
      Finset.single_le_sum (f := x.down.val) (fun i _ => hnn i)
        (Finset.mem_univ (0 : Fin (k + 2)))
    linarith [hsum]
  exact if h : t₀ = 1 then ULift.up b
  else
    have ht₀_lt : t₀ < 1 := lt_of_le_of_ne ht₀_le h
    let s := 1 - t₀
    have hs : (0 : ℝ) < s := sub_pos.mpr ht₀_lt
    let normTail : stdSimplex ℝ (Fin (k + 1)) :=
      ⟨fun i => x.down.val (Fin.succ i) / s, by
        refine ⟨fun i => div_nonneg (hnn _) (le_of_lt hs), ?_⟩
        have htail : ∑ i : Fin (k + 1), x.down.val (Fin.succ i) = s := by
          have heq : ∑ i, x.down.val i =
              x.down.val 0 + ∑ i : Fin (k + 1), x.down.val (Fin.succ i) :=
            Fin.sum_univ_succ x.down.val
          linarith [hsum]
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul, htail, mul_inv_cancel₀ (ne_of_gt hs)]⟩
    let τ_applied := (τ.hom' (ULift.up normTail)).down
    ULift.up ⟨fun j => t₀ * b.val j + s * τ_applied.val j, by
      refine ⟨fun j => ?_, ?_⟩
      · apply add_nonneg
        · exact mul_nonneg (hnn 0) (b.2.1 j)
        · exact mul_nonneg (le_of_lt hs) (τ_applied.2.1 j)
      · simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        erw [b.2.2, τ_applied.2.2]
        linarith⟩

/-- The cone map `coneSingularSimplexFun b τ : Δ^{k+1} → Δ^n` is continuous. -/
theorem coneSingularSimplex_continuous {n k : ℕ} (b : stdSimplex ℝ (Fin (n + 1)))
    (τ : stdSimplexTop k ⟶ stdSimplexTop n) :
    Continuous (coneSingularSimplexFun b τ) := by sorry

/-- The cone `b * τ : Δ^{k+1} → Δ^n` of a singular `k`-simplex `τ` of `Δ^n` over the
cone point `b`, as a morphism in `TopCat`. -/
def coneSingularSimplex {n k : ℕ} (b : stdSimplex ℝ (Fin (n + 1)))
    (τ : stdSimplexTop k ⟶ stdSimplexTop n) :
    stdSimplexTop (k + 1) ⟶ stdSimplexTop n :=
  ⟨⟨coneSingularSimplexFun b τ, coneSingularSimplex_continuous b τ⟩⟩

/-- The cone operator `b * (-) : S_k(Δ^n) → S_{k+1}(Δ^n)` sending each generator `τ`
to its cone `b * τ` over the chosen cone point `b ∈ Δ^n`, extended linearly. -/
def coneOperator {n : ℕ} (b : stdSimplex ℝ (Fin (n + 1))) (k : ℕ) :
    (singularChainFunctorZ.obj (stdSimplexTop n)).X k ⟶
    (singularChainFunctorZ.obj (stdSimplexTop n)).X (k + 1) := by
  rw [chainGroup_eq_coprod]
  exact Sigma.desc (fun τ =>
    Sigma.ι (fun (_ : SingType (stdSimplexTop n) (k + 1)) => AddCommGrpCat.of ℤ)
      (ULift.up (coneSingularSimplex b τ.down)))

/-- The chain `1 · σ ∈ S_n(X)` associated to a singular simplex `σ`, viewed as a free
generator in the coproduct representation of the singular chain group. -/
def chainGenerator {X : TopCat.{0}} {n : ℕ} (σ : SingType X n) :
    ↑((singularChainFunctorZ.obj X).X n) :=
  (Sigma.ι (fun (_ : SingType X n) => AddCommGrpCat.of ℤ) σ) (1 : ℤ)

/-- Push forward a chain `elem ∈ S_k(Δ^k)` along a singular `k`-simplex `σ : Δ^k → X`
to obtain a chain in `S_k(X)`. -/
def chainPushforward {X : TopCat.{0}} {k : ℕ}
    (elem : ↑((singularChainFunctorZ.obj (stdSimplexTop k)).X k))
    (σ : SingType X k) :
    ↑((singularChainFunctorZ.obj X).X k) :=
  ((singularChainFunctorZ.map σ.down).f k) elem

/-- Endomorphism of `S_k(X)` built from a chosen element `elem ∈ S_k(Δ^k)`: on each
generator `σ` it returns the pushforward `σ_*(elem)`. This is the abstract pattern
used to define the subdivision operator from its values on the universal simplex. -/
def sdDegreeWithElem {k : ℕ}
    (elem : ↑((singularChainFunctorZ.obj (stdSimplexTop k)).X k))
    (X : TopCat.{0}) :
    (singularChainFunctorZ.obj X).X k ⟶ (singularChainFunctorZ.obj X).X k := by
  rw [chainGroup_eq_coprod]
  exact Sigma.desc (fun σ =>
    AddCommGrpCat.ofHom ((zmultiplesHom _) (chainPushforward elem σ)))

/-- The subdivision `$ι_n ∈ S_n(Δ^n)` of the universal `n`-simplex, defined recursively:
in degree `0` it is the identity simplex, and in degree `n + 1` it is the cone
from the barycenter over the subdivision of the boundary `d ι_{n+1}`. This is the
inductive definition driving the construction of the subdivision operator
of Proposition 12.1. -/
def sdIota_elem : (n : ℕ) → ↑((singularChainFunctorZ.obj (stdSimplexTop n)).X n)
  | 0 => chainGenerator (identitySimplex 0)
  | n + 1 =>
    let idGen := chainGenerator (identitySimplex (n + 1))
    let boundary := ((singularChainFunctorZ.obj (stdSimplexTop (n + 1))).d (n + 1) n) idGen
    let sdBoundary := (sdDegreeWithElem (sdIota_elem n) (stdSimplexTop (n + 1))) boundary
    (coneOperator (barycenter (n + 1)) n) sdBoundary

/-- The subdivision element `$ι_n`, packaged as the group homomorphism `ℤ → S_n(Δ^n)`
sending `1` to `$ι_n`. -/
def sdIotaHom (n : ℕ) :
    AddCommGrpCat.of ℤ ⟶ (singularChainFunctorZ.obj (stdSimplexTop n)).X n :=
  AddCommGrpCat.ofHom
    ((zmultiplesHom ↑((singularChainFunctorZ.obj (stdSimplexTop n)).X n)) (sdIota_elem n))

/-- The component of the subdivision operator on the free generator indexed by `σ`:
it sends the generator to `σ_*($ι_n) ∈ S_n(X)`. -/
def sdSigmaComponent (X : TopCat.{0}) (n : ℕ) (σ : SingType X n) :
    AddCommGrpCat.of ℤ ⟶ (singularChainFunctorZ.obj X).X n :=
  sdIotaHom n ≫ (singularChainFunctorZ.map σ.down).f n

/-- The subdivision operator `$ : S_n(X) → S_n(X)` in degree `n`, assembled from its
components on free generators via the coproduct universal property. -/
def sdDegreeMap (X : TopCat.{0}) (n : ℕ) :
    (singularChainFunctorZ.obj X).X n ⟶ (singularChainFunctorZ.obj X).X n := by
  rw [chainGroup_eq_coprod]
  exact Sigma.desc (sdSigmaComponent X n)

/-- The subdivision operator commutes with the boundary on `S_*(Δ^n)`; that is, on the
standard simplex it is a chain map. This standard-simplex case is the seed from
which the general chain-map property is bootstrapped by naturality. -/
theorem sdDegreeMap_comm_on_stdSimplex (n : ℕ) (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    sdDegreeMap (stdSimplexTop n) i ≫ (singularChainFunctorZ.obj (stdSimplexTop n)).d i j =
    (singularChainFunctorZ.obj (stdSimplexTop n)).d i j ≫ sdDegreeMap (stdSimplexTop n) j := by sorry

set_option maxHeartbeats 3200000 in
/-- The subdivision operator `$` commutes with the boundary on `S_*(X)` for any
topological space `X`, so it is a chain map. This is the chain-map half of
Proposition 12.1, deduced from the standard-simplex case by naturality. -/
theorem sdDegreeMap_comm (X : TopCat.{0}) (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    sdDegreeMap X i ≫ (singularChainFunctorZ.obj X).d i j =
    (singularChainFunctorZ.obj X).d i j ≫ sdDegreeMap X j := by
  apply Sigma.hom_ext _ _ _
  intro σ
  let g_i := (TopCat.toSSet.{0}.map σ.down).app (Opposite.op (SimplexCategory.mk i))
  have hg_i : g_i (identitySimplex i) = σ := by
    simp only [identitySimplex]; apply ULift.ext; change 𝟙 _ ≫ σ.down = σ.down; simp
  have hι_eq : Sigma.ι (fun _ => AddCommGrpCat.of ℤ) σ =
    Sigma.ι (fun (_ : SingType (stdSimplexTop i) i) => AddCommGrpCat.of ℤ) (identitySimplex i) ≫
      Sigma.map' g_i (fun _ => 𝟙 _) := by
    rw [Sigma.ι_comp_map', Category.id_comp, hg_i]
  simp only [hι_eq, Category.assoc]
  congr 1
  change (singularChainFunctorZ.map σ.down).f i ≫ sdDegreeMap X i ≫
    (singularChainFunctorZ.obj X).d i j =
    (singularChainFunctorZ.map σ.down).f i ≫ (singularChainFunctorZ.obj X).d i j ≫ sdDegreeMap X j
  set F := singularChainFunctorZ.map σ.down
  have nat_i : F.f i ≫ sdDegreeMap X i = sdDegreeMap (stdSimplexTop i) i ≫ F.f i := by
    change Sigma.map' g_i (fun _ => 𝟙 _) ≫ Sigma.desc (sdSigmaComponent X i) =
           Sigma.desc (sdSigmaComponent (stdSimplexTop i) i) ≫ Sigma.map' g_i (fun _ => 𝟙 _)
    apply Sigma.hom_ext _ _ _; intro τ
    rw [Sigma.ι_comp_map'_assoc, Category.id_comp, Sigma.ι_desc]
    erw [Sigma.ι_desc_assoc]
    simp only [sdSigmaComponent, Category.assoc]
    conv_lhs => rw [show (g_i τ).down = τ.down ≫ σ.down from rfl,
      singularChainFunctorZ.map_comp, HomologicalComplex.comp_f]
    congr 1
  let g_j := (TopCat.toSSet.{0}.map σ.down).app (Opposite.op (SimplexCategory.mk j))
  have nat_j : F.f j ≫ sdDegreeMap X j = sdDegreeMap (stdSimplexTop i) j ≫ F.f j := by
    change Sigma.map' g_j (fun _ => 𝟙 _) ≫ Sigma.desc (sdSigmaComponent X j) =
           Sigma.desc (sdSigmaComponent (stdSimplexTop i) j) ≫ Sigma.map' g_j (fun _ => 𝟙 _)
    apply Sigma.hom_ext _ _ _; intro τ
    rw [Sigma.ι_comp_map'_assoc, Category.id_comp, Sigma.ι_desc]
    erw [Sigma.ι_desc_assoc]
    simp only [sdSigmaComponent, Category.assoc]
    conv_lhs => rw [show (g_j τ).down = τ.down ≫ σ.down from rfl,
      singularChainFunctorZ.map_comp, HomologicalComplex.comp_f]
    congr 1
  have hFd := F.comm' i j hij
  have goal_eq : F.f i ≫ sdDegreeMap X i ≫ (singularChainFunctorZ.obj X).d i j =
    sdDegreeMap (stdSimplexTop i) i ≫ (singularChainFunctorZ.obj (stdSimplexTop i)).d i j ≫ F.f j := by
    conv_lhs => rw [← Category.assoc, nat_i]; erw [Category.assoc, hFd]
    rfl

  have goal_eq2 : F.f i ≫ (singularChainFunctorZ.obj X).d i j ≫ sdDegreeMap X j =
    (singularChainFunctorZ.obj (stdSimplexTop i)).d i j ≫ sdDegreeMap (stdSimplexTop i) j ≫ F.f j := by
    conv_lhs => rw [← Category.assoc, hFd, Category.assoc, nat_j]
    rfl
  rw [goal_eq, goal_eq2, ← Category.assoc, sdDegreeMap_comm_on_stdSimplex i i j hij, Category.assoc]

/-- The subdivision chain map `$ : S_*(X) → S_*(X)`, assembled from the degreewise
maps `sdDegreeMap X n` together with the boundary-commutation theorem. This is
the chain map of Proposition 12.1 for a fixed space `X`. -/
def sdChainMap (X : TopCat.{0}) :
    singularChainFunctorZ.obj X ⟶ singularChainFunctorZ.obj X where
  f := sdDegreeMap X
  comm' := sdDegreeMap_comm X

set_option maxHeartbeats 800000 in
/-- Naturality of the subdivision chain map in `X`: for `f : X → Y`, the squares
`f_* ∘ $_X = $_Y ∘ f_*` commute. This is the naturality assertion of
Proposition 12.1. -/
theorem sdChainMap_naturality (X Y : TopCat.{0}) (f : X ⟶ Y) :
    singularChainFunctorZ.map f ≫ sdChainMap Y =
    sdChainMap X ≫ singularChainFunctorZ.map f := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, sdChainMap]
  let g := (TopCat.toSSet.{0}.map f).app (Opposite.op (SimplexCategory.mk n))
  change Sigma.map' g (fun _ => 𝟙 _) ≫ Sigma.desc (sdSigmaComponent Y n) =
         Sigma.desc (sdSigmaComponent X n) ≫ Sigma.map' g (fun _ => 𝟙 _)
  apply Sigma.hom_ext _ _ _
  intro σ
  rw [Sigma.ι_comp_map'_assoc, Category.id_comp, Sigma.ι_desc]
  erw [Sigma.ι_desc_assoc]
  simp only [sdSigmaComponent, Category.assoc]
  conv_lhs => rw [show (g σ).down = σ.down ≫ f from rfl,
    singularChainFunctorZ.map_comp, HomologicalComplex.comp_f]
  congr 1

/-- The subdivision operator as a natural transformation `$ : S_* ⟹ S_*` of singular
chain complex functors. This is the natural chain map of Proposition 12.1. -/
def subdivisionOperator : singularChainFunctorZ ⟶ singularChainFunctorZ where
  app X := sdChainMap X
  naturality X Y f := sdChainMap_naturality X Y f

/-- Push forward a chain `elem ∈ S_{k+1}(Δ^k)` along a singular `k`-simplex
`σ : Δ^k → X` to obtain a chain in `S_{k+1}(X)`. Used in the construction of
the chain homotopy. -/
def homotopyPushforward {X : TopCat.{0}} {k : ℕ}
    (elem : ↑((singularChainFunctorZ.obj (stdSimplexTop k)).X (k + 1)))
    (σ : SingType X k) :
    ↑((singularChainFunctorZ.obj X).X (k + 1)) :=
  ((singularChainFunctorZ.map σ.down).f (k + 1)) elem

/-- Degree-raising map `S_k(X) → S_{k+1}(X)` built from a chosen element
`elem ∈ S_{k+1}(Δ^k)`: on each generator `σ` it returns `σ_*(elem)`. This is the
abstract pattern used to build the chain homotopy. -/
def homotopyDegreeWithElem {k : ℕ}
    (elem : ↑((singularChainFunctorZ.obj (stdSimplexTop k)).X (k + 1)))
    (X : TopCat.{0}) :
    (singularChainFunctorZ.obj X).X k ⟶ (singularChainFunctorZ.obj X).X (k + 1) := by
  rw [chainGroup_eq_coprod]
  exact Sigma.desc (fun σ =>
    AddCommGrpCat.ofHom ((zmultiplesHom _) (homotopyPushforward elem σ)))

/-- The element `T_n ∈ S_{n+1}(Δ^n)` defining the chain homotopy on the universal
`n`-simplex, constructed recursively: zero in degree `0`, and in degree `n + 1`
the cone from the barycenter over `$ι_{n+1} - ι_{n+1} - T(dι_{n+1})`. This is
the standard inductive recipe yielding `dh + hd = $ - 1`. -/
def sdHomotopyIota_elem : (n : ℕ) →
    ↑((singularChainFunctorZ.obj (stdSimplexTop n)).X (n + 1))
  | 0 => 0
  | n + 1 =>
    let idGen := chainGenerator (identitySimplex (n + 1))
    let sdElem := sdIota_elem (n + 1)
    let boundary :=
      ((singularChainFunctorZ.obj (stdSimplexTop (n + 1))).d (n + 1) n) idGen
    let T_boundary :=
      (homotopyDegreeWithElem (sdHomotopyIota_elem n) (stdSimplexTop (n + 1))) boundary
    let inner := sdElem - idGen - T_boundary
    (coneOperator (barycenter (n + 1)) (n + 1)) inner

/-- The chain-homotopy element `T_n`, packaged as the group homomorphism
`ℤ → S_{n+1}(Δ^n)` sending `1` to `T_n`. -/
def sdHomotopyIotaHom (n : ℕ) :
    AddCommGrpCat.of ℤ ⟶ (singularChainFunctorZ.obj (stdSimplexTop n)).X (n + 1) :=
  AddCommGrpCat.ofHom
    ((zmultiplesHom ↑((singularChainFunctorZ.obj (stdSimplexTop n)).X (n + 1)))
      (sdHomotopyIota_elem n))

/-- The component of the chain homotopy on the free generator indexed by `σ`: it sends
the generator to `σ_*(T_n) ∈ S_{n+1}(X)`. -/
def sdHomotopySigmaComponent (X : TopCat.{0}) (n : ℕ) (σ : SingType X n) :
    AddCommGrpCat.of ℤ ⟶ (singularChainFunctorZ.obj X).X (n + 1) :=
  sdHomotopyIotaHom n ≫ (singularChainFunctorZ.map σ.down).f (n + 1)

/-- The chain homotopy `h : S_n(X) → S_{n+1}(X)` in degree `n`, assembled from its
components on the free generators of `S_n(X)`. -/
def sdHomotopyDegreeMap (X : TopCat.{0}) (n : ℕ) :
    (singularChainFunctorZ.obj X).X n ⟶ (singularChainFunctorZ.obj X).X (n + 1) := by
  rw [chainGroup_eq_coprod]
  exact Sigma.desc (sdHomotopySigmaComponent X n)

/-- The chain homotopy assembled into the family of maps required by Mathlib's
`Homotopy` structure: it equals `sdHomotopyDegreeMap` (up to a degree cast) when
`j = i + 1` and is zero otherwise. -/
def sdChainHomotopyHom (X : TopCat.{0}) (i j : ℕ) :
    (singularChainFunctorZ.obj X).X i ⟶ (singularChainFunctorZ.obj X).X j :=
  if h : (ComplexShape.down ℕ).Rel j i then
    sdHomotopyDegreeMap X i ≫ eqToHom (by congr 1)
  else 0

/-- Outside the relevant degree shift the chain homotopy vanishes. -/
theorem sdChainHomotopyHom_zero (X : TopCat.{0}) (i j : ℕ)
    (h : ¬(ComplexShape.down ℕ).Rel j i) :
    sdChainHomotopyHom X i j = 0 := by
  unfold sdChainHomotopyHom
  rw [dif_neg h]

/-- On the standard simplex `Δ^i`, the chain homotopy identity `$ = dh + hd + id` holds
in degree `i`. This is the seed case from which the general identity is bootstrapped
by naturality. -/
theorem sdChainHomotopyHom_comm_on_stdSimplex (i : ℕ) :
    (sdChainMap (stdSimplexTop i)).f i =
      dNext i (sdChainHomotopyHom (stdSimplexTop i)) +
        prevD i (sdChainHomotopyHom (stdSimplexTop i)) +
          HomologicalComplex.Hom.f (𝟙 (singularChainFunctorZ.obj (stdSimplexTop i))) i := by sorry

set_option maxHeartbeats 1600000 in
/-- The chain homotopy identity `$ = dh + hd + id` in every degree on `S_*(X)` for any
topological space `X`. This is the chain-homotopy half of Proposition 12.1:
`$` is chain-homotopic to the identity. -/
theorem sdChainHomotopyHom_comm (X : TopCat.{0}) (i : ℕ) :
    (sdChainMap X).f i =
      dNext i (sdChainHomotopyHom X) + prevD i (sdChainHomotopyHom X) +
        HomologicalComplex.Hom.f (𝟙 (singularChainFunctorZ.obj X)) i := by

  apply Sigma.hom_ext _ _ _
  intro σ
  set F := singularChainFunctorZ.map σ.down
  have hnat_sd : F.f i ≫ (sdChainMap X).f i = (sdChainMap (stdSimplexTop i)).f i ≫ F.f i := by
    have := sdChainMap_naturality (stdSimplexTop i) X σ.down
    exact congr_fun (congr_arg HomologicalComplex.Hom.f this) i
  have hnat_T : ∀ a b, F.f a ≫ sdChainHomotopyHom X a b =
      sdChainHomotopyHom (stdSimplexTop i) a b ≫ F.f b := by
    intro a b
    unfold sdChainHomotopyHom
    split_ifs with h
    · have hab : a + 1 = b := h; subst hab
      simp only [eqToHom_refl, Category.comp_id]
      let g_a := (TopCat.toSSet.{0}.map σ.down).app (Opposite.op (SimplexCategory.mk a))
      change Sigma.map' g_a (fun _ => 𝟙 _) ≫ Sigma.desc (sdHomotopySigmaComponent X a) =
             Sigma.desc (sdHomotopySigmaComponent (stdSimplexTop i) a) ≫
               (singularChainFunctorZ.map σ.down).f (a + 1)
      apply Sigma.hom_ext _ _ _
      intro τ
      rw [Sigma.ι_comp_map'_assoc, Category.id_comp, Sigma.ι_desc]

      erw [Sigma.ι_desc_assoc]
      simp only [sdHomotopySigmaComponent, Category.assoc]
      conv_lhs => rw [show (g_a τ).down = τ.down ≫ σ.down from rfl,
        singularChainFunctorZ.map_comp, HomologicalComplex.comp_f]
      congr 1
    · simp only [Limits.comp_zero, Limits.zero_comp]; rfl
  have hdN : F.f i ≫ dNext i (sdChainHomotopyHom X) =
      dNext i (sdChainHomotopyHom (stdSimplexTop i)) ≫ F.f i := by
    rw [← dNext_comp_left F (sdChainHomotopyHom X) i,
        ← dNext_comp_right (sdChainHomotopyHom (stdSimplexTop i)) F i]
    congr 1; funext a b; exact hnat_T a b
  have hpD : F.f i ≫ prevD i (sdChainHomotopyHom X) =
      prevD i (sdChainHomotopyHom (stdSimplexTop i)) ≫ F.f i := by
    rw [← prevD_comp_left F (sdChainHomotopyHom X) i,
        ← prevD_comp_right (sdChainHomotopyHom (stdSimplexTop i)) F i]
    congr 1; funext a b; exact hnat_T a b

  let g := (TopCat.toSSet.{0}.map σ.down).app (Opposite.op (SimplexCategory.mk i))
  have hg : g (identitySimplex i) = σ := by
    simp only [identitySimplex]; apply ULift.ext; change 𝟙 _ ≫ σ.down = σ.down; simp
  have hι_eq : Sigma.ι (fun _ => AddCommGrpCat.of ℤ) σ =
    Sigma.ι (fun (_ : SingType (stdSimplexTop i) i) => AddCommGrpCat.of ℤ) (identitySimplex i) ≫
      Sigma.map' g (fun _ => 𝟙 _) := by
    rw [Sigma.ι_comp_map', Category.id_comp, hg]
  simp only [hι_eq, Category.assoc]
  congr 1
  show F.f i ≫ (sdChainMap X).f i =
    F.f i ≫ (dNext i (sdChainHomotopyHom X) + prevD i (sdChainHomotopyHom X) +
      HomologicalComplex.Hom.f (𝟙 (singularChainFunctorZ.obj X)) i)
  rw [Preadditive.comp_add, Preadditive.comp_add, hnat_sd, hdN, hpD]
  simp only [HomologicalComplex.id_f, Category.comp_id]
  rw [sdChainHomotopyHom_comm_on_stdSimplex i]
  simp only [HomologicalComplex.id_f, Preadditive.add_comp, Category.id_comp]
  rfl

/-- The chain homotopy `h : $ ≃ id` on `S_*(X)`, packaged as a `Homotopy` between the
subdivision operator and the identity chain map. This is the explicit witness
behind Proposition 12.1. -/
def subdivisionChainHomotopy (X : TopCat.{0}) :
    Homotopy (subdivisionOperator.app X) (𝟙 (singularChainFunctorZ.obj X)) where
  hom := sdChainHomotopyHom X
  zero := sdChainHomotopyHom_zero X
  comm := sdChainHomotopyHom_comm X

/-- Proposition 12.1: the subdivision operator `$` on `S_*(X)` is chain-homotopic to
the identity. -/
theorem subdivision_homotopic_id (X : TopCat.{0}) :
    Nonempty (Homotopy (subdivisionOperator.app X) (𝟙 (singularChainFunctorZ.obj X))) :=
  ⟨subdivisionChainHomotopy X⟩

set_option maxHeartbeats 800000 in
/-- Naturality of the chain-homotopy degree map in `X`: `f_* ∘ h_X = h_Y ∘ f_*` for
every continuous map `f : X → Y`. This makes the chain homotopy from
Proposition 12.1 natural in the space. -/
theorem sdHomotopyDegreeMap_naturality (X Y : TopCat.{0}) (f : X ⟶ Y) (n : ℕ) :
    (singularChainFunctorZ.map f).f n ≫ sdHomotopyDegreeMap Y n =
    sdHomotopyDegreeMap X n ≫ (singularChainFunctorZ.map f).f (n + 1) := by


  let g_n := (TopCat.toSSet.{0}.map f).app (Opposite.op (SimplexCategory.mk n))


  change Sigma.map' g_n (fun _ => 𝟙 _) ≫ Sigma.desc (sdHomotopySigmaComponent Y n) =
         Sigma.desc (sdHomotopySigmaComponent X n) ≫ (singularChainFunctorZ.map f).f (n + 1)
  apply Sigma.hom_ext _ _ _
  intro σ
  rw [Sigma.ι_comp_map'_assoc, Category.id_comp, Sigma.ι_desc]
  erw [Sigma.ι_desc_assoc]
  simp only [sdHomotopySigmaComponent, Category.assoc]
  conv_lhs => rw [show (g_n σ).down = σ.down ≫ f from rfl,
    singularChainFunctorZ.map_comp, HomologicalComplex.comp_f]
  congr 1

end BarycentricSubdivision

end
