/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.ModelChains

open Finset BigOperators

namespace AlgebraicTopologyI

noncomputable section

open ContinuousMap

/-- The singular chain cross product
`× : S_p(X) × S_q(Y) → S_{p+q}(X × Y)` as a bilinear map, defined on generators
by applying the universal model cross product to each pair of simplices and
extending freely. This is the underlying construction for Theorem 6.2. -/
noncomputable def crossProductMap (p q : ℕ) (X : Type) (Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] :
    SingularChains p X →+ (SingularChains q Y →+ SingularChains (p + q) (X × Y)) :=
  FreeAbelianGroup.lift (fun (σ : SingularSimplex p X) =>
    FreeAbelianGroup.lift (fun (τ : SingularSimplex q Y) =>
      crossFromModelChain (universalCross p q) σ τ))

/-- Naturality of the cross product: for continuous maps `f : X → X'` and
`g : Y → Y'`, the cross product commutes with the induced maps on singular
chains, i.e. `f_*(a) × g_*(b) = (f × g)_*(a × b)`. This is the naturality
part of Theorem 6.2. -/
theorem crossProductMap_naturality
    (p q : ℕ) (X X' Y Y' : Type)
    [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y'))
    (a : SingularChains p X) (b : SingularChains q Y) :
    (crossProductMap p q X' Y') (SingularChains.map f a) (SingularChains.map g b) =
      SingularChains.map (ContinuousMap.prodMap f g) ((crossProductMap p q X Y) a b) := by sorry

/-- The Leibniz rule for the cross product: the boundary of a cross product
chain satisfies `d(a × b) = (da) × b + (-1)^p · a × (db)`. This is the
graded-derivation part of Theorem 6.2. -/
theorem crossProductMap_leibniz
    (p q : ℕ) (X : Type) (Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (a : SingularChains (p + 1) X) (b : SingularChains (q + 1) Y) :
    let ab := (crossProductMap (p + 1) (q + 1) X Y) a b
    let ab' := SingularChains.castIdx (show (p + 1) + (q + 1) = (p + q + 1) + 1 by omega) ab
    let dab := boundaryMap (p + q + 1) (X × Y) ab'
    let da_b := SingularChains.castIdx (show p + (q + 1) = p + q + 1 by rfl)
                  ((crossProductMap p (q + 1) X Y) (boundaryMap p X a) b)
    let a_db := SingularChains.castIdx (show (p + 1) + q = p + q + 1 by omega)
                  ((crossProductMap (p + 1) q X Y) a (boundaryMap q Y b))
    dab = da_b + (-1 : ℤ) ^ (p + 1) • a_db := by sorry

/-- Left normalization for the cross product: for any point `x ∈ X` and any
chain `b ∈ S_q(Y)`, the cross product `c_x^0 × b` agrees with the chain
obtained by pushing `b` forward along the inclusion `y ↦ (x, y)`. This is
the left-normalization clause of Theorem 6.2. -/
theorem crossProductMap_normalization_left
    (q : ℕ) (X : Type) (Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (b : SingularChains q Y) :
    SingularChains.castIdx (show 0 + q = q by omega)
      ((crossProductMap 0 q X Y) (constChain x) b) =
      SingularChains.map (inclusionRight x) b := by sorry

/-- Right normalization for the cross product: for any point `y ∈ Y` and any
chain `a ∈ S_p(X)`, the cross product `a × c_y^0` agrees with the chain
obtained by pushing `a` forward along the inclusion `x ↦ (x, y)`. This is
the right-normalization clause of Theorem 6.2. -/
theorem crossProductMap_normalization_right
    (p : ℕ) (X : Type) (Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (y : Y) (a : SingularChains p X) :
    (crossProductMap p 0 X Y) a (constChain y) =
      SingularChains.map (inclusionLeft y) a := by sorry

/-- Theorem 6.2: there exists a singular chain cross product
`× : S_p(X) × S_q(Y) → S_{p+q}(X × Y)` satisfying naturality, bilinearity,
the Leibniz rule, and the normalization conditions. The witness is built
from `crossProductMap` together with the four preceding lemmas. -/
theorem crossProduct_exists : Nonempty CrossProduct :=
  ⟨{
    crossMap := crossProductMap
    naturality := crossProductMap_naturality
    leibniz := crossProductMap_leibniz
    normalization_left := crossProductMap_normalization_left
    normalization_right := crossProductMap_normalization_right
  }⟩

open ContinuousMap unitInterval

/-- A chain homotopy between the singular-chain maps induced by two
continuous maps `f0, f1 : X → Y`: a sequence of homomorphisms
`hom n : S_n(X) → S_{n+1}(Y)` satisfying the chain-homotopy identity
`d ∘ hom + hom ∘ d = f1_* - f0_*`. This is the chain-level homotopy
witnessing Theorem 6.1 / Proposition 5.11. -/
structure SingularChainHomotopy {X : Type} {Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f0 f1 : C(X, Y)) where
  hom : ∀ (n : ℕ), SingularChains n X →+ SingularChains (n + 1) Y
  chain_htpy : ∀ (n : ℕ) (s : SingularChains (n + 1) X),
    boundaryMap (n + 1) Y (hom (n + 1) s) + hom n (boundaryMap n X s) =
      SingularChains.map f1 s - SingularChains.map f0 s

/-- The bottom inclusion `X → X × I` given by `x ↦ (x, 0)`. -/
noncomputable def inclusion0 (X : Type) [TopologicalSpace X] :
    C(X, X × ↥I) :=
  ContinuousMap.prodMk (ContinuousMap.id X) (ContinuousMap.const X ⟨0, unitInterval.zero_mem⟩)

/-- The top inclusion `X → X × I` given by `x ↦ (x, 1)`. -/
noncomputable def inclusion1 (X : Type) [TopologicalSpace X] :
    C(X, X × ↥I) :=
  ContinuousMap.prodMk (ContinuousMap.id X) (ContinuousMap.const X ⟨1, unitInterval.one_mem⟩)

/-- A natural chain homotopy between the singular-chain maps induced by the
two inclusions `inclusion0, inclusion1 : X → X × I`. The data consists of
homomorphisms `S_n(X) → S_{n+1}(X × I)` satisfying the chain-homotopy
identity and a naturality square in `X`. This is the universal ingredient
used to build chain homotopies from continuous homotopies in Theorem 6.1. -/
structure NaturalChainHomotopyInclusions where
  hom : ∀ (X : Type) [TopologicalSpace X] (n : ℕ),
    SingularChains n X →+ SingularChains (n + 1) (X × ↥I)
  chain_htpy : ∀ (X : Type) [TopologicalSpace X] (n : ℕ)
    (s : SingularChains (n + 1) X),
    boundaryMap (n + 1) (X × ↥I) (hom X (n + 1) s) + hom X n (boundaryMap n X s) =
      SingularChains.map (inclusion1 X) s - SingularChains.map (inclusion0 X) s
  naturality : ∀ (X X' : Type) [TopologicalSpace X] [TopologicalSpace X']
    (g : C(X', X)) (n : ℕ) (s : SingularChains n X'),
    SingularChains.map (ContinuousMap.prodMap g (ContinuousMap.id ↥I)) (hom X' n s) =
      hom X n (SingularChains.map g s)

/-- Functoriality of the singular-chain map: the chain map induced by a
composition of continuous maps is the composition of the induced chain
maps. -/
lemma SingularChains.map_comp {n : ℕ} {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (g : C(X, Y)) (s : SingularChains n X) :
    SingularChains.map (f.comp g) s = SingularChains.map f (SingularChains.map g s) := by
  show (FreeAbelianGroup.map (SingularSimplex.map (f.comp g))) s =
    (FreeAbelianGroup.map (SingularSimplex.map f)) ((FreeAbelianGroup.map (SingularSimplex.map g)) s)
  rw [← FreeAbelianGroup.map_comp_apply]
  congr 1

/-- The singular boundary map commutes with the chain map induced by a
continuous map; equivalently, `SingularChains.map f` is a chain map. -/
lemma boundaryMap_map_comm {n : ℕ} {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (s : SingularChains (n + 1) X) :
    boundaryMap n Y (SingularChains.map f s) =
      SingularChains.map f (boundaryMap n X s) := by


  have h_eq : (boundaryMap n Y).comp (SingularChains.map f) =
      (SingularChains.map f).comp (boundaryMap n X) := by
    apply FreeAbelianGroup.lift_ext
    intro sigma

    show (boundaryMap n Y) (FreeAbelianGroup.of (SingularSimplex.map f sigma)) =
      (SingularChains.map f) ((boundaryMap n X) (FreeAbelianGroup.of sigma))

    unfold boundaryMap SingularChains.map SingularSimplex.map SingularSimplex.face
    erw [FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of, map_sum]
    congr 1
    ext i : 1
    erw [map_zsmul, FreeAbelianGroup.map_of_apply]
    simp only [ContinuousMap.comp_assoc]
    rfl
  exact DFunLike.congr_fun h_eq s

/-- The fundamental singular `1`-simplex `ι₁ : Δ¹ → I` given on barycentric
coordinates `(t₀, t₁)` by `(t₀, t₁) ↦ t₁`. -/
noncomputable def iotaSimplex : SingularSimplex 1 ↥I where
  toFun t := ⟨t.1 1, by
    obtain ⟨hnn, hsum⟩ := t.2
    constructor
    · exact hnn 1
    · have h0 := hnn 0
      have : t.1 0 + t.1 1 = 1 := by
        have := hsum
        simp [Fin.sum_univ_two] at this
        exact this
      linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_apply 1).comp continuous_subtype_val

/-- The `0`-th face of `iotaSimplex` is the constant simplex at `1`. -/
lemma iotaSimplex_face0 :
    SingularSimplex.face 0 iotaSimplex = constSimplex ⟨1, unitInterval.one_mem⟩ := by
  apply ContinuousMap.ext
  intro t
  simp only [SingularSimplex.face, iotaSimplex, faceInclusion, constSimplex,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, ContinuousMap.const_apply]
  apply Subtype.ext
  obtain ⟨_, hsum⟩ := t.2
  rw [Fin.sum_univ_one] at hsum
  simpa using hsum

/-- The `1`-st face of `iotaSimplex` is the constant simplex at `0`. -/
lemma iotaSimplex_face1 :
    SingularSimplex.face 1 iotaSimplex = constSimplex ⟨0, unitInterval.zero_mem⟩ := by
  apply ContinuousMap.ext
  intro t
  simp only [SingularSimplex.face, iotaSimplex, faceInclusion, constSimplex,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, ContinuousMap.const_apply]
  apply Subtype.ext
  simp

/-- The boundary of the fundamental `1`-simplex `ι₁` on `I` is
`c₁⁰ - c₀⁰`, the difference of the constant `0`-simplices at the endpoints. -/
lemma boundary_iota :
    boundaryMap 0 ↥I (FreeAbelianGroup.of iotaSimplex) =
      constChain ⟨1, unitInterval.one_mem⟩ - constChain ⟨0, unitInterval.zero_mem⟩ := by
  unfold boundaryMap
  erw [FreeAbelianGroup.lift_apply_of]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_one_smul,
    iotaSimplex_face0, iotaSimplex_face1, constChain]
  abel

/-- The right-product-inclusion at the endpoint `1 ∈ I` agrees with
`inclusion1`. -/
lemma inclusionLeft_one_eq_inclusion1 (X : Type) [TopologicalSpace X] :
    inclusionLeft (Y := ↥I) ⟨1, unitInterval.one_mem⟩ = inclusion1 X := by
  apply ContinuousMap.ext; intro x; rfl

/-- The right-product-inclusion at the endpoint `0 ∈ I` agrees with
`inclusion0`. -/
lemma inclusionLeft_zero_eq_inclusion0 (X : Type) [TopologicalSpace X] :
    inclusionLeft (Y := ↥I) ⟨0, unitInterval.zero_mem⟩ = inclusion0 X := by
  apply ContinuousMap.ext; intro x; rfl

/-- Existence of a natural chain homotopy between the two inclusions
`X → X × I`. The witness is built by crossing with the fundamental
`1`-simplex `ι₁` on `I` and using the Leibniz rule and normalization of
the singular chain cross product. This is the chain-level engine behind
Theorem 6.1. -/
theorem naturalChainHomotopyInclusions_exists : Nonempty NaturalChainHomotopyInclusions := by
  obtain ⟨cp⟩ := crossProduct_exists
  let iota : SingularChains 1 ↥I := FreeAbelianGroup.of iotaSimplex
  refine ⟨{
    hom := fun X _ n => ((-1 : ℤ) ^ n) • ((cp.crossMap n 1 X ↥I).flip iota)
    chain_htpy := fun X _ n s => ?_
    naturality := fun X X' _ _ g n s => ?_
  }⟩
  ·
    show boundaryMap (n + 1) (X × ↥I)
        (((-1 : ℤ) ^ (n + 1) • (cp.crossMap (n + 1) 1 X ↥I).flip iota) s) +
      ((-1 : ℤ) ^ n • (cp.crossMap n 1 X ↥I).flip iota) (boundaryMap n X s) =
      SingularChains.map (inclusion1 X) s - SingularChains.map (inclusion0 X) s
    simp only [AddMonoidHom.smul_apply, AddMonoidHom.flip_apply, map_zsmul]
    have hleib := cp.leibniz n 0 X ↥I s iota
    simp only [SingularChains.castIdx, AddMonoidHom.id_apply] at hleib
    have hnorm1 := cp.normalization_right (n + 1) X ↥I ⟨1, unitInterval.one_mem⟩ s
    have hnorm0 := cp.normalization_right (n + 1) X ↥I ⟨0, unitInterval.zero_mem⟩ s
    rw [boundary_iota] at hleib
    rw [map_sub] at hleib
    rw [hnorm1, hnorm0] at hleib
    rw [inclusionLeft_one_eq_inclusion1, inclusionLeft_zero_eq_inclusion0] at hleib
    rw [hleib]
    simp only [smul_add, smul_sub, smul_smul]
    have h1 : (-1 : ℤ) ^ (n + 1) * (-1 : ℤ) ^ (n + 1) = 1 := by
      rw [← pow_add]; exact (Even.add_self (n + 1)).neg_one_pow
    have h2 : (-1 : ℤ) ^ (n + 1) = -((-1 : ℤ) ^ n) := by ring
    rw [h1, h2, one_smul]
    simp only [neg_smul]
    abel
  ·
    show SingularChains.map (ContinuousMap.prodMap g (ContinuousMap.id ↥I))
      (((-1 : ℤ) ^ n • (cp.crossMap n 1 X' ↥I).flip iota) s) =
      ((-1 : ℤ) ^ n • (cp.crossMap n 1 X ↥I).flip iota) (SingularChains.map g s)
    simp only [AddMonoidHom.smul_apply, map_zsmul]
    congr 1
    show SingularChains.map (ContinuousMap.prodMap g (ContinuousMap.id ↥I))
      ((cp.crossMap n 1 X' ↥I s) iota) =
      (cp.crossMap n 1 X ↥I (SingularChains.map g s)) iota
    rw [← cp.naturality]
    congr 1

/-- Theorem 6.1: a continuous homotopy `h : f0 ≃ f1 : X → Y` determines a
natural chain homotopy `f0_* ≃ f1_* : S_*(X) → S_*(Y)`. The chain homotopy
is constructed by composing the universal chain homotopy for the inclusions
`X → X × I` (cf. `NaturalChainHomotopyInclusions`) with the homotopy
`h`. -/
noncomputable def ContinuousMap.Homotopy.naturalSingularChainHomotopy
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f0 f1 : C(X, Y)} (h : ContinuousMap.Homotopy f0 f1) :
    SingularChainHomotopy f0 f1 :=
  let k := Classical.choice naturalChainHomotopyInclusions_exists
  {
  hom n :=
    (SingularChains.map (h.toContinuousMap.comp ContinuousMap.prodSwap)).comp
      (k.hom X n)
  chain_htpy n s := by
    set h_swap : C(X × ↥I, Y) := h.toContinuousMap.comp ContinuousMap.prodSwap with h_swap_def
    show boundaryMap (n + 1) Y (SingularChains.map h_swap (k.hom X (n + 1) s)) +
        SingularChains.map h_swap (k.hom X n (boundaryMap n X s)) =
      SingularChains.map f1 s - SingularChains.map f0 s
    rw [boundaryMap_map_comm h_swap (k.hom X (n + 1) s)]
    rw [← map_add (SingularChains.map h_swap)]
    rw [k.chain_htpy X n s]
    rw [map_sub (SingularChains.map h_swap)]
    rw [← SingularChains.map_comp h_swap (inclusion1 X) s]
    rw [← SingularChains.map_comp h_swap (inclusion0 X) s]
    have h1 : h_swap.comp (inclusion1 X) = f1 := by
      ext x
      simp only [h_swap_def, inclusion1, ContinuousMap.comp_apply,
        ContinuousMap.prodSwap_apply, ContinuousMap.prod_eval,
        ContinuousMap.id_apply, ContinuousMap.const_apply]
      exact h.map_one_left x
    have h0 : h_swap.comp (inclusion0 X) = f0 := by
      ext x
      simp only [h_swap_def, inclusion0, ContinuousMap.comp_apply,
        ContinuousMap.prodSwap_apply, ContinuousMap.prod_eval,
        ContinuousMap.id_apply, ContinuousMap.const_apply]
      exact h.map_zero_left x
    rw [h1, h0] }

end

end AlgebraicTopologyI
