/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section33
import Atlas.AlgebraicTopologyI.code.Section29
import Atlas.AlgebraicTopologyI.code.Section25
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Basis.Prod

open CategoryTheory AlgebraicTopology Limits SingularCohomology

noncomputable section

open scoped TensorProduct

namespace CohomologyKunneth

/-- Total singular cohomology of `X` with coefficients in `R`, assembled as the
direct sum `⨁_{n : ℕ} H^n(X; R)` over natural-number degrees. -/
abbrev totalSingularCohomology
    (R : Type) [CommRing R] (X : TopCat.{0}) : Type :=
  DirectSum ℕ (singularCohomologyFamily R X)


/-- The bidegree-`(p, q)` component of the cohomology cross product, viewed as
a linear map from `H^p(X; R) ⊗ H^q(Y; R)` into the total cohomology
`⨁_n H^n(X × Y; R)` by landing in the degree `p + q` summand. -/
def componentCrossMap
    (R : Type) [CommRing R] (X Y : TopCat.{0}) (pq : ℕ × ℕ) :
    TensorProduct R (singularCohomologyFamily R X pq.1)
      (singularCohomologyFamily R Y pq.2) →ₗ[R]
      totalSingularCohomology R (TopCat.of (↑X × ↑Y)) :=
  (DirectSum.lof R ℕ (singularCohomologyFamily R (TopCat.of (↑X × ↑Y))) (pq.1 + pq.2)).comp
    (cohomologyCross R X Y pq.1 pq.2)

/-- The total cohomology cross product
`× : H^*(X; R) ⊗_R H^*(Y; R) → H^*(X × Y; R)`, built by distributing the tensor
product over the direct-sum decompositions and assembling the bidegree
components `componentCrossMap`. -/
def totalCohomologyCrossProduct
    (R : Type) [CommRing R] (X Y : TopCat.{0}) :
    (totalSingularCohomology R X ⊗[R]
      totalSingularCohomology R Y) →ₗ[R]
      totalSingularCohomology R (TopCat.of (↑X × ↑Y)) :=
  (DirectSum.toModule R (ℕ × ℕ)
    (totalSingularCohomology R (TopCat.of (↑X × ↑Y)))
    (componentCrossMap R X Y)).comp
    (TensorProduct.directSum R R
      (singularCohomologyFamily R X)
      (singularCohomologyFamily R Y)).toLinearMap

/-- Auxiliary statement of the bijectivity of the Kronecker pairing
`H^n(X; R) → Hom_R(H_n(X; R), R)` when `R` is a PID and every singular homology
module of `X` is finitely generated and free. This is the universal coefficient
isomorphism in this special case. -/
theorem kroneckerPairing_bijective_of_free_aux
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (X : TopCat.{0}) (n : ℕ)
    (hfree : ∀ m, Module.Free R (singularHomologyModule R X m : Type))
    (hfg : ∀ m, Module.Finite R (singularHomologyModule R X m : Type)) :
    Function.Bijective (kroneckerPairing R X n) := by sorry

/-- Public version of `kroneckerPairing_bijective_of_free_aux`: when `R` is a
PID and `H_*(X; R)` is finitely generated free in every degree, the Kronecker
pairing `H^n(X; R) → Hom_R(H_n(X; R), R)` is bijective. -/
theorem kroneckerPairing_bijective_of_free
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (X : TopCat.{0}) (n : ℕ)
    (hfree : ∀ m, Module.Free R (singularHomologyModule R X m : Type))
    (hfg : ∀ m, Module.Finite R (singularHomologyModule R X m : Type)) :
    Function.Bijective (kroneckerPairing R X n) :=
  kroneckerPairing_bijective_of_free_aux R X n hfree hfg

/-- Packaging of `kroneckerPairing_bijective_of_free` as an explicit linear
equivalence `H^n(X; R) ≃ₗ[R] Hom_R(H_n(X; R), R)`. -/
def kroneckerPairing_isLinearEquiv
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (X : TopCat.{0}) (n : ℕ)
    (hfree : ∀ m, Module.Free R (singularHomologyModule R X m : Type))
    (hfg : ∀ m, Module.Finite R (singularHomologyModule R X m : Type)) :
    (singularCohomologyFamily R X n) ≃ₗ[R]
      ((singularHomologyModule R X n : Type) →ₗ[R] R) :=
  LinearEquiv.ofBijective (kroneckerPairing R X n)
    (kroneckerPairing_bijective_of_free R X n hfree hfg)

/-- Total dual of singular homology: the direct sum
`⨁_{n : ℕ} Hom_R(H_n(X; R), R)`. Under the universal coefficient theorem this
is naturally isomorphic to `totalSingularCohomology` whenever `H_*(X; R)` is
free. -/
abbrev totalDualHomology (R : Type) [CommRing R] (X : TopCat.{0}) : Type :=
  DirectSum ℕ (fun n => (singularHomologyModule R X n : Type) →ₗ[R] R)

/-- The bidegree-`(p, q)` component of an inverse to the homology Künneth map
in degree `n = p + q`: pick a splitting of the Künneth short exact sequence on
`X` and `Y` and project the resulting retraction onto the
`H_p(X; R) ⊗ H_q(Y; R)` summand. -/
def kunnethInvComponent
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (X Y : TopCat.{0}) (p q : ℕ)
    (_hfree : ∀ n, Module.Free R (singularHomologyModule R X n : Type)) :
    (singularHomologyModule R (TopCat.of (↑X × ↑Y)) (p + q) : Type) →ₗ[R]
      TensorProduct R (singularHomologyModule R X p : Type)
        (singularHomologyModule R Y q : Type) :=
  let n := p + q
  let split := (KunnethTopological.kunnethShortExact_splitting R n X Y).some
  let retract := split.r
  let idx : { pq : ℕ × ℕ // pq.1 + pq.2 = n } := ⟨(p, q), rfl⟩
  let proj := Sigma.π (fun (pq : { pq : ℕ × ℕ // pq.1 + pq.2 = n }) =>
    MonoidalCategory.tensorObj (KunnethTopological.singularHomologyMod R pq.1.1 X)
      (KunnethTopological.singularHomologyMod R pq.1.2 Y)) idx
  (retract ≫ proj).hom

/-- Bidegree-`(p, q)` component of the left edge of the commuting diagram used
to prove bijectivity of the cohomology cross product: apply the Kronecker
pairings on each factor, distribute the tensor product through the dual, and
dualize the Künneth inverse component. -/
def componentDiagramLeftMap
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (X Y : TopCat.{0}) (p q : ℕ)
    (hfree : ∀ n, Module.Free R (singularHomologyModule R X n : Type)) :
    TensorProduct R (singularCohomologyFamily R X p)
      (singularCohomologyFamily R Y q) →ₗ[R]
      ((singularHomologyModule R (TopCat.of (↑X × ↑Y)) (p + q) : Type) →ₗ[R] R) :=

  ((kunnethInvComponent R X Y p q hfree).dualMap).comp

    ((TensorProduct.dualDistrib R
      (singularHomologyModule R X p : Type)
      (singularHomologyModule R Y q : Type)).comp

      (TensorProduct.map (kroneckerPairing R X p) (kroneckerPairing R Y q)))

/-- The total left edge of the comparison diagram: a linear map
`H^*(X; R) ⊗_R H^*(Y; R) → ⨁_n Hom_R(H_n(X × Y; R), R)` assembled from the
bidegree components `componentDiagramLeftMap`. -/
def diagramLeftMap
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (X Y : TopCat.{0})
    (hfree : ∀ n, Module.Free R (singularHomologyModule R X n : Type))
    (hfg : ∀ n, Module.Finite R (singularHomologyModule R X n : Type)) :
    (totalSingularCohomology R X ⊗[R] totalSingularCohomology R Y) →ₗ[R]
      totalDualHomology R (TopCat.of (↑X × ↑Y)) :=


  (DirectSum.toModule R (ℕ × ℕ)
    (totalDualHomology R (TopCat.of (↑X × ↑Y)))
    (fun pq =>
      (DirectSum.lof R ℕ
        (fun n => (singularHomologyModule R (TopCat.of (↑X × ↑Y)) n : Type) →ₗ[R] R)
        (pq.1 + pq.2)).comp
        (componentDiagramLeftMap R X Y pq.1 pq.2 hfree))).comp
    (TensorProduct.directSum R R
      (singularCohomologyFamily R X)
      (singularCohomologyFamily R Y)).toLinearMap

/-- The total right edge of the comparison diagram: apply the Kronecker
pairing in each degree to convert `H^*(X × Y; R)` into the direct sum of duals
`⨁_n Hom_R(H_n(X × Y; R), R)`. -/
def diagramRightMap
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (X Y : TopCat.{0})
    (hfree : ∀ n, Module.Free R (singularHomologyModule R X n : Type))
    (hfg : ∀ n, Module.Finite R (singularHomologyModule R X n : Type)) :
    totalSingularCohomology R (TopCat.of (↑X × ↑Y)) →ₗ[R]
      totalDualHomology R (TopCat.of (↑X × ↑Y)) :=
  DirectSum.toModule R ℕ (totalDualHomology R (TopCat.of (↑X × ↑Y)))
    (fun n => (DirectSum.lof R ℕ
      (fun n => (singularHomologyModule R (TopCat.of (↑X × ↑Y)) n : Type) →ₗ[R] R) n).comp
      (kroneckerPairing R (TopCat.of (↑X × ↑Y)) n))

/-- Pointwise commutativity of the comparison diagram on simple tensors and a
single homology class: the Kronecker pairing of the cohomology cross product
`a × b` against a class `z ∈ H_{p+q}(X × Y; R)` agrees with the dual pairing
obtained by routing `z` through the Künneth inverse. -/
theorem diagram_comm_component_pointwise
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (X Y : TopCat.{0}) (p q : ℕ)
    (hfree : ∀ n, Module.Free R (singularHomologyModule R X n : Type))
    (a : singularCohomologyFamily R X p)
    (b : singularCohomologyFamily R Y q)
    (z : (singularHomologyModule R (TopCat.of (↑X × ↑Y)) (p + q) : Type)) :
    kroneckerPairing R (TopCat.of (↑X × ↑Y)) (p + q)
      (cohomologyCross R X Y p q (TensorProduct.mk R _ _ a b)) z =
    (TensorProduct.dualDistrib R
      (singularHomologyModule R X p : Type)
      (singularHomologyModule R Y q : Type)
      (TensorProduct.map (kroneckerPairing R X p) (kroneckerPairing R Y q)
        (TensorProduct.mk R _ _ a b)))
      (kunnethInvComponent R X Y p q hfree z) := by sorry

/-- Bidegree-`(p, q)` commutativity of the comparison diagram: composing the
Kronecker pairing with the cohomology cross product agrees with
`componentDiagramLeftMap` on `H^p(X; R) ⊗ H^q(Y; R)`. -/
theorem diagram_comm_component
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (X Y : TopCat.{0}) (p q : ℕ)
    (hfree : ∀ n, Module.Free R (singularHomologyModule R X n : Type)) :
    (kroneckerPairing R (TopCat.of (↑X × ↑Y)) (p + q)).comp
      (cohomologyCross R X Y p q) =
    componentDiagramLeftMap R X Y p q hfree := by


  apply TensorProduct.ext
  ext a b

  simp only [componentDiagramLeftMap]

  exact diagram_comm_component_pointwise R X Y p q hfree a b _

/-- The total comparison square commutes:
`diagramRightMap ∘ totalCohomologyCrossProduct = diagramLeftMap`. This is the
totalized version of `diagram_comm_component`. -/
theorem diagram_comm
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (X Y : TopCat.{0})
    (hfree : ∀ n, Module.Free R (singularHomologyModule R X n : Type))
    (hfg : ∀ n, Module.Finite R (singularHomologyModule R X n : Type)) :
    (diagramRightMap R X Y hfree hfg).comp (totalCohomologyCrossProduct R X Y) =
    diagramLeftMap R X Y hfree hfg := by


  suffices h : (diagramRightMap R X Y hfree hfg).comp
    (DirectSum.toModule R (ℕ × ℕ) _ (componentCrossMap R X Y)) =
    DirectSum.toModule R (ℕ × ℕ) _ (fun pq =>
      (DirectSum.lof R ℕ _ (pq.1 + pq.2)).comp
        (componentDiagramLeftMap R X Y pq.1 pq.2 hfree)) by
    have lhs_eq : (diagramRightMap R X Y hfree hfg).comp (totalCohomologyCrossProduct R X Y) =
      ((diagramRightMap R X Y hfree hfg).comp
        (DirectSum.toModule R (ℕ × ℕ) _ (componentCrossMap R X Y))).comp
        (TensorProduct.directSum R R (singularCohomologyFamily R X)
          (singularCohomologyFamily R Y)).toLinearMap := by
      simp only [totalCohomologyCrossProduct, LinearMap.comp_assoc]
    rw [lhs_eq, h]
    rfl

  apply DirectSum.linearMap_ext R
  intro pq


  apply LinearMap.ext
  intro t
  simp only [LinearMap.comp_apply, componentCrossMap, DirectSum.toModule_lof,
    diagramRightMap, DirectSum.toModule_lof]


  have hcomp := diagram_comm_component R X Y pq.1 pq.2 hfree

  congr 1
  exact LinearMap.congr_fun hcomp t

/-- The assembly map underlying `diagramLeftMap` (the direct-sum gluing of all
`componentDiagramLeftMap`) is bijective; this is the technical core of the
Künneth bijectivity argument on the left edge. -/
theorem diagramLeftMap_assembly_bijective
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (X Y : TopCat.{0})
    (hfree : ∀ n, Module.Free R (singularHomologyModule R X n : Type))
    (hfg : ∀ n, Module.Finite R (singularHomologyModule R X n : Type)) :
    Function.Bijective
      (DirectSum.toModule R (ℕ × ℕ)
        (totalDualHomology R (TopCat.of (↑X × ↑Y)))
        (fun pq =>
          (DirectSum.lof R ℕ
            (fun n => (singularHomologyModule R (TopCat.of (↑X × ↑Y)) n : Type) →ₗ[R] R)
            (pq.1 + pq.2)).comp
            (componentDiagramLeftMap R X Y pq.1 pq.2 hfree))) := by sorry

/-- The left edge `diagramLeftMap` is bijective: combining the bijectivity of
the assembly map with the tensor-direct-sum distributivity equivalence. -/
theorem diagramLeftMap_bijective
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (X Y : TopCat.{0})
    (hfree : ∀ n, Module.Free R (singularHomologyModule R X n : Type))
    (hfg : ∀ n, Module.Finite R (singularHomologyModule R X n : Type)) :
    Function.Bijective (diagramLeftMap R X Y hfree hfg) := by

  show Function.Bijective
    ((DirectSum.toModule R (ℕ × ℕ)
      (totalDualHomology R (TopCat.of (↑X × ↑Y)))
      (fun pq =>
        (DirectSum.lof R ℕ
          (fun n => (singularHomologyModule R (TopCat.of (↑X × ↑Y)) n : Type) →ₗ[R] R)
          (pq.1 + pq.2)).comp
          (componentDiagramLeftMap R X Y pq.1 pq.2 hfree))).comp
      (TensorProduct.directSum R R
        (singularCohomologyFamily R X)
        (singularCohomologyFamily R Y)).toLinearMap)
  rw [LinearMap.coe_comp]
  exact (diagramLeftMap_assembly_bijective R X Y hfree hfg).comp
    (TensorProduct.directSum R R
      (singularCohomologyFamily R X)
      (singularCohomologyFamily R Y)).bijective

/-- Generic helper: if `f i : M i →ₗ[R'] N i` is bijective for every index `i`,
then the assembled map `⨁ M i → ⨁ N i` built by composing each `f i` with the
direct-sum inclusion `lof` is bijective. -/
lemma directSum_toModule_lof_comp_bijective
    {R' : Type} [CommRing R'] {ι : Type} [DecidableEq ι]
    {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module R' (M i)]
    {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module R' (N i)]
    (f : ∀ i, M i →ₗ[R'] N i) (hf : ∀ i, Function.Bijective (f i)) :
    Function.Bijective (DirectSum.toModule R' ι (DirectSum ι N)
      (fun n => (DirectSum.lof R' ι N n).comp (f n))) := by
  have heq : DirectSum.toModule R' ι (DirectSum ι N)
      (fun n => (DirectSum.lof R' ι N n).comp (f n)) = DirectSum.lmap (R := R') f := by
    ext i m j
    simp only [DirectSum.toModule_lof, LinearMap.comp_apply]
    change ((DirectSum.lof R' ι N i) ((f i) m)) j =
      (DFinsupp.mapRange (fun i x => (f i) x) (by intro i; simp)
        ((DirectSum.lof R' ι M i) m)) j
    conv_rhs => rw [show (DirectSum.lof R' ι M i) m = (DFinsupp.single i m : Π₀ k, M k) from rfl]
    rw [DFinsupp.mapRange_single]
    rfl
  rw [heq]
  let equivs : ∀ i, M i ≃ₗ[R'] N i := fun i => LinearEquiv.ofBijective (f i) (hf i)
  have heq2 : (DirectSum.lmap (R := R') f : (DirectSum ι M) →ₗ[R'] (DirectSum ι N)) =
    (DFinsupp.mapRange.linearEquiv equivs).toLinearMap := by
    ext i m j
    change (DFinsupp.mapRange (fun i x => (f i) x) (by intro i; simp)
      ((DirectSum.lof R' ι M i) m)) j =
      (DFinsupp.mapRange (fun i x => (equivs i) x) (by intro i; simp)
      ((DirectSum.lof R' ι M i) m)) j
    congr 2
  rw [heq2]
  exact (DFinsupp.mapRange.linearEquiv equivs).bijective

/-- The tensor-product term `⨁_{p+q=m} H_p(X) ⊗_R H_q(Y)` appearing in the
homology Künneth short exact sequence is free over the PID `R` whenever
`H_*(X; R)` is finitely generated and free in every degree. -/
theorem kunnethTensorTerm_free
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (m : ℕ) (X Y : TopCat.{0})
    (hfree : ∀ n, Module.Free R (singularHomologyModule R X n : Type))
    (hfg : ∀ n, Module.Finite R (singularHomologyModule R X n : Type)) :
    Module.Free R (KunnethTopological.kunnethTensorTerm R m X Y : Type) := by sorry

/-- The Tor term `⨁_{p+q=m-1} Tor^R_1(H_p(X), H_q(Y))` in the homology Künneth
short exact sequence is free over the PID `R` under the same hypotheses; in
fact, when `H_*(X; R)` is free this Tor vanishes. -/
theorem kunnethTorTerm_free
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (m : ℕ) (X Y : TopCat.{0})
    (hfree : ∀ n, Module.Free R (singularHomologyModule R X n : Type))
    (hfg : ∀ n, Module.Finite R (singularHomologyModule R X n : Type)) :
    Module.Free R (KunnethTopological.kunnethTorTerm R m X Y : Type) := by sorry

/-- If `H_*(X; R)` is finitely generated free over a PID `R`, then
`H_m(X × Y; R)` is also free, obtained as a direct sum of the (free) Künneth
tensor and Tor terms via a splitting of the Künneth short exact sequence. -/
theorem productHomology_free
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (X Y : TopCat.{0})
    (hfree : ∀ n, Module.Free R (singularHomologyModule R X n : Type))
    (hfg : ∀ n, Module.Finite R (singularHomologyModule R X n : Type))
    (m : ℕ) :
    Module.Free R (singularHomologyModule R (TopCat.of (↑X × ↑Y)) m : Type) := by

  obtain ⟨spl⟩ := KunnethTopological.kunnethShortExact_splitting R m X Y

  haveI : Module.Free R (KunnethTopological.kunnethTensorTerm R m X Y : Type) :=
    kunnethTensorTerm_free R m X Y hfree hfg
  haveI : Module.Free R (KunnethTopological.kunnethTorTerm R m X Y : Type) :=
    kunnethTorTerm_free R m X Y hfree hfg


  exact Module.Free.of_equiv'
    (Module.Free.of_equiv' (Module.Free.prod R _ _)
      (ModuleCat.biprodIsoProd
        (KunnethTopological.kunnethTensorTerm R m X Y)
        (KunnethTopological.kunnethTorTerm R m X Y)).toLinearEquiv.symm)
    spl.isoBinaryBiproduct.toLinearEquiv.symm

/-- Finiteness analogue of `kunnethTensorTerm_free`: the tensor term in the
homology Künneth sequence is finitely generated over `R` when each
`H_n(X; R)` is. -/
theorem kunnethTensorTerm_finite
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (m : ℕ) (X Y : TopCat.{0})
    (hfree : ∀ n, Module.Free R (singularHomologyModule R X n : Type))
    (hfg : ∀ n, Module.Finite R (singularHomologyModule R X n : Type)) :
    Module.Finite R (KunnethTopological.kunnethTensorTerm R m X Y : Type) := by sorry

/-- Finiteness analogue of `kunnethTorTerm_free`: the Tor term in the
homology Künneth sequence is finitely generated over `R`. -/
theorem kunnethTorTerm_finite
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (m : ℕ) (X Y : TopCat.{0})
    (hfree : ∀ n, Module.Free R (singularHomologyModule R X n : Type))
    (hfg : ∀ n, Module.Finite R (singularHomologyModule R X n : Type)) :
    Module.Finite R (KunnethTopological.kunnethTorTerm R m X Y : Type) := by sorry

/-- Companion of `productHomology_free`: `H_m(X × Y; R)` is finitely generated
over `R` whenever each `H_n(X; R)` is, using a splitting of the Künneth short
exact sequence. -/
theorem productHomology_finite
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (X Y : TopCat.{0})
    (hfree : ∀ n, Module.Free R (singularHomologyModule R X n : Type))
    (hfg : ∀ n, Module.Finite R (singularHomologyModule R X n : Type))
    (m : ℕ) :
    Module.Finite R (singularHomologyModule R (TopCat.of (↑X × ↑Y)) m : Type) := by

  obtain ⟨spl⟩ := KunnethTopological.kunnethShortExact_splitting R m X Y

  let iso := spl.isoBinaryBiproduct

  let e := iso.toLinearEquiv

  let e2 := (ModuleCat.biprodIsoProd
    (KunnethTopological.kunnethTensorTerm R m X Y)
    (KunnethTopological.kunnethTorTerm R m X Y)).toLinearEquiv

  haveI : Module.Finite R (KunnethTopological.kunnethTensorTerm R m X Y : Type) :=
    kunnethTensorTerm_finite R m X Y hfree hfg
  haveI : Module.Finite R (KunnethTopological.kunnethTorTerm R m X Y : Type) :=
    kunnethTorTerm_finite R m X Y hfree hfg

  exact Module.Finite.equiv (e2.symm.trans e.symm)

/-- The right edge `diagramRightMap` is bijective: under the freeness and
finiteness assumptions on `H_*(X; R)`, the product homology
`H_*(X × Y; R)` is also free and finitely generated, so the Kronecker pairing
on `X × Y` is a bijection in every degree, and bijectivity assembles to the
direct sum. -/
theorem diagramRightMap_bijective
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (X Y : TopCat.{0})
    (hfree : ∀ n, Module.Free R (singularHomologyModule R X n : Type))
    (hfg : ∀ n, Module.Finite R (singularHomologyModule R X n : Type)) :
    Function.Bijective (diagramRightMap R X Y hfree hfg) := by

  have hfreeXY : ∀ m, Module.Free R (singularHomologyModule R (TopCat.of (↑X × ↑Y)) m : Type) :=
    fun m => productHomology_free R X Y hfree hfg m
  have hfgXY : ∀ m, Module.Finite R (singularHomologyModule R (TopCat.of (↑X × ↑Y)) m : Type) :=
    fun m => productHomology_finite R X Y hfree hfg m

  have hbij : ∀ n, Function.Bijective (kroneckerPairing R (TopCat.of (↑X × ↑Y)) n) :=
    fun n => kroneckerPairing_bijective_of_free R (TopCat.of (↑X × ↑Y)) n hfreeXY hfgXY

  exact directSum_toModule_lof_comp_bijective
    (fun n => kroneckerPairing R (TopCat.of (↑X × ↑Y)) n) hbij

/-- Diagram-chase proof of the cohomology Künneth theorem: combining the
commutativity `diagram_comm` with the bijectivity of the left and right edges
forces the total cohomology cross product to be bijective. -/
theorem totalCohomologyCrossProduct_bijective_aux
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (X Y : TopCat.{0})
    (hfree : ∀ n, Module.Free R (singularHomologyModule R X n : Type))
    (hfg : ∀ n, Module.Finite R (singularHomologyModule R X n : Type)) :
    Function.Bijective (totalCohomologyCrossProduct R X Y) := by

  set φ := diagramLeftMap R X Y hfree hfg
  set ψ := diagramRightMap R X Y hfree hfg
  have hcomm : ψ.comp (totalCohomologyCrossProduct R X Y) = φ :=
    diagram_comm R X Y hfree hfg
  have hφ := diagramLeftMap_bijective R X Y hfree hfg
  have hψ := diagramRightMap_bijective R X Y hfree hfg

  have key : ∀ x, ψ (totalCohomologyCrossProduct R X Y x) = φ x := by
    intro x
    have := congr_arg (· x) hcomm
    simp only [LinearMap.comp_apply] at this
    exact this
  constructor
  ·
    intro x₁ x₂ heq
    exact hφ.1 (by rw [← key x₁, ← key x₂, heq])
  ·
    intro b
    obtain ⟨a, ha⟩ := hφ.2 (ψ b)
    exact ⟨a, hψ.1 (by rw [key a, ha])⟩

/-- The assembly map `⨁_{(p, q)} (H^p(X; R) ⊗ H^q(Y; R)) → H^*(X × Y; R)` built
from the bidegree cross-product components is bijective. This is extracted
from the bijectivity of the total cross product by cancelling the
tensor-direct-sum distributivity equivalence. -/
theorem assemblyEquiv
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (X Y : TopCat.{0})
    (hfree : ∀ n, Module.Free R (singularHomologyModule R X n : Type))
    (hfg : ∀ n, Module.Finite R (singularHomologyModule R X n : Type)) :
    Function.Bijective
      (DirectSum.toModule R (ℕ × ℕ)
        (totalSingularCohomology R (TopCat.of (↑X × ↑Y)))
        (componentCrossMap R X Y)) := by
  set assembly := DirectSum.toModule R (ℕ × ℕ)
    (totalSingularCohomology R (TopCat.of (↑X × ↑Y)))
    (componentCrossMap R X Y) with assembly_def
  set distrib := (TensorProduct.directSum R R
    (singularCohomologyFamily R X)
    (singularCohomologyFamily R Y)) with distrib_def
  have htotal := totalCohomologyCrossProduct_bijective_aux R X Y hfree hfg
  have hdistrib : Function.Bijective (⇑distrib.toLinearMap) :=
    distrib.bijective
  rwa [show totalCohomologyCrossProduct R X Y = assembly.comp distrib.toLinearMap from rfl,
    LinearMap.coe_comp, Function.Bijective.of_comp_iff (⇑assembly) hdistrib] at htotal

/-- **Cohomology Künneth theorem** (Theorem 33.3). Let `R` be a PID and
suppose every singular homology module `H_n(X; R)` is finitely generated and
free. Then the cohomology cross product
`× : H^*(X; R) ⊗_R H^*(Y; R) → H^*(X × Y; R)` is a bijection. -/
theorem totalCohomologyCrossProduct_bijective
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (X Y : TopCat.{0})
    (hfree : ∀ n, Module.Free R (singularHomologyModule R X n : Type))
    (hfg : ∀ n, Module.Finite R (singularHomologyModule R X n : Type)) :
    Function.Bijective (totalCohomologyCrossProduct R X Y) := by
  show Function.Bijective ((DirectSum.toModule R (ℕ × ℕ)
    (totalSingularCohomology R (TopCat.of (↑X × ↑Y)))
    (componentCrossMap R X Y)).comp
    (TensorProduct.directSum R R
      (singularCohomologyFamily R X)
      (singularCohomologyFamily R Y)).toLinearMap)
  rw [LinearMap.coe_comp]
  exact (assemblyEquiv R X Y hfree hfg).comp
    (TensorProduct.directSum R R
      (singularCohomologyFamily R X)
      (singularCohomologyFamily R Y)).bijective

end CohomologyKunneth

end
