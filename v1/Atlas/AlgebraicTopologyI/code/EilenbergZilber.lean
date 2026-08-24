/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.Category.TopCat.Monoidal

open CategoryTheory MonoidalCategory AlgebraicTopology

noncomputable section

namespace EilenbergZilber

universe u

/-- The singular chain complex of a topological space $X$ with coefficients in an
$R$-module $M$, viewed as a chain complex of $R$-modules. -/
noncomputable def singularChainComplex
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (X : TopCat.{u}) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj M).obj X


/-- **Theorem 25.13 (Eilenberg–Zilber theorem)**. There is a natural chain homotopy
equivalence
$$S_*(X; M) \otimes S_*(Y; M) \simeq S_*(X \times Y; M)$$
covering the canonical isomorphism in degree $0$. This packaged form provides both the
forward (shuffle) map and a chain homotopy inverse (Alexander–Whitney), unique up to
chain homotopy. -/
noncomputable def eilenbergZilber_homotopyEquiv
    {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (X Y : TopCat.{u}) :
    HomotopyEquiv
      (HomologicalComplex.tensorObj
        (singularChainComplex M X)
        (singularChainComplex M Y))
      (singularChainComplex M (X ⊗ Y)) := by sorry


/-- Uniqueness part of **Theorem 25.13**: any chain map
$S_*(X; M) \otimes S_*(Y; M) \to S_*(X \times Y; M)$ that agrees with the Eilenberg–Zilber
map on $H_0$ is chain homotopic to it. A direct consequence of the acyclic models
theorem. -/
theorem eilenbergZilber_unique
    {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (X Y : TopCat.{u})
    (φ fwd : HomologicalComplex.tensorObj
        (singularChainComplex M X)
        (singularChainComplex M Y) ⟶
      singularChainComplex M (X ⊗ Y))
    (hfwd : fwd = (eilenbergZilber_homotopyEquiv M X Y).hom)
    (hφ : HomologicalComplex.homologyMap φ 0 =
      HomologicalComplex.homologyMap fwd 0) :
    Nonempty (Homotopy φ fwd) := by sorry


/-- Dual uniqueness statement to `eilenbergZilber_unique`: any chain map
$S_*(X \times Y; M) \to S_*(X; M) \otimes S_*(Y; M)$ that agrees with the Alexander–Whitney
map on $H_0$ is chain homotopic to it. Together with `eilenbergZilber_unique` this gives
the uniqueness clause of Theorem 25.13. -/
theorem alexanderWhitney_unique
    {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (X Y : TopCat.{u})
    (ψ bwd : singularChainComplex M (X ⊗ Y) ⟶
      HomologicalComplex.tensorObj
        (singularChainComplex M X)
        (singularChainComplex M Y))
    (hbwd : bwd = (eilenbergZilber_homotopyEquiv M X Y).inv)
    (hψ : HomologicalComplex.homologyMap ψ 0 =
      HomologicalComplex.homologyMap bwd 0) :
    Nonempty (Homotopy ψ bwd) := by sorry


/-- Naturality of the Eilenberg–Zilber map: the forward map
$S_*(X) \otimes S_*(Y) \to S_*(X \times Y)$ commutes with maps $f : X \to X'$ and
$g : Y \to Y'$ on each side of the square. -/
theorem eilenbergZilber_natural
    {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) {X X' Y Y' : TopCat.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    HomologicalComplex.tensorHom
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj M).map f)
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj M).map g) ≫
      (eilenbergZilber_homotopyEquiv M X' Y').hom =
    (eilenbergZilber_homotopyEquiv M X Y).hom ≫
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj M).map
        (MonoidalCategory.tensorHom f g)) := by sorry

/-- **Corollary 25.14**. The induced isomorphism on homology from the Eilenberg–Zilber
chain homotopy equivalence:
$$H_n\bigl(S_*(X; M) \otimes S_*(Y; M)\bigr) \;\cong\; H_n(X \times Y; M).$$ -/
noncomputable def eilenbergZilberHomologyIso
    {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (X Y : TopCat.{u}) (n : ℕ) :
    (HomologicalComplex.tensorObj
      (singularChainComplex M X)
      (singularChainComplex M Y)).homology n ≅
    (singularChainComplex M (X ⊗ Y)).homology n :=
  (eilenbergZilber_homotopyEquiv M X Y).toHomologyIso n

end EilenbergZilber
