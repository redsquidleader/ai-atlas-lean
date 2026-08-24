/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section26
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Projective

open CategoryTheory AlgebraicTopology Limits

noncomputable section

/-- **Definition 27.2.** The Ext-functor $\mathrm{Ext}^n_R(M, N)$ at level $n$, packaged
as a `ModuleCat R`. Concretely, this is the $n$-th cohomology of $\mathrm{Hom}_R(F_*, N)$
for any free resolution $0 \leftarrow M \leftarrow F_0 \leftarrow F_1 \leftarrow \cdots$,
realised here via the derived functor `Ext` on the abelian category of `R`-modules. -/
def ExtR (R : Type*) [CommRing R] (n : ℕ) (M N : ModuleCat R) : ModuleCat R :=
  ((Ext R (ModuleCat R) n).obj (Opposite.op M)).obj N

namespace UniversalCoefficientTheorem

/-- From an iso $A \oplus D \cong B$, manufacture a short exact sequence
$0 \to A \to B \to D \to 0$ together with a splitting. Used to package the UCT biproduct
decomposition as the split short exact sequence appearing in Theorem 27.1. -/
lemma splitting_from_biprod_iso
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    {A B D : C} [HasBinaryBiproduct A D] (φ : A ⊞ D ≅ B) :
    ∃ (S : ShortComplex C), S.X₁ = A ∧ S.X₂ = B ∧ S.X₃ = D ∧
      S.ShortExact ∧ Nonempty S.Splitting := by
  let S : ShortComplex C :=
    ShortComplex.mk (biprod.inl ≫ φ.hom) (φ.inv ≫ biprod.snd) (by simp)
  have split : S.Splitting := {
    r := φ.inv ≫ biprod.fst
    s := biprod.inr ≫ φ.hom
    f_r := by
      show (biprod.inl ≫ φ.hom) ≫ (φ.inv ≫ biprod.fst) = 𝟙 A
      simp [Category.assoc]
    s_g := by
      show (biprod.inr ≫ φ.hom) ≫ (φ.inv ≫ biprod.snd) = 𝟙 D
      simp [Category.assoc]
    id := by
      show (φ.inv ≫ biprod.fst) ≫ (biprod.inl ≫ φ.hom) +
           (φ.inv ≫ biprod.snd) ≫ (biprod.inr ≫ φ.hom) = 𝟙 B
      simp only [Category.assoc]
      rw [← Preadditive.comp_add, ← Category.assoc biprod.fst,
          ← Category.assoc biprod.snd, ← Preadditive.add_comp,
          biprod.total, Category.id_comp, Iso.inv_hom_id]
  }
  exact ⟨S, rfl, rfl, rfl, split.shortExact, ⟨split⟩⟩

/-- The underlying biproduct isomorphism behind the UCT: for a free chain complex $C_*$
over a PID $R$ and a coefficient module $N$, there is an iso
$\mathrm{Ext}^1(H_{n-1}, N) \oplus \mathrm{Hom}(H_n, N) \cong H^n(\mathrm{Hom}(C_*, N))$.
This is the unsplit form of Theorem 27.1, from which the split short exact sequence is
extracted by `splitting_from_biprod_iso`. -/
noncomputable def uct_iso
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (N : ModuleCat.{0} R)
    (hfree : ∀ i, Module.Free R (C.X i))
    (n : ℕ) :
    ((Ext R (ModuleCat.{0} R) 1).obj (Opposite.op (C.homology (n - 1)))).obj N ⊞
    ((Ext R (ModuleCat.{0} R) 0).obj (Opposite.op (C.homology n))).obj N ≅
    (C.linearYonedaObj R N).homology n := by sorry

/-- **Theorem 27.1 (Mixed-variance Universal Coefficient Theorem).** For a chain complex
$C_*$ of free $R$-modules over a PID $R$ and any coefficient module $N$, there is a
(non-naturally) split short exact sequence
$$0 \to \mathrm{Ext}^1_R(H_{n-1}(C_*), N) \to H^n(\mathrm{Hom}_R(C_*, N)) \to
   \mathrm{Hom}_R(H_n(C_*), N) \to 0.$$ -/
theorem cohomologyUCT
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (N : ModuleCat.{0} R)
    (hfree : ∀ i, Module.Free R (C.X i))
    (n : ℕ) :
    ∃ (S : ShortComplex (ModuleCat.{0} R)),
      S.X₁ = ((Ext R (ModuleCat.{0} R) 1).obj (Opposite.op (C.homology (n - 1)))).obj N ∧
      S.X₂ = (C.linearYonedaObj R N).homology n ∧
      S.X₃ = ((Ext R (ModuleCat.{0} R) 0).obj (Opposite.op (C.homology n))).obj N ∧
      S.ShortExact ∧
      Nonempty S.Splitting :=
  splitting_from_biprod_iso (uct_iso R C N hfree n)

/-- The cochain map $\mathrm{Hom}(D_*, N) \to \mathrm{Hom}(C_*, N)$ induced by a chain map
$\varphi : C_* \to D_*$, used to phrase naturality of the UCT in the chain-complex variable. -/
def uctInducedChainMap
    (R : Type) [CommRing R]
    {C D : ChainComplex (ModuleCat.{0} R) ℕ} (N : ModuleCat.{0} R) (φ : C ⟶ D) :
    D.linearYonedaObj R N ⟶ C.linearYonedaObj R N :=
  (HomologicalComplex.unopFunctor _ _).map
    ((((linearYoneda R (ModuleCat.{0} R)).obj N).rightOp.mapHomologicalComplex _).map φ).op

/-- The cochain map $\mathrm{Hom}(C_*, N) \to \mathrm{Hom}(C_*, N')$ induced by a coefficient
map $f : N \to N'$, used to phrase naturality of the UCT in the coefficient variable. -/
def uctInducedCoefficientMap
    (R : Type) [CommRing R]
    (C : ChainComplex (ModuleCat.{0} R) ℕ) {N N' : ModuleCat.{0} R} (f : N ⟶ N') :
    C.linearYonedaObj R N ⟶ C.linearYonedaObj R N' :=
  (HomologicalComplex.unopFunctor _ _).map
    (((((linearYoneda R (ModuleCat.{0} R)).map f).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)).app C).op)

/-- Naturality of the UCT biproduct isomorphism in the chain-complex variable: a chain map
$\varphi : C_* \to D_*$ induces compatible maps on $\mathrm{Ext}^1(H_{n-1}(-), N)$,
$\mathrm{Hom}(H_n(-), N)$, and $H^n(\mathrm{Hom}(-, N))$, making the obvious square commute. -/
theorem uct_iso_natural_chain
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (C D : ChainComplex (ModuleCat.{0} R) ℕ)
    (N : ModuleCat.{0} R)
    (hfreeC : ∀ i, Module.Free R (C.X i))
    (hfreeD : ∀ i, Module.Free R (D.X i))
    (φ : C ⟶ D)
    (n : ℕ) :
    (uct_iso R D N hfreeD n).hom ≫
      HomologicalComplex.homologyMap (uctInducedChainMap R N φ) n =
    biprod.map
      (((Ext R (ModuleCat.{0} R) 1).map
        (HomologicalComplex.homologyMap φ (n - 1)).op).app N)
      (((Ext R (ModuleCat.{0} R) 0).map
        (HomologicalComplex.homologyMap φ n).op).app N) ≫
    (uct_iso R C N hfreeC n).hom := by sorry

/-- Naturality of the UCT biproduct isomorphism in the coefficient variable: a coefficient
map $f : N \to N'$ induces compatible maps on $\mathrm{Ext}^1(H_{n-1}, -)$,
$\mathrm{Hom}(H_n, -)$, and $H^n(\mathrm{Hom}(C_*, -))$, making the obvious square commute. -/
theorem uct_iso_natural_coeff
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (N N' : ModuleCat.{0} R)
    (hfree : ∀ i, Module.Free R (C.X i))
    (f : N ⟶ N')
    (n : ℕ) :
    (uct_iso R C N hfree n).hom ≫
      HomologicalComplex.homologyMap (uctInducedCoefficientMap R C f) n =
    biprod.map
      (((Ext R (ModuleCat.{0} R) 1).obj
        (Opposite.op (C.homology (n - 1)))).map f)
      (((Ext R (ModuleCat.{0} R) 0).obj
        (Opposite.op (C.homology n))).map f) ≫
    (uct_iso R C N' hfree n).hom := by sorry

end UniversalCoefficientTheorem

namespace SingularCohomology

/-- The cap product $\cap : H^p(X; R) \otimes H_n(X; R) \to H_{n-p}(X; R)$ expressed as
the curried $R$-bilinear map $H^p(X; R) \to (H_n(X; R) \to H_{n-p}(X; R))$. Used downstream
for capping with the fundamental class in Poincaré duality. -/
noncomputable def capProduct (R : Type) [CommRing R] (X : TopCat.{0}) (n p : ℕ) :
    (singularCohomology R X (ModuleCat.of R R) p : Type) →ₗ[R]
    (singularHomologyModule R X n : Type) →ₗ[R]
    (singularHomologyModule R X (n - p) : Type) := by sorry


/-- The singular chain complex $S_*(X; R)$ of a topological space $X$ with coefficients in
$R$, packaged as a chain complex of `R`-modules indexed by `ℕ`. -/
abbrev singularChains (R : Type) [CommRing R] (X : TopCat.{0}) :
    ChainComplex (ModuleCat.{0} R) ℕ :=
  ((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj X

/-- Each module of singular chains $S_i(X; R)$ is free over $R$ (with basis the singular
$i$-simplices). This is the hypothesis needed to apply the UCT (`cohomologyUCT`) to the
singular chain complex. -/
theorem singularChains_free
    (R : Type) [CommRing R] (X : TopCat.{0}) (i : ℕ) :
    Module.Free R ((singularChains R X).X i) := by sorry

end SingularCohomology
