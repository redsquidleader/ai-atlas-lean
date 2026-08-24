/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.RingTheory.Flat.CategoryTheory

open CategoryTheory MonoidalCategory Limits

noncomputable section

namespace UniversalCoefficientTheorem

/-- The chain complex obtained from $C_*$ by tensoring degreewise on the right with the
$R$-module $M$: $(C_* \otimes M)_n = C_n \otimes M$ with the induced differential. -/
def tensorComplex (R : Type*) [CommRing R] (C : ChainComplex (ModuleCat R) ℕ)
    (M : ModuleCat R) : ChainComplex (ModuleCat R) ℕ :=
  (((tensoringRight (ModuleCat R)).obj M).mapHomologicalComplex (ComplexShape.down ℕ)).obj C

/-- Functoriality of `tensorComplex` in the chain complex argument: a chain map
$\varphi : C \to D$ tensored with the identity on $M$. -/
def tensorComplexMap (R : Type*) [CommRing R] {C D : ChainComplex (ModuleCat R) ℕ}
    (φ : C ⟶ D) (M : ModuleCat R) : tensorComplex R C M ⟶ tensorComplex R D M :=
  (((tensoringRight (ModuleCat R)).obj M).mapHomologicalComplex (ComplexShape.down ℕ)).map φ

/-- Tensoring on the right with a fixed module $M$ preserves colimits; obtained by
transporting along the symmetry isomorphism with `tensorLeft M`. -/
instance tensorRight_preservesColimits (R : Type*) [CommRing R] (M : ModuleCat R) :
    PreservesColimits ((tensoringRight (ModuleCat R)).obj M) := by
  change PreservesColimits (tensorRight M)
  exact preservesColimits_of_natIso
    (NatIso.ofComponents (fun X => (_root_.CategoryTheory.BraidedCategory.braiding M X))
      (fun {X Y} f => _root_.CategoryTheory.BraidedCategory.braiding_naturality_right M f) :
      tensorLeft M ≅ tensorRight M)

/-- In the downward $\mathbb{N}$-indexed complex shape, the successor `n + 1` has
`next = n`. -/
lemma down_next_succ (n : ℕ) : (ComplexShape.down ℕ).next (n + 1) = n :=
  ComplexShape.next_eq' _ (ComplexShape.down_mk (n + 1) n (by omega))

/-- In the downward $\mathbb{N}$-indexed complex shape, the successor `n + 1` has
`prev = n + 2`. -/
lemma down_prev_succ (n : ℕ) : (ComplexShape.down ℕ).prev (n + 1) = n + 2 :=
  ComplexShape.prev_eq' _ (ComplexShape.down_mk (n + 2) (n + 1) (by omega))

/-- The image of the cycles inclusion $Z_{n+1}(C) \hookrightarrow C_{n+1}$ under the
functor $- \otimes M$ vanishes when followed by the differential of $C \otimes M$. Used
to lift the cycles into the homology of the tensor complex. -/
lemma iCycles_tensor_comp_d (R : Type*) [CommRing R] (M : ModuleCat R)
    (n : ℕ) (C : ChainComplex (ModuleCat R) ℕ) :
    ((tensoringRight (ModuleCat R)).obj M).map (C.iCycles (n + 1)) ≫
      (tensorComplex R C M).d (n + 1) n = 0 := by
  change _ ≫ ((tensoringRight (ModuleCat R)).obj M).map (C.d (n + 1) n) = 0
  rw [← ((tensoringRight (ModuleCat R)).obj M).map_comp,
    HomologicalComplex.iCycles_d, Functor.map_zero]

/-- The map $Z_{n+1}(C) \otimes M \to H_{n+1}(C \otimes M)$ obtained by lifting through
the cycles of the tensor complex and then quotienting by boundaries. This is the building
block of the UCT map $\alpha$. -/
def cyclesToHomologyTC (R : Type*) [CommRing R] (M : ModuleCat R)
    (n : ℕ) (C : ChainComplex (ModuleCat R) ℕ) :
    ((tensoringRight (ModuleCat R)).obj M).obj (C.cycles (n + 1)) ⟶
      (tensorComplex R C M).homology (n + 1) :=
  (tensorComplex R C M).liftCycles
    (((tensoringRight (ModuleCat R)).obj M).map (C.iCycles (n + 1)))
    n (down_next_succ n) (iCycles_tensor_comp_d R M n C) ≫
  (tensorComplex R C M).homologyπ (n + 1)

/-- The composition of the canonical map into cycles with `cyclesToHomologyTC` vanishes;
i.e. boundaries are killed. This is the relation needed to descend `cyclesToHomologyTC`
along the cokernel description of homology. -/
lemma toCycles_comp_cyclesToHomologyTC (R : Type*) [CommRing R] (M : ModuleCat R)
    (n : ℕ) (C : ChainComplex (ModuleCat R) ℕ) :
    ((tensoringRight (ModuleCat R)).obj M).map (C.toCycles (n + 2) (n + 1)) ≫
      cyclesToHomologyTC R M n C = 0 := by
  simp only [cyclesToHomologyTC, ← Category.assoc]
  rw [HomologicalComplex.comp_liftCycles]
  refine HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary
    (tensorComplex R C M) _ n (down_next_succ n) (𝟙 _) ?_
  rw [Category.id_comp]
  change ((tensoringRight (ModuleCat R)).obj M).map (C.toCycles (n + 2) (n + 1)) ≫
    ((tensoringRight (ModuleCat R)).obj M).map (C.iCycles (n + 1)) =
    ((tensoringRight (ModuleCat R)).obj M).map (C.d (n + 2) (n + 1))
  rw [← ((tensoringRight (ModuleCat R)).obj M).map_comp, HomologicalComplex.toCycles_i]

/-- The UCT map $\alpha : H_{n+1}(C) \otimes M \to H_{n+1}(C \otimes M)$, defined by
descending the cycles-to-homology map through the cokernel presentation of $H_{n+1}(C)$
(valid because tensoring with $M$ preserves the relevant cokernel for free $C$). -/
def uctAlpha (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (M : ModuleCat R) (n : ℕ)
    (C : ChainComplex (ModuleCat R) ℕ) (_hfree : ∀ i, Module.Free R (C.X i)) :
    C.homology (n + 1) ⊗ M ⟶ (tensorComplex R C M).homology (n + 1) := by
  have hcokerF := isColimitCoforkMapOfIsColimit'
    ((tensoringRight (ModuleCat R)).obj M)
    (C.toCycles_comp_homologyπ (n + 2) (n + 1))
    (C.homologyIsCokernel (n + 2) (n + 1) (down_prev_succ n))
  exact (Cofork.IsColimit.desc' hcokerF
    (cyclesToHomologyTC R M n C)
    (by rw [toCycles_comp_cyclesToHomologyTC, zero_comp])).1

/-- The defining property of `uctAlpha`: precomposing with the canonical projection from
cycles to homology recovers the basic `cyclesToHomologyTC` map. This is the universal
property of the cokernel description of homology. -/
@[reassoc (attr := simp)]
lemma homologyπ_comp_uctAlpha (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (M : ModuleCat R) (n : ℕ) (C : ChainComplex (ModuleCat R) ℕ)
    (hfree : ∀ i, Module.Free R (C.X i)) :
    ((tensoringRight (ModuleCat R)).obj M).map (C.homologyπ (n + 1)) ≫
      uctAlpha R M n C hfree = cyclesToHomologyTC R M n C := by
  have := (Cofork.IsColimit.desc'
    (isColimitCoforkMapOfIsColimit' ((tensoringRight (ModuleCat R)).obj M)
      (C.toCycles_comp_homologyπ (n + 2) (n + 1))
      (C.homologyIsCokernel (n + 2) (n + 1) (down_prev_succ n)))
    (cyclesToHomologyTC R M n C)
    (by rw [toCycles_comp_cyclesToHomologyTC, zero_comp])).2
  simp only [CokernelCofork.π_ofπ] at this
  exact this


set_option maxHeartbeats 800000 in
/-- Naturality of the UCT map $\alpha$ in the chain complex variable: $\alpha$ commutes
with the maps induced by a chain map $\varphi : C \to D$ between free chain complexes. -/
theorem uctAlpha_natural (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (M : ModuleCat R) (n : ℕ)
    (C D : ChainComplex (ModuleCat R) ℕ)
    (hfreeC : ∀ i, Module.Free R (C.X i)) (hfreeD : ∀ i, Module.Free R (D.X i))
    (φ : C ⟶ D) :
    uctAlpha R M n C hfreeC ≫ HomologicalComplex.homologyMap (tensorComplexMap R φ M) (n + 1) =
      ((tensoringRight (ModuleCat R)).obj M).map (HomologicalComplex.homologyMap φ (n + 1)) ≫
        uctAlpha R M n D hfreeD := by

  have hcokerFC := isColimitCoforkMapOfIsColimit' ((tensoringRight (ModuleCat R)).obj M)
    (C.toCycles_comp_homologyπ (n + 2) (n + 1))
    (C.homologyIsCokernel (n + 2) (n + 1) (down_prev_succ n))
  apply Cofork.IsColimit.hom_ext hcokerFC
  simp only [CokernelCofork.π_ofπ]

  erw [homologyπ_comp_uctAlpha_assoc,
    ← ((tensoringRight (ModuleCat R)).obj M).map_comp_assoc,
    HomologicalComplex.homologyπ_naturality,
    ((tensoringRight (ModuleCat R)).obj M).map_comp_assoc,
    homologyπ_comp_uctAlpha]

  simp only [cyclesToHomologyTC, Category.assoc, HomologicalComplex.homologyπ_naturality]
  rw [HomologicalComplex.liftCycles_comp_cyclesMap_assoc,
    HomologicalComplex.comp_liftCycles_assoc]
  congr 2
  change ((tensoringRight (ModuleCat R)).obj M).map (C.iCycles (n + 1)) ≫
      ((tensoringRight (ModuleCat R)).obj M).map (φ.f (n + 1)) =
    ((tensoringRight (ModuleCat R)).obj M).map (HomologicalComplex.cyclesMap φ (n + 1)) ≫
      ((tensoringRight (ModuleCat R)).obj M).map (D.iCycles (n + 1))
  rw [← ((tensoringRight (ModuleCat R)).obj M).map_comp,
    ← ((tensoringRight (ModuleCat R)).obj M).map_comp,
    HomologicalComplex.cyclesMap_i]

/-- Packaged data of the **Universal Coefficient Theorem** in degree $n+1$: for every
free chain complex $C_*$ over a PID $R$ and every $R$-module $M$, a natural split short
exact sequence
$$0 \to H_{n+1}(C_*) \otimes M \xrightarrow{\alpha} H_{n+1}(C_* \otimes M) \xrightarrow{\beta} \operatorname{Tor}_1^R(H_n(C_*), M) \to 0,$$
together with naturality of $\alpha$ and $\beta$ in $C_*$. -/
structure NaturalUCTData (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (M : ModuleCat R) (n : ℕ) where
  α : (C : ChainComplex (ModuleCat R) ℕ) → (∀ i, Module.Free R (C.X i)) →
    (C.homology (n + 1) ⊗ M ⟶ (tensorComplex R C M).homology (n + 1))
  β : (C : ChainComplex (ModuleCat R) ℕ) → (∀ i, Module.Free R (C.X i)) →
    ((tensorComplex R C M).homology (n + 1) ⟶ ((Tor (ModuleCat R) 1).obj (C.homology n)).obj M)
  zero : ∀ (C : ChainComplex (ModuleCat R) ℕ) (hfree : ∀ i, Module.Free R (C.X i)),
    α C hfree ≫ β C hfree = 0
  shortExact : ∀ (C : ChainComplex (ModuleCat R) ℕ) (hfree : ∀ i, Module.Free R (C.X i)),
    (ShortComplex.mk (α C hfree) (β C hfree) (zero C hfree)).ShortExact
  splitting : ∀ (C : ChainComplex (ModuleCat R) ℕ) (hfree : ∀ i, Module.Free R (C.X i)),
    Nonempty (ShortComplex.mk (α C hfree) (β C hfree) (zero C hfree)).Splitting
  α_natural : ∀ (C D : ChainComplex (ModuleCat R) ℕ)
    (hfreeC : ∀ i, Module.Free R (C.X i)) (hfreeD : ∀ i, Module.Free R (D.X i))
    (φ : C ⟶ D),
    α C hfreeC ≫ HomologicalComplex.homologyMap (tensorComplexMap R φ M) (n + 1) =
      ((tensoringRight (ModuleCat R)).obj M).map (HomologicalComplex.homologyMap φ (n + 1)) ≫
        α D hfreeD
  β_natural : ∀ (C D : ChainComplex (ModuleCat R) ℕ)
    (hfreeC : ∀ i, Module.Free R (C.X i)) (hfreeD : ∀ i, Module.Free R (D.X i))
    (φ : C ⟶ D),
    β C hfreeC ≫ ((Tor (ModuleCat R) 1).map (HomologicalComplex.homologyMap φ n)).app M =
      HomologicalComplex.homologyMap (tensorComplexMap R φ M) (n + 1) ≫ β D hfreeD

/-- Tor as the homology of a projective resolution: for any projective resolution $P_\bullet$
of $M$,
$$\operatorname{Tor}_1(X, M) \cong H_1(X \otimes P_\bullet).$$
Used to identify the connecting map of the UCT short exact sequence with the Tor term. -/
noncomputable def torIsoHomology (R : Type*) [CommRing R]
    [HasProjectiveResolutions (ModuleCat R)]
    (X M : ModuleCat R) (P : ProjectiveResolution M) :
    ((Tor (ModuleCat R) 1).obj X).obj M ≅
      (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 1).obj
        ((((tensoringLeft (ModuleCat R)).obj X).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj P.complex) :=
  P.isoLeftDerivedObj ((tensoringLeft (ModuleCat R)).obj X) 1

/-- In a projective resolution $P_\bullet \to M$, the composition $d_1 \circ \pi_0 = 0$:
the augmentation kills the image of the first differential. -/
lemma res_d_comp_pi_zero (R : Type*) [CommRing R] (M : ModuleCat R)
    (P : ProjectiveResolution M) : P.complex.d 1 0 ≫ P.π.f 0 = 0 := by
  have h := P.π.comm 1 0; simp at h; exact h.symm

/-- The short complex of chain complexes obtained by tensoring $C_*$ degreewise with the
short exact sequence $0 \to P_1 \to P_0 \to M \to 0$ extracted from a projective resolution
$P_\bullet$ of $M$. -/
def resSES (R : Type*) [CommRing R]
    (C : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R)
    (P : ProjectiveResolution M) :
    CategoryTheory.ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  CategoryTheory.ShortComplex.mk
    ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat R)).map (P.complex.d 1 0))
      (ComplexShape.down ℕ)).app C)
    ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat R)).map (P.π.f 0))
      (ComplexShape.down ℕ)).app C)
    (by
      rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
        ← (tensoringRight (ModuleCat R)).map_comp, res_d_comp_pi_zero R M P, Functor.map_zero]
      ext i : 1
      simp only [NatTrans.mapHomologicalComplex, HomologicalComplex.zero_f_apply]
      rfl)


/-- Over a PID, every projective resolution of an $R$-module can be chosen to have
length one, so $d_{2,1} = 0$. Used to upgrade the right end of `resSES` into a short
exact sequence. -/
theorem projRes_d_two_one_eq_zero (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (M : ModuleCat R) (P : ProjectiveResolution M) :
    P.complex.d 2 1 = 0 := by sorry

/-- Consequence of `projRes_d_two_one_eq_zero`: in a PID projective resolution the map
$P_1 \to P_0$ is a monomorphism, so $0 \to P_1 \to P_0 \to M \to 0$ is short exact. -/
theorem projRes_mono_d_one_zero (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (M : ModuleCat R) (P : ProjectiveResolution M) :
    Mono (P.complex.d 1 0) := by
  have hexact := P.exact_succ 0
  rw [show P.complex.d 1 0 = (CategoryTheory.ShortComplex.mk (P.complex.d 2 1) (P.complex.d 1 0)
    (P.complex.d_comp_d 2 1 0)).g from rfl]
  rw [hexact.mono_g_iff]
  exact projRes_d_two_one_eq_zero R M P

/-- For a free chain complex $C_*$ over a PID and a projective resolution $P_\bullet$ of
$M$, the short complex `resSES R C M P` obtained by tensoring with the length-one
resolution is short exact in every degree. -/
theorem resSES_shortExact (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (C : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R)
    (P : ProjectiveResolution M) (hfree : ∀ i, Module.Free R (C.X i)) :
    (resSES R C M P).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  haveI : Module.Free R (C.X i) := hfree i
  have hse : (CategoryTheory.ShortComplex.mk (P.complex.d 1 0) (P.π.f 0)
      (res_d_comp_pi_zero R M P)).ShortExact := by
    refine CategoryTheory.ShortComplex.ShortExact.mk' P.exact₀ ?_ inferInstance
    show Mono (P.complex.d 1 0)
    exact projRes_mono_d_one_zero R M P
  show ((resSES R C M P).map
    (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) i)).ShortExact
  exact (show (resSES R C M P).map
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) i) =
    (CategoryTheory.ShortComplex.mk (P.complex.d 1 0) (P.π.f 0)
      (res_d_comp_pi_zero R M P)).map (tensorLeft (C.X i)) from rfl) ▸
    hse.map_of_exact (tensorLeft (C.X i))

/-- The natural identification of the homology in degree $n$ of the chain complex
$C_* \otimes P_1$ with $\operatorname{Tor}_1^R(H_n(C_*), M)$, where $P_\bullet$ is a
projective (in fact length-one) resolution of $M$. -/
noncomputable def torIdentification (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (C : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R)
    (P : ProjectiveResolution M) (hfree : ∀ i, Module.Free R (C.X i)) (n : ℕ) :
    (tensorComplex R C (P.complex.X 1)).homology n ⟶
      ((Tor (ModuleCat R) 1).obj (C.homology n)).obj M := by sorry

/-- Naturality of `torIdentification` in the chain complex variable. -/
theorem torIdentification_natural (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (M : ModuleCat R) (n : ℕ)
    (C D : ChainComplex (ModuleCat R) ℕ)
    (P : ProjectiveResolution M)
    (hfreeC : ∀ i, Module.Free R (C.X i))
    (hfreeD : ∀ i, Module.Free R (D.X i))
    (φ : C ⟶ D) :
    torIdentification R C M P hfreeC n ≫
      ((Tor (ModuleCat R) 1).map (HomologicalComplex.homologyMap φ n)).app M =
    HomologicalComplex.homologyMap (tensorComplexMap R φ (P.complex.X 1)) n ≫
      torIdentification R D M P hfreeD n := by sorry

/-- The UCT connecting map
$\beta : H_{n+1}(C_* \otimes M) \to \operatorname{Tor}_1^R(H_n(C_*), M)$,
built as the connecting homomorphism of `resSES` composed with `torIdentification`. -/
def uctBeta (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (M : ModuleCat R) (n : ℕ)
    (C : ChainComplex (ModuleCat R) ℕ) (hfree : ∀ i, Module.Free R (C.X i)) :
    (tensorComplex R C M).homology (n + 1) ⟶ ((Tor (ModuleCat R) 1).obj (C.homology n)).obj M :=
  let P := ProjectiveResolution.of M
  (resSES_shortExact R C M P hfree).δ (n + 1) n
    (ComplexShape.down_mk (n + 1) n (by omega)) ≫
  torIdentification R C M P hfree n

/-- Naturality of `cyclesToHomologyTC` in the module variable $M$: the construction
commutes with maps $f : M_1 \to M_2$. Used to relate $\alpha$ with the connecting map
of the tensored resolution. -/
lemma cyclesToHomologyTC_naturality (R : Type*) [CommRing R]
    {M₁ M₂ : ModuleCat R} (f : M₁ ⟶ M₂)
    (n : ℕ) (C : ChainComplex (ModuleCat R) ℕ) :
    ((tensoringRight (ModuleCat R)).map f).app (C.cycles (n + 1)) ≫
      cyclesToHomologyTC R M₂ n C =
    cyclesToHomologyTC R M₁ n C ≫
      HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat R)).map f)
          (ComplexShape.down ℕ)).app C) (n + 1) := by
  simp only [cyclesToHomologyTC, Category.assoc]
  erw [HomologicalComplex.homologyπ_naturality]
  rw [HomologicalComplex.liftCycles_comp_cyclesMap_assoc,
    HomologicalComplex.comp_liftCycles_assoc]
  congr 2
  exact (((tensoringRight (ModuleCat R)).map f).naturality (C.iCycles (n + 1))).symm

set_option maxHeartbeats 800000 in
/-- The composition $\beta \circ \alpha = 0$, i.e. the maps in the UCT short complex
form a complex. -/
theorem uctAlpha_comp_uctBeta (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (M : ModuleCat R) (n : ℕ)
    (C : ChainComplex (ModuleCat R) ℕ) (hfree : ∀ i, Module.Free R (C.X i)) :
    uctAlpha R M n C hfree ≫ uctBeta R M n C hfree = 0 := by

  have hcokerF := isColimitCoforkMapOfIsColimit'
    ((tensoringRight (ModuleCat R)).obj M)
    (C.toCycles_comp_homologyπ (n + 2) (n + 1))
    (C.homologyIsCokernel (n + 2) (n + 1) (down_prev_succ n))
  apply Cofork.IsColimit.hom_ext hcokerF
  simp only [CokernelCofork.π_ofπ]

  erw [homologyπ_comp_uctAlpha_assoc]


  show cyclesToHomologyTC R M n C ≫ uctBeta R M n C hfree = 0
  unfold uctBeta


  suffices h : cyclesToHomologyTC R M n C ≫
      (resSES_shortExact R C M (ProjectiveResolution.of M) hfree).δ (n + 1) n
        (ComplexShape.down_mk (n + 1) n (by omega)) = 0 by
    rw [reassoc_of% h, zero_comp]

  set P := ProjectiveResolution.of M

  have hη : Epi (((tensoringRight (ModuleCat R)).map (P.π.f 0)).app (C.cycles (n + 1))) := by
    change Epi ((tensorLeft (C.cycles (n + 1))).map (P.π.f 0))
    exact preserves_epi_of_preservesColimit _ _

  haveI := hη
  have key : ((tensoringRight (ModuleCat R)).map (P.π.f 0)).app (C.cycles (n + 1)) ≫
      (cyclesToHomologyTC R M n C ≫
        (resSES_shortExact R C M P hfree).δ (n + 1) n
          (ComplexShape.down_mk (n + 1) n (by omega))) = 0 := by

    have hnat := cyclesToHomologyTC_naturality R (P.π.f 0) n C
    simp only [← Category.assoc]
    rw [show ((tensoringRight (ModuleCat R)).map (P.π.f 0)).app (C.cycles (n + 1)) ≫
        cyclesToHomologyTC R M n C =
      cyclesToHomologyTC R (P.complex.X 0) n C ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat R)).map (P.π.f 0))
            (ComplexShape.down ℕ)).app C) (n + 1) from hnat]


    have hδ := (resSES_shortExact R C M P hfree).comp_δ (n + 1) n
      (ComplexShape.down_mk (n + 1) n (by omega))
    erw [Category.assoc, hδ, comp_zero]
  exact ((cancel_epi (((tensoringRight (ModuleCat R)).map (P.π.f 0)).app
    (C.cycles (n + 1)))).mp (key.trans (comp_zero).symm))


/-- For a free chain complex over a PID, the cokernel of $Z_n \hookrightarrow C_n$ — i.e.
the boundary group $B_{n-1}(C)$ identified inside $C_{n-1}$ — is projective. This rests
on the fact that submodules of free modules over a PID are free. -/
theorem cokernel_iCycles_projective (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (C : ChainComplex (ModuleCat R) ℕ) (hfree : ∀ i, Module.Free R (C.X i)) (n : ℕ) :
    Projective (cokernel (C.iCycles n)) := by sorry

/-- A splitting of the inclusion $Z_n(C) \hookrightarrow C_n$ for a free chain complex
over a PID, obtained from the short exact sequence
$0 \to Z_n \to C_n \to \mathrm{cok}(Z_n \hookrightarrow C_n) \to 0$ together with
projectivity of the cokernel. -/
def iCycles_splitMono (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (C : ChainComplex (ModuleCat R) ℕ) (hfree : ∀ i, Module.Free R (C.X i)) (n : ℕ) :
    SplitMono (C.iCycles n) := by

  set S := ShortComplex.mk (C.iCycles n) (cokernel.π (C.iCycles n)) (by simp)
  have hSE : S.ShortExact :=
    { exact := ShortComplex.exact_cokernel (C.iCycles n)
      mono_f := inferInstance
      epi_g := inferInstance }

  haveI : Projective S.X₃ := cokernel_iCycles_projective R C hfree n

  exact (hSE.splittingOfProjective).splitMono_f


/-- Noncomputable variant of `iCycles_splitMono`: the same splitting of
$Z_n(C) \hookrightarrow C_n$, packaged for use in contexts where computability is not
required. -/
noncomputable def iCycles_splitMono' (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (C : ChainComplex (ModuleCat R) ℕ) (hfree : ∀ i, Module.Free R (C.X i)) (n : ℕ) :
    SplitMono (C.iCycles n) := by sorry

set_option maxHeartbeats 800000 in
/-- A retraction (split-mono witness) of the UCT map $\alpha_n$, constructed from a
splitting of $Z_{n+1}(C) \hookrightarrow C_{n+1}$. This is the key ingredient making the
UCT short exact sequence split. -/
def uctAlpha_retraction (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (M : ModuleCat R) (n : ℕ)
    (C : ChainComplex (ModuleCat R) ℕ) (hfree : ∀ i, Module.Free R (C.X i)) :
    SplitMono (uctAlpha R M n C hfree) := by
  set F := (tensoringRight (ModuleCat R)).obj M
  set TC := tensorComplex R C M


  have hsm : SplitMono (C.iCycles (n + 1)) := iCycles_splitMono' R C hfree (n + 1)
  let ret := hsm.retraction
  have hret : C.iCycles (n + 1) ≫ ret = 𝟙 _ := hsm.id


  set k := TC.iCycles (n + 1) ≫ F.map (ret ≫ C.homologyπ (n + 1))

  have hk : TC.toCycles (n + 2) (n + 1) ≫ k = 0 := by
    simp only [k, ← Category.assoc]
    rw [HomologicalComplex.toCycles_i]
    change F.map (C.d (n + 2) (n + 1)) ≫ F.map (ret ≫ C.homologyπ (n + 1)) = 0
    rw [← F.map_comp]
    have h1 : C.d (n + 2) (n + 1) ≫ ret ≫ C.homologyπ (n + 1) = 0 := by
      rw [show C.d (n + 2) (n + 1) = C.toCycles (n + 2) (n + 1) ≫ C.iCycles (n + 1)
        from (HomologicalComplex.toCycles_i C (n + 2) (n + 1)).symm]
      slice_lhs 2 3 => rw [hret]
      simp [HomologicalComplex.toCycles_comp_homologyπ]
    rw [h1, F.map_zero]

  have hcoker := TC.homologyIsCokernel (n + 2) (n + 1) (down_prev_succ n)
  set desc := CokernelCofork.IsColimit.desc' hcoker k hk

  refine ⟨desc.1, ?_⟩


  haveI hEpi : Epi (F.map (C.homologyπ (n + 1))) := Functor.map_epi F (C.homologyπ (n + 1))
  have key : F.map (C.homologyπ (n + 1)) ≫ (uctAlpha R M n C hfree ≫ desc.val) =
      F.map (C.homologyπ (n + 1)) := by
    rw [← Category.assoc, homologyπ_comp_uctAlpha]
    simp only [cyclesToHomologyTC, Category.assoc]
    have hdesc2 : TC.homologyπ (n + 1) ≫ desc.val = k := by
      have := desc.property
      simp only [CokernelCofork.π_ofπ] at this
      exact this
    rw [hdesc2]
    simp only [k, ← Category.assoc]
    rw [HomologicalComplex.liftCycles_i]
    change F.map (C.iCycles (n + 1)) ≫ F.map (ret ≫ C.homologyπ (n + 1)) =
      F.map (C.homologyπ (n + 1))
    rw [← F.map_comp]
    congr 1

    slice_lhs 1 2 => rw [hret]
    simp
  exact (cancel_epi (F.map (C.homologyπ (n + 1)))).mp
    (key.trans (Category.comp_id _).symm)

/-- The identification of $\mathrm{Tor}_1(H_n(C), M)$ with a kernel of an induced
homology map is an isomorphism on the relevant kernel, providing the bridge between the
abstract Tor functor and the concrete connecting homomorphism appearing in the UCT. -/
theorem torIdentification_iso_on_kernel (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (C : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R)
    (P : ProjectiveResolution M) (hfree : ∀ i, Module.Free R (C.X i)) (n : ℕ) :
    IsIso (Limits.kernel.ι (HomologicalComplex.homologyMap (resSES R C M P).f n) ≫
      torIdentification R C M P hfree n) := by sorry

/-- The UCT map $\beta_n : H_{n+1}(C \otimes M) \to \mathrm{Tor}_1(H_n(C), M)$ is an
epimorphism. This is the surjectivity claim in the UCT short exact sequence. -/
theorem uctBeta_epi (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (M : ModuleCat R) (n : ℕ)
    (C : ChainComplex (ModuleCat R) ℕ) (hfree : ∀ i, Module.Free R (C.X i)) :
    Epi (uctBeta R M n C hfree) := by

  set P := ProjectiveResolution.of M
  set hS := resSES_shortExact R C M P hfree
  set hij := ComplexShape.down_mk (n + 1) n (by omega)

  show Epi (hS.δ (n + 1) n hij ≫ torIdentification R C M P hfree n)

  have hexact := hS.homology_exact₁ (n + 1) n hij

  haveI h_epi_lift : Epi (Limits.kernel.lift
      (HomologicalComplex.homologyMap (resSES R C M P).f n)
      (hS.δ (n + 1) n hij)
      (hS.δ_comp (n + 1) n hij)) :=
    hexact.epi_kernelLift

  haveI h_iso := torIdentification_iso_on_kernel R C M P hfree n

  have h_factor : hS.δ (n + 1) n hij =
      Limits.kernel.lift (HomologicalComplex.homologyMap (resSES R C M P).f n)
        (hS.δ (n + 1) n hij) (hS.δ_comp (n + 1) n hij) ≫
      Limits.kernel.ι (HomologicalComplex.homologyMap (resSES R C M P).f n) :=
    (Limits.kernel.lift_ι _ _ _).symm

  rw [show hS.δ (n + 1) n hij ≫ torIdentification R C M P hfree n =
    Limits.kernel.lift (HomologicalComplex.homologyMap (resSES R C M P).f n)
      (hS.δ (n + 1) n hij) (hS.δ_comp (n + 1) n hij) ≫
    (Limits.kernel.ι (HomologicalComplex.homologyMap (resSES R C M P).f n) ≫
      torIdentification R C M P hfree n) from by
    rw [← Category.assoc, ← h_factor]]

  exact epi_comp _ _

/-- Exactness of the UCT short complex at its middle term: the image of $\alpha_n$ equals
the kernel of $\beta_n$, giving the exact middle of the universal coefficient sequence. -/
theorem uctExact (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (M : ModuleCat R) (n : ℕ)
    (C : ChainComplex (ModuleCat R) ℕ) (hfree : ∀ i, Module.Free R (C.X i)) :
    (ShortComplex.mk (uctAlpha R M n C hfree) (uctBeta R M n C hfree)
      (uctAlpha_comp_uctBeta R M n C hfree)).Exact := by sorry

/-- The UCT short exact sequence splits: a (non-natural) splitting of the sequence
$0 \to H_n(C) \otimes M \to H_n(C \otimes M) \to \mathrm{Tor}_1(H_{n-1}(C), M) \to 0$,
obtained from the retraction `uctAlpha_retraction` together with exactness. -/
theorem uctSplitting (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (M : ModuleCat R) (n : ℕ)
    (C : ChainComplex (ModuleCat R) ℕ) (hfree : ∀ i, Module.Free R (C.X i)) :
    Nonempty (ShortComplex.mk (uctAlpha R M n C hfree) (uctBeta R M n C hfree)
      (uctAlpha_comp_uctBeta R M n C hfree)).Splitting := by

  haveI := uctBeta_epi R M n C hfree

  exact ⟨ShortComplex.Splitting.ofExactOfRetraction _ (uctExact R M n C hfree)
    (uctAlpha_retraction R M n C hfree).retraction
    (uctAlpha_retraction R M n C hfree).id inferInstance⟩

/-- The UCT sequence is short exact: combining injectivity of $\alpha_n$, exactness in
the middle, and surjectivity of $\beta_n$ into a single `ShortExact` package. -/
theorem uctShortExact (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (M : ModuleCat R) (n : ℕ)
    (C : ChainComplex (ModuleCat R) ℕ) (hfree : ∀ i, Module.Free R (C.X i)) :
    (ShortComplex.mk (uctAlpha R M n C hfree) (uctBeta R M n C hfree)
      (uctAlpha_comp_uctBeta R M n C hfree)).ShortExact :=
  (uctSplitting R M n C hfree).some.shortExact

/-- Naturality of the UCT connecting map $\beta_n$ in the chain complex variable: a chain
map $\varphi : C \to D$ between free complexes induces a commuting square between the
UCT $\beta$'s for $C$ and $D$. -/
theorem uctBeta_natural (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (M : ModuleCat R) (n : ℕ)
    (C D : ChainComplex (ModuleCat R) ℕ)
    (hfreeC : ∀ i, Module.Free R (C.X i))
    (hfreeD : ∀ i, Module.Free R (D.X i))
    (φ : C ⟶ D) :
    uctBeta R M n C hfreeC ≫
      ((Tor (ModuleCat R) 1).map (HomologicalComplex.homologyMap φ n)).app M =
    HomologicalComplex.homologyMap (tensorComplexMap R φ M) (n + 1) ≫
      uctBeta R M n D hfreeD := by
  simp only [uctBeta, Category.assoc]
  have htor := torIdentification_natural R M n C D (ProjectiveResolution.of M) hfreeC hfreeD φ
  have hδ := _root_.HomologicalComplex.HomologySequence.δ_naturality
    (ShortComplex.Hom.mk
      (tensorComplexMap R φ ((ProjectiveResolution.of M).complex.X 1))
      (tensorComplexMap R φ ((ProjectiveResolution.of M).complex.X 0))
      (tensorComplexMap R φ M)
      ((NatTrans.mapHomologicalComplex
        ((tensoringRight (ModuleCat R)).map ((ProjectiveResolution.of M).complex.d 1 0))
        (ComplexShape.down ℕ)).naturality φ)
      ((NatTrans.mapHomologicalComplex
        ((tensoringRight (ModuleCat R)).map ((ProjectiveResolution.of M).π.f 0))
        (ComplexShape.down ℕ)).naturality φ) :
      resSES R C M (ProjectiveResolution.of M) ⟶ resSES R D M (ProjectiveResolution.of M))
    (resSES_shortExact R C M (ProjectiveResolution.of M) hfreeC)
    (resSES_shortExact R D M (ProjectiveResolution.of M) hfreeD)
    (n + 1) n (ComplexShape.down_mk (n + 1) n (by omega))
  dsimp only [ShortComplex.Hom.mk] at hδ
  erw [htor, ← Category.assoc, hδ, Category.assoc]

/-- **Theorem 24.1 (Universal Coefficient Theorem)**. For a PID $R$, a chain complex of
free $R$-modules $C$, and an $R$-module $M$, there is a natural split short exact
sequence
$$0 \to H_n(C) \otimes_R M \to H_n(C \otimes_R M) \to \mathrm{Tor}_1^R(H_{n-1}(C), M) \to 0.$$
This bundles the maps $\alpha_n, \beta_n$, exactness, splitting, and naturality. -/
def universal_coefficient_theorem (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (M : ModuleCat R) (n : ℕ) : NaturalUCTData R M n where
  α := uctAlpha R M n
  β := uctBeta R M n
  zero := uctAlpha_comp_uctBeta R M n
  shortExact := uctShortExact R M n
  splitting := uctSplitting R M n
  α_natural := uctAlpha_natural R M n
  β_natural := uctBeta_natural R M n

end UniversalCoefficientTheorem
