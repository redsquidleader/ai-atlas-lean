/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section10
import Atlas.AlgebraicTopologyI.code.Section26
import Atlas.AlgebraicTopologyI.code.Section27
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Algebra.Algebra.TransferInstance
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.LinearAlgebra.DirectSum.Basis

open DirectSum GradedMonoid

namespace CupProduct

/-- **Definition 29.1.** A *graded $R$-algebra* (for $R$ a commutative ring) is
a $\mathbb{Z}$-graded $R$-module $A_*$ equipped with multiplication maps
$A_p \otimes_R A_q \to A_{p+q}$ and a unit $\eta : R \to A_0$ satisfying the
usual associativity and unit diagrams.

This bundles a family of $R$-modules with the graded-semiring/graded-algebra
data taken from Mathlib's `DirectSum` / `GAlgebra` API. -/
structure GradedRAlgebra (R : Type*) [CommRing R] where
  A : ℤ → Type*
  instAddCommGroup : ∀ i, AddCommGroup (A i)
  instModule : ∀ i, Module R (A i)
  instGSemiring : GSemiring A
  instGAlgebra : GAlgebra R A

attribute [instance] GradedRAlgebra.instAddCommGroup GradedRAlgebra.instModule
  GradedRAlgebra.instGSemiring GradedRAlgebra.instGAlgebra

namespace GradedRAlgebra

variable {R : Type*} [CommRing R] (GA : GradedRAlgebra R)

/-- Multiplication in a graded $R$-algebra: $A_p \otimes A_q \to A_{p + q}$. -/
def mul {p q : ℤ} (x : GA.A p) (y : GA.A q) : GA.A (p + q) :=
  GMul.mul x y

/-- The unit map $\eta : R \to A_0$ of a graded $R$-algebra. -/
def unit : R →+ GA.A 0 :=
  GAlgebra.toFun

/-- A graded $R$-algebra $A$ is *(graded) commutative* if the twist isomorphism
satisfies $\tau(x \otimes y) = (-1)^{pq} y \otimes x$, i.e.
$$x \cdot y = (-1)^{pq} y \cdot x$$
for $x \in A_p$ and $y \in A_q$. This is the Koszul sign rule, as used for
example in singular cohomology under cup product. -/
structure IsGradedCommutative : Prop where
  mul_comm : ∀ (p q : ℤ) (x : GA.A p) (y : GA.A q),
    GMul.mul x y =
      ((p * q).negOnePow : ℤ) • cast (congrArg GA.A (add_comm q p)) (GMul.mul y x)

end GradedRAlgebra

end CupProduct

open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI

noncomputable section

namespace SingularCohomology

variable (R : Type) [CommRing R]

/-- The total cohomology ring $H^*(X; R) = \bigoplus_{n \ge 0} H^n(X; R)$ of a
space $X$ with coefficients in $R$, as a wrapper around the direct sum of
singular cohomology groups. It will be given the structure of a graded
$R$-algebra via the cup product. -/
structure CupProductAlgebra (X : TopCat.{0}) : Type where
  toDirectSum : DirectSum ℕ (fun n ↦
    (singularCohomology R X (ModuleCat.of R R) n : Type))

/-- The graded family $n \mapsto H^n(X; R)$ of singular cohomology groups,
viewed as plain types indexed by $\mathbb{N}$. -/
abbrev singularCohomologyFamily (X : TopCat.{0}) : ℕ → Type :=
  fun n => (singularCohomology R X (ModuleCat.of R R) n : Type)

/-- The additive group structure on each cohomology group $H^n(X; R)$,
inherited from its `ModuleCat` representation. -/
instance (X : TopCat.{0}) (n : ℕ) : AddCommGroup (singularCohomologyFamily R X n) :=
  ModuleCat.isAddCommGroup _


/-- The cup product on singular cohomology, as a graded multiplication
$\smile : H^p(X) \otimes H^q(X) \to H^{p + q}(X)$. -/
def cupMul (X : TopCat.{0}) {p q : ℕ}
    (x : singularCohomologyFamily R X p) (y : singularCohomologyFamily R X q) :
    singularCohomologyFamily R X (p + q) :=
  (cupProduct R X p q).hom (x ⊗ₜ[R] y)


/-- The cup product as a graded-monoid multiplication on $H^*(X; R)$. -/
instance instGMulCohomologyFamily (X : TopCat.{0}) :
    GradedMonoid.GMul (singularCohomologyFamily R X) where
  mul := cupMul R X


/-- The *augmentation cocycle* $\varepsilon \in C^0(X; R)$: the singular
$0$-cochain assigning $1 \in R$ to every singular $0$-simplex. Its cohomology
class is the unit of $H^*(X; R)$. -/
noncomputable def augmentationCocycle
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    (singularCochainComplex R X (ModuleCat.of R R)).X 0 :=
  Sigma.desc (fun _ => 𝟙 (ModuleCat.of R R))

set_option maxHeartbeats 6400000 in
set_option backward.isDefEq.respectTransparency false in
/-- The augmentation cocycle $\varepsilon$ is indeed a $0$-cocycle: its
coboundary vanishes, since for each $1$-simplex $\sigma$ both endpoints map to
$1 \in R$ and cancel. Used to lift $\varepsilon$ to a cohomology class. -/
lemma augmentationCocycle_coboundary_zero
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj X).d 1 0 ≫
      augmentationCocycle R X = 0 := by
  apply Sigma.hom_ext
  intro σ
  simp only [Limits.HasZeroMorphisms.comp_zero, ← Category.assoc, augmentationCocycle]
  simp only [singularChainComplexFunctor, SSet.singularChainComplexFunctor]
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.whiskeringLeft, Functor.postcompose₂]
  erw [AlternatingFaceMapComplex.obj_d_eq]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, Preadditive.sum_comp,
    Preadditive.zsmul_comp]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    SimplicialObject.δ]
  erw [Sigma.ι_comp_map' _ _ σ, Sigma.ι_comp_map' _ _ σ]
  simp only [Category.id_comp, Sigma.ι_desc]
  simp [add_neg_cancel]

set_option maxHeartbeats 6400000 in
/-- The unit $1 \in H^0(X; R)$ of the cohomology ring, obtained as the
cohomology class of the augmentation cocycle $\varepsilon$. -/
noncomputable def cohomologyUnit
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    singularCohomologyFamily R X 0 :=
  let K := singularCochainComplex R X (ModuleCat.of R R)
  let cycleElt : ↑((forget₂ (ModuleCat.{0} R) Ab).obj (K.cycles 0)) :=
    HomologicalComplex.cyclesMk K (augmentationCocycle R X) 1
      (CochainComplex.next ℕ 0)
      (by
        change (K.d 0 1).hom (augmentationCocycle R X) = 0
        simp only [K, singularCochainComplex, ChainComplex.linearYonedaObj_d]
        exact augmentationCocycle_coboundary_zero R X)
  (ConcreteCategory.hom ((forget₂ (ModuleCat.{0} R) Ab).map
    (CochainComplex.isoHomologyπ₀ K).hom)) cycleElt

/-- The cohomology unit `cohomologyUnit` as the graded-monoid identity of
$H^*(X; R)$. -/
instance instGOneCohomologyFamily (X : TopCat.{0}) :
    GradedMonoid.GOne (singularCohomologyFamily R X) where
  one := cohomologyUnit R X


/-- Left unit law for the cup product: $1 \smile y = y$ for every $y \in H^q(X; R)$,
where $1 \in H^0(X; R)$ is the class of the augmentation cocycle. -/
theorem cupProduct_unit_left
    (R : Type) [CommRing R] (X : TopCat.{0}) (q : ℕ)
    (y : singularCohomologyFamily R X q) :
    cast (congrArg (singularCohomologyFamily R X) (Nat.zero_add q))
      ((cupProduct R X 0 q).hom (cohomologyUnit R X ⊗ₜ[R] y)) = y := by sorry

/-- Graded-monoid form of `cupProduct_unit_left`: $1 \cdot a = a$ in $H^*(X; R)$. -/
theorem cupProduct_one_mul
    (R : Type) [CommRing R] (X : TopCat.{0})
    (a : GradedMonoid (singularCohomologyFamily R X)) :
    (1 : GradedMonoid (singularCohomologyFamily R X)) * a = a := by
  obtain ⟨q, y⟩ := a
  exact Sigma.ext (Nat.zero_add q)
    (heq_of_cast_eq _ (cupProduct_unit_left R X q y))


/-- Graded commutativity (Koszul sign rule) for the cup product:
$x \smile y = (-1)^{pq}\, y \smile x$ for $x \in H^p(X; R)$, $y \in H^q(X; R)$. -/
theorem cupProduct_graded_comm
    (R : Type) [CommRing R] (X : TopCat.{0})
    (p q : ℕ) (x : singularCohomologyFamily R X p) (y : singularCohomologyFamily R X q) :
    GradedMonoid.GMul.mul x y =
      (((p : ℤ) * (q : ℤ)).negOnePow : ℤ) •
        cast (congrArg (singularCohomologyFamily R X) (Nat.add_comm q p))
          (GradedMonoid.GMul.mul y x) := by sorry

/-- Right unit law for the cup product: $a \cdot 1 = a$. Deduced from
`cupProduct_one_mul` by graded commutativity (the sign is trivially $+1$ in degree $0$). -/
theorem cupProduct_mul_one
    (R : Type) [CommRing R] (X : TopCat.{0})
    (a : GradedMonoid (singularCohomologyFamily R X)) :
    a * (1 : GradedMonoid (singularCohomologyFamily R X)) = a := by
  obtain ⟨p, x⟩ := a
  have h_comm := cupProduct_graded_comm R X p 0 x GOne.one
  have sign_simp : (((p : ℤ) * (↑(0 : ℕ) : ℤ)).negOnePow : ℤ) = 1 := by
    simp [mul_zero, Int.negOnePow_zero]
  have h1 : (GradedMonoid.mk p x : GradedMonoid (singularCohomologyFamily R X)) * 1 =
      1 * (GradedMonoid.mk p x) := by
    show GradedMonoid.mk (p + 0) (GMul.mul x GOne.one) =
      GradedMonoid.mk (0 + p) (GMul.mul GOne.one x)
    congr 1
    · omega
    · rw [h_comm, sign_simp, one_smul]
      exact cast_heq _ _
  exact h1.trans (cupProduct_one_mul R X ⟨p, x⟩)


/-- Associativity of the cup product on cochain-level homs:
$(x \smile y) \smile z = x \smile (y \smile z)$ in $H^{p + q + r}(X; R)$. -/
theorem cupProduct_hom_assoc
    (R : Type) [CommRing R] (X : TopCat.{0})
    (p q r : ℕ) (x : singularCohomologyFamily R X p)
    (y : singularCohomologyFamily R X q) (z : singularCohomologyFamily R X r) :
    cast (congrArg (singularCohomologyFamily R X) (Nat.add_assoc p q r))
      ((cupProduct R X (p + q) r).hom ((cupProduct R X p q).hom (x ⊗ₜ[R] y) ⊗ₜ[R] z)) =
    (cupProduct R X p (q + r)).hom (x ⊗ₜ[R] (cupProduct R X q r).hom (y ⊗ₜ[R] z)) := by sorry

/-- Graded-monoid form of associativity: $(a \cdot b) \cdot c = a \cdot (b \cdot c)$
in the total cohomology $H^*(X; R)$. -/
theorem cupProduct_mul_assoc
    (R : Type) [CommRing R] (X : TopCat.{0})
    (a b c : GradedMonoid (singularCohomologyFamily R X)) :
    a * b * c = a * (b * c) := by
  obtain ⟨p, x⟩ := a
  obtain ⟨q, y⟩ := b
  obtain ⟨r, z⟩ := c
  exact Sigma.ext (Nat.add_assoc p q r) (heq_of_cast_eq _ (cupProduct_hom_assoc R X p q r x y z))


/-- Right annihilator: cup product with $0$ on the right vanishes,
since the underlying linear map is $R$-bilinear. -/
theorem cupProduct_mul_zero
    (R : Type) [CommRing R] (X : TopCat.{0})
    {i j : ℕ} (a : singularCohomologyFamily R X i) :
    GradedMonoid.GMul.mul a (0 : singularCohomologyFamily R X j) = 0 := by
  show cupMul R X a 0 = 0
  simp only [cupMul, TensorProduct.tmul_zero, map_zero]

/-- Left annihilator: cup product with $0$ on the left vanishes. -/
theorem cupProduct_zero_mul
    (R : Type) [CommRing R] (X : TopCat.{0})
    {i j : ℕ} (b : singularCohomologyFamily R X j) :
    GradedMonoid.GMul.mul (0 : singularCohomologyFamily R X i) b = 0 := by
  show cupMul R X 0 b = 0
  simp only [cupMul, TensorProduct.zero_tmul, map_zero]

/-- Right distributivity of the cup product: $a \smile (b + c) = a \smile b + a \smile c$. -/
theorem cupProduct_mul_add
    (R : Type) [CommRing R] (X : TopCat.{0})
    {i j : ℕ} (a : singularCohomologyFamily R X i) (b c : singularCohomologyFamily R X j) :
    GradedMonoid.GMul.mul a (b + c) =
      GradedMonoid.GMul.mul a b + GradedMonoid.GMul.mul a c := by
  show cupMul R X a (b + c) = cupMul R X a b + cupMul R X a c
  simp only [cupMul, TensorProduct.tmul_add, map_add]

/-- Left distributivity of the cup product: $(a + b) \smile c = a \smile c + b \smile c$. -/
theorem cupProduct_add_mul
    (R : Type) [CommRing R] (X : TopCat.{0})
    {i j : ℕ} (a b : singularCohomologyFamily R X i) (c : singularCohomologyFamily R X j) :
    GradedMonoid.GMul.mul (a + b) c =
      GradedMonoid.GMul.mul a c + GradedMonoid.GMul.mul b c := by
  show cupMul R X (a + b) c = cupMul R X a c + cupMul R X b c
  simp only [cupMul, TensorProduct.add_tmul, map_add]


/-- The natural-number cast $\mathbb{N} \to H^0(X; R)$, defined recursively as
$n \mapsto n \cdot 1_{H^*(X; R)}$. Provides the `natCast` field for the graded
ring structure on $H^*(X; R)$. -/
def cupProduct_natCast
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    ℕ → singularCohomologyFamily R X 0
  | 0 => 0
  | n + 1 => cupProduct_natCast R X n + GradedMonoid.GOne.one

/-- Base case for the natural-number cast: $0 \in \mathbb{N}$ maps to $0 \in H^0(X; R)$. -/
theorem cupProduct_natCast_zero
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    cupProduct_natCast R X 0 = 0 := rfl

/-- Successor case for the natural-number cast: the cast of $n + 1$ is the cast of
$n$ plus the cohomology unit. -/
theorem cupProduct_natCast_succ
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    cupProduct_natCast R X (n + 1) = cupProduct_natCast R X n + GradedMonoid.GOne.one := rfl


/-- The integer cast $\mathbb{Z} \to H^0(X; R)$, extending the natural-number cast
by negation on negative integers. Provides the `intCast` field for the graded
ring structure. -/
def cupProduct_intCast
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    ℤ → singularCohomologyFamily R X 0
  | Int.ofNat n => cupProduct_natCast R X n
  | Int.negSucc n => -cupProduct_natCast R X (n + 1)

/-- Compatibility of the integer cast with the natural-number cast on non-negative
integers $n \ge 0$. -/
theorem cupProduct_intCast_ofNat
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    cupProduct_intCast R X ↑n = cupProduct_natCast R X n := rfl

/-- Behaviour of the integer cast on a negative integer $-(n + 1)$: it returns
$-(n + 1) \cdot 1$ in $H^0(X; R)$. -/
theorem cupProduct_intCast_negSucc
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    cupProduct_intCast R X (Int.negSucc n) = -cupProduct_natCast R X (n + 1) := rfl

/-- Graded ring structure on the cohomology family $n \mapsto H^n(X; R)$,
assembling unit, associativity, distributivity and the natural/integer casts
proved above. This is what promotes $H^*(X; R) = \bigoplus_n H^n(X; R)$ to a ring
under cup product. -/
instance instGRingCohomologyFamily
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    DirectSum.GRing (singularCohomologyFamily R X) where
  mul_zero := cupProduct_mul_zero R X
  zero_mul := cupProduct_zero_mul R X
  mul_add := cupProduct_mul_add R X
  add_mul := cupProduct_add_mul R X
  one_mul := cupProduct_one_mul R X
  mul_one := cupProduct_mul_one R X
  mul_assoc := cupProduct_mul_assoc R X
  natCast := cupProduct_natCast R X
  natCast_zero := cupProduct_natCast_zero R X
  natCast_succ := cupProduct_natCast_succ R X
  intCast := cupProduct_intCast R X
  intCast_ofNat := cupProduct_intCast_ofNat R X
  intCast_negSucc_ofNat := cupProduct_intCast_negSucc R X


/-- The unit map $R \to H^0(X; R)$ of the cohomology algebra,
sending $r \in R$ to $r \cdot 1_{H^*(X; R)}$. -/
def cohomologyAlgebraMap
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    R →+ singularCohomologyFamily R X 0 where
  toFun r := r • cohomologyUnit R X
  map_zero' := by simp [zero_smul]
  map_add' r s := by simp [add_smul]

/-- The cohomology algebra map sends $1 \in R$ to the cohomology unit
$1 \in H^0(X; R)$. -/
theorem cohomologyAlgebraMap_one
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    cohomologyAlgebraMap R X 1 = GradedMonoid.GOne.one := by
  show (1 : R) • cohomologyUnit R X = cohomologyUnit R X
  simp [one_smul]

/-- Multiplicativity of the cohomology algebra map: $\eta(rs) = \eta(r) \smile \eta(s)$,
using the idempotence $1 \smile 1 = 1$ of the cohomology unit and bilinearity. -/
theorem cohomologyAlgebraMap_mul
    (R : Type) [CommRing R] (X : TopCat.{0}) (r s : R) :
    GradedMonoid.mk _ (cohomologyAlgebraMap R X (r * s)) =
      GradedMonoid.mk _ (GradedMonoid.GMul.mul (cohomologyAlgebraMap R X r)
        (cohomologyAlgebraMap R X s)) := by
  congr 1
  show (r * s) • cohomologyUnit R X = cupMul R X (r • cohomologyUnit R X) (s • cohomologyUnit R X)
  simp only [cupMul]
  have unit_idem : (ModuleCat.Hom.hom (cupProduct R X 0 0))
      (cohomologyUnit R X ⊗ₜ[R] cohomologyUnit R X) = cohomologyUnit R X := by
    have hmul := cupProduct_one_mul R X ⟨0, cohomologyUnit R X⟩
    exact Sigma.mk.inj_iff.mp hmul |>.2 |>.eq
  conv_rhs =>
    rw [← TensorProduct.smul_tmul' (R' := R) r (cohomologyUnit R X) (s • cohomologyUnit R X),
      TensorProduct.tmul_smul, smul_smul]
  rw [map_smul, unit_idem]

/-- Central commutativity: scalars from $R$ commute with every cohomology class.
Required to view $H^*(X; R)$ as an $R$-algebra. -/
theorem cohomologyAlgebraMap_commutes
    (R : Type) [CommRing R] (X : TopCat.{0})
    (r : R) (x : GradedMonoid (singularCohomologyFamily R X)) :
    GradedMonoid.mk _ (cohomologyAlgebraMap R X r) * x =
      x * GradedMonoid.mk _ (cohomologyAlgebraMap R X r) := by sorry

/-- Casting along an equality of degrees commutes with scalar multiplication:
$\mathrm{cast}_h(r \cdot z) = r \cdot \mathrm{cast}_h(z)$ in the cohomology family. -/
lemma cast_smul_family
    {R : Type} [CommRing R] {X : TopCat.{0}} {n m : ℕ} (h : n = m)
    (r : R) (z : singularCohomologyFamily R X n) :
    cast (congrArg (singularCohomologyFamily R X) h) (r • z) =
    r • cast (congrArg (singularCohomologyFamily R X) h) z := by
  subst h; rfl

/-- Compatibility of $R$-scalar multiplication with the algebra map:
$r \cdot x = \eta(r) \smile x$. Together with the previous lemmas this gives the
$R$-algebra structure on $H^*(X; R)$. -/
theorem cohomologyAlgebraMap_smul_def
    (R : Type) [CommRing R] (X : TopCat.{0})
    (r : R) (x : GradedMonoid (singularCohomologyFamily R X)) :
    r • x = GradedMonoid.mk _ (cohomologyAlgebraMap R X r) * x := by
  obtain ⟨q, y⟩ := x


  symm
  apply Sigma.ext (Nat.zero_add q)
  apply heq_of_cast_eq

  show cast (congrArg (singularCohomologyFamily R X) (Nat.zero_add q))
    ((cupProduct R X 0 q).hom ((r • cohomologyUnit R X) ⊗ₜ[R] y)) = r • y
  rw [← TensorProduct.smul_tmul', map_smul,
      cast_smul_family (Nat.zero_add q) r, cupProduct_unit_left]

/-- Graded $R$-algebra structure on $H^*(X; R)$, bundling the cohomology unit
map, its multiplicativity, central commutativity, and compatibility with scalar
multiplication. -/
instance instGAlgebraCohomologyFamily
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    DirectSum.GAlgebra R (singularCohomologyFamily R X) where
  toFun := cohomologyAlgebraMap R X
  map_one := cohomologyAlgebraMap_one R X
  map_mul := cohomologyAlgebraMap_mul R X
  commutes := cohomologyAlgebraMap_commutes R X
  smul_def := cohomologyAlgebraMap_smul_def R X

/-- The wrapper structure `CupProductAlgebra R X` is canonically equivalent to the
underlying direct sum $\bigoplus_n H^n(X; R)$, used to transfer ring/algebra
instances onto it. -/
def CupProductAlgebra.equiv (X : TopCat.{0}) :
    CupProductAlgebra R X ≃
      DirectSum ℕ (singularCohomologyFamily R X) where
  toFun a := a.toDirectSum
  invFun d := ⟨d⟩
  left_inv _ := rfl
  right_inv _ := rfl


/-- The ring structure on $H^*(X; R) = \bigoplus_n H^n(X; R)$, transferred from
the direct sum along `CupProductAlgebra.equiv`. -/
@[reducible]
noncomputable def instRingCupProductAlgebra
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    Ring (CupProductAlgebra R X) :=
  (CupProductAlgebra.equiv R X).ring

attribute [instance] instRingCupProductAlgebra


/-- The $R$-algebra structure on the cohomology ring $H^*(X; R)$, also transferred
from the direct sum along `CupProductAlgebra.equiv`. -/
@[reducible]
noncomputable def instAlgebraCupProductAlgebra
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    @Algebra R (CupProductAlgebra R X) _
      (instRingCupProductAlgebra R X).toSemiring :=
  (CupProductAlgebra.equiv R X).algebra R

attribute [instance] instAlgebraCupProductAlgebra

/-- The *Koszul tensor algebra* $H^*(X; R) \otimes_R H^*(X; R)$, wrapping the
$R$-tensor product of two cohomology rings. The cohomology cross product will be
defined as a ring homomorphism out of this algebra. -/
structure KoszulTensorAlgebra (X Y : TopCat.{0}) : Type where
  toTensorProduct : TensorProduct R (CupProductAlgebra R X) (CupProductAlgebra R Y)


/-- Ring structure on the Koszul tensor algebra, induced by the graded-commutative
ring structures on $H^*(X; R)$ and $H^*(Y; R)$ together with the Koszul sign rule. -/
noncomputable instance instRingKoszulTensorAlgebra
    (R : Type) [CommRing R] (X Y : TopCat.{0}) :
    Ring (KoszulTensorAlgebra R X Y) := by sorry

attribute [instance] instRingKoszulTensorAlgebra


/-- $R$-algebra structure on the Koszul tensor algebra. -/
noncomputable instance instAlgebraKoszulTensorAlgebra
    (R : Type) [CommRing R] (X Y : TopCat.{0}) :
    @Algebra R (KoszulTensorAlgebra R X Y) _
      (instRingKoszulTensorAlgebra R X Y).toSemiring := by sorry

attribute [instance] instAlgebraKoszulTensorAlgebra


/-- The cohomology *cross product* assembled as a ring homomorphism
$H^*(X; R) \otimes_R H^*(Y; R) \to H^*(X \times Y; R)$. The cross product of
$a \in H^p(X)$ and $b \in H^q(Y)$ is $\mathrm{pr}_X^* a \smile \mathrm{pr}_Y^* b$. -/
noncomputable def crossProduct_ringHom_core
    (R : Type) [CommRing R] (X Y : TopCat.{0}) :
    @RingHom (KoszulTensorAlgebra R X Y) (CupProductAlgebra R (TopCat.of (↑X × ↑Y)))
      (instRingKoszulTensorAlgebra R X Y).toNonAssocSemiring
      (instRingCupProductAlgebra R (TopCat.of (↑X × ↑Y))).toNonAssocSemiring := by sorry


/-- The cross-product ring homomorphism is compatible with the $R$-algebra unit:
$\eta_{X \times Y}(r) = \mathrm{cross}(\eta_X(r) \otimes 1) = \mathrm{cross}(1 \otimes \eta_Y(r))$.
This is needed to upgrade `crossProduct_ringHom_core` to an algebra map. -/
theorem crossProduct_commutes_algebraMap_core
    (R : Type) [CommRing R] (X Y : TopCat.{0}) (r : R) :
    (crossProduct_ringHom_core R X Y)
      (@algebraMap R (KoszulTensorAlgebra R X Y) _
        (instRingKoszulTensorAlgebra R X Y).toSemiring
        (instAlgebraKoszulTensorAlgebra R X Y) r) =
      @algebraMap R (CupProductAlgebra R (TopCat.of (↑X × ↑Y))) _
        (instRingCupProductAlgebra R (TopCat.of (↑X × ↑Y))).toSemiring
        (instAlgebraCupProductAlgebra R (TopCat.of (↑X × ↑Y))) r := by sorry

/-- The cohomology cross product packaged as an $R$-algebra homomorphism
$H^*(X; R) \otimes_R H^*(Y; R) \to H^*(X \times Y; R)$. -/
def crossProduct_algHom
    (R : Type) [CommRing R] (X Y : TopCat.{0}) :
    KoszulTensorAlgebra R X Y →ₐ[R]
      CupProductAlgebra R (TopCat.of (↑X × ↑Y)) :=
  @AlgHom.mk R (KoszulTensorAlgebra R X Y) (CupProductAlgebra R (TopCat.of (↑X × ↑Y)))
    _ (instRingKoszulTensorAlgebra R X Y).toSemiring
    (instRingCupProductAlgebra R (TopCat.of (↑X × ↑Y))).toSemiring
    (instAlgebraKoszulTensorAlgebra R X Y)
    (instAlgebraCupProductAlgebra R (TopCat.of (↑X × ↑Y)))
    (crossProduct_ringHom_core R X Y)
    (crossProduct_commutes_algebraMap_core R X Y)


/-- **Proposition 29.2** (cohomology cross product, linear form). The cohomology
cross product, viewed merely as an $R$-linear map
$$H^*(X; R) \otimes_R H^*(Y; R) \longrightarrow H^*(X \times Y; R).$$
Obtained from the algebra map `crossProduct_algHom` by forgetting the
multiplicative structure. -/
def cohomologyCrossProductLinear
    (R : Type) [CommRing R] (X Y : TopCat.{0}) :
    KoszulTensorAlgebra R X Y →ₗ[R]
      CupProductAlgebra R (TopCat.of (↑X × ↑Y)) :=
  (crossProduct_algHom R X Y).toLinearMap


/-- **Proposition 29.2** (multiplicativity of the cross product). The cohomology
cross product is multiplicative:
$$(a \times b) \cdot (a' \times b') = (-1)^{|b||a'|}\,(a \smile a') \times (b \smile b').$$
In compact form: the linear map `cohomologyCrossProductLinear` preserves products. -/
theorem crossProduct_map_mul
    (R : Type) [CommRing R] (X Y : TopCat.{0})
    (a b : KoszulTensorAlgebra R X Y) :
    cohomologyCrossProductLinear R X Y (a * b) =
      cohomologyCrossProductLinear R X Y a *
        cohomologyCrossProductLinear R X Y b :=
  map_mul (crossProduct_algHom R X Y) a b


end SingularCohomology

namespace CupProduct

section SphereCupProduct

open CategoryTheory AlgebraicTopology Limits

variable (R : Type) [CommRing R]

/-- The singular cochain complex $C^*(X; G) = \mathrm{Hom}_R(C_*(X; R), G)$ of a
topological space $X$ with coefficients in an $R$-module $G$, as an object of
`CochainComplex (ModuleCat R) ℕ`. -/
noncomputable abbrev singCochains (G : ModuleCat.{0} R) (X : TopCat.{0}) :
    CochainComplex (ModuleCat R) ℕ :=
  (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
    (ModuleCat.of R R)).obj X).linearYonedaObj R G

/-- The $n$-th singular cohomology $H^n(X; G)$ as an $R$-module, defined as the
homology of the cochain complex `singCochains R G X` in degree $n$. -/
noncomputable abbrev singCohom (G : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    ModuleCat R :=
  (singCochains R G X).homology n

/-- Contravariant action of a continuous map $f : X \to Y$ on singular cochains:
the pullback $f^* : C^*(Y; G) \to C^*(X; G)$ defined by precomposition with the
induced chain map on $C_*(-; R)$. -/
noncomputable def pullbackCochainMap (G : ModuleCat.{0} R) {X Y : TopCat.{0}} (f : X ⟶ Y) :
    singCochains R G Y ⟶ singCochains R G X :=
  let chainMap := ((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
    (ModuleCat.of R R)).map f
  let mapHC := (((linearYoneda R (ModuleCat.{0} R)).obj G).rightOp.mapHomologicalComplex
    (ComplexShape.down ℕ)).map chainMap
  (HomologicalComplex.unopFunctor (ModuleCat R) (ComplexShape.down ℕ)).map mapHC.op

/-- The induced map $f^* : H^n(Y; G) \to H^n(X; G)$ on singular cohomology,
obtained from `pullbackCochainMap` by passing to homology in degree $n$. -/
noncomputable def cohomPullback (G : ModuleCat.{0} R) {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    singCohom R G Y n ⟶ singCohom R G X n :=
  HomologicalComplex.homologyMap (pullbackCochainMap R G f) n

/-- The singular chain complex $C_*(S^m; \mathbb{Z})$ of the $m$-sphere with
integer coefficients, packaged as an object of `ChainComplex (ModuleCat ℤ) ℕ`. -/
noncomputable abbrev sphereChainZ (m : ℕ) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  ((singularChainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.sphere.{0} m)

/-- Identification of the Mathlib sphere `TopCat.sphere m` with the
`SphereHomology.Sphere m` used elsewhere in Atlas, via the canonical `ULift`
homeomorphism. -/
noncomputable def sphereTopCatIso (m : ℕ) :
    TopCat.sphere.{0} m ≅ TopCat.of (SphereHomology.Sphere m) :=
  TopCat.isoOfHomeo Homeomorph.ulift

/-- Each chain group $C_i(S^m; \mathbb{Z})$ is a free $\mathbb{Z}$-module, being
the direct sum of copies of $\mathbb{Z}$ indexed by singular simplices. -/
theorem sphereChainZ_free (m : ℕ) (i : ℕ) :
    Module.Free ℤ ((sphereChainZ m).X i) := by
  show Module.Free ℤ
    ↑(∐ fun (_ : (TopCat.toSSet.obj (TopCat.sphere m)).obj
      (Opposite.op (SimplexCategory.mk i))) => ModuleCat.of ℤ ℤ)
  classical
  exact Module.Free.of_equiv'
    (Module.Free.directSum ℤ (fun _ => ↑(ModuleCat.of ℤ ℤ)))
    (ModuleCat.coprodIsoDirectSum _).toLinearEquiv.symm


/-- Compatibility of the singular chain complex functor with the forgetful functor
$\mathrm{Mod}_{\mathbb{Z}} \to \mathrm{Ab}$: forgetting the $\mathbb{Z}$-module
structure on $C_*(X; \mathbb{Z})$ recovers the singular chain complex of $X$ valued
in abelian groups. -/
noncomputable def singularChainComplexFunctor_forget₂_iso (X : TopCat.{0}) :
  ((forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (((singularChainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).obj X) ≅
  ((singularChainComplexFunctor.{0} AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).obj X := by sorry


/-- Vanishing of singular homology with $\mathbb{Z}$-module coefficients is
equivalent to vanishing of the abelian-group-valued singular homology, allowing us
to transfer known vanishing results from `SphereHomology` into the `ModuleCat`
setting. -/
theorem moduleCat_singularHomology_isZero_iff (X : TopCat.{0}) (n : ℕ) :
    IsZero ((((singularChainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj X).homology n) ↔
    IsZero ((((singularChainComplexFunctor.{0} AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ)).obj X).homology n) := by
  set F := forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat
  set K_mod := (((singularChainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj X)
  set K_ab := (((singularChainComplexFunctor.{0} AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)).obj X)


  have bridge : F.obj (K_mod.homology n) ≅ K_ab.homology n :=
    ((K_mod.sc n).mapHomologyIso F).symm ≪≫
    HomologicalComplex.homologyMapIso (iso := singularChainComplexFunctor_forget₂_iso X) (i := n)
  constructor
  · intro h
    exact IsZero.of_iso (Functor.map_isZero F h) bridge.symm
  · intro h
    exact IsZero.of_full_of_faithful_of_isZero F _ (IsZero.of_iso h bridge)

/-- Vanishing of sphere homology: $H_n(S^m; \mathbb{Z}) = 0$ for $0 < n < m$.
Obtained by transporting `SphereHomology.sphere_homology_vanishing` from
abelian-group coefficients to $\mathbb{Z}$-module coefficients. -/
theorem sphereChainZ_homology_isZero (m n : ℕ) (hn_lt : n < m) (hn_pos : 0 < n) :
    IsZero ((sphereChainZ m).homology n) := by


  have e_chain : sphereChainZ m ≅
      (((singularChainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of (SphereHomology.Sphere m))) :=
    ((singularChainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).mapIso
      (sphereTopCatIso m)
  exact IsZero.of_iso
    ((moduleCat_singularHomology_isZero_iff (TopCat.of (SphereHomology.Sphere m)) n).mpr
      (SphereHomology.sphere_homology_vanishing n m (by omega) (by omega) (by omega)))
    (HomologicalComplex.homologyMapIso (iso := e_chain) (i := n))

/-- All Ext groups out of a zero object vanish: $\mathrm{Ext}^n(0, Y) = 0$ for
every $n \ge 0$ and every $\mathbb{Z}$-module $Y$. -/
lemma isZero_Ext_of_isZero {X : ModuleCat.{0} ℤ} (hX : IsZero X)
    (Y : ModuleCat.{0} ℤ) (n : ℕ) :
    IsZero (((Ext ℤ (ModuleCat.{0} ℤ) n).obj (Opposite.op X)).obj Y) := by
  haveI : CategoryTheory.Projective X := hX.projective
  cases n with
  | zero =>
    refine IsZero.of_iso ?_ ((CategoryTheory.ProjectiveResolution.self X).isoExt 0 Y)
    rw [← HomologicalComplex.exactAt_iff_isZero_homology, HomologicalComplex.exactAt_iff]
    refine ShortComplex.exact_of_isZero_X₂ _ ?_
    dsimp [ChainComplex.linearYonedaObj]
    rw [IsZero.iff_id_eq_zero]
    ext (f : X ⟶ Y)
    exact (hX.eq_of_src f 0).symm ▸ rfl
  | succ k =>
    exact isZero_Ext_succ_of_projective X Y k


/-- For $m \ge 2$, the degree-$0$ homology $H_0(S^m; \mathbb{Z}) \cong \mathbb{Z}$
is a projective $\mathbb{Z}$-module (indeed free), so its Ext groups vanish in
positive degree. -/
theorem sphereChainZ_homology_zero_projective (m : ℕ) (hm : m ≥ 2) :
    CategoryTheory.Projective ((sphereChainZ m).homology 0) := by sorry

/-- Vanishing of the $\mathrm{Ext}^1$ term appearing in the UCT for $H^n(S^m; \mathbb{Z})$
when $0 < n < m$: either $n - 1 > 0$ and the previous homology vanishes, or $n = 1$
and $H_0(S^m; \mathbb{Z})$ is projective. -/
theorem sphereChainZ_ext1_isZero (m n : ℕ) (hn_lt : n < m) (hn_pos : 0 < n) :
    IsZero (((Ext ℤ (ModuleCat.{0} ℤ) 1).obj
      (Opposite.op ((sphereChainZ m).homology (n - 1)))).obj (ModuleCat.of ℤ ℤ)) := by
  by_cases hn : n ≥ 2
  ·
    have h_nm1_pos : 0 < n - 1 := by omega
    have h_nm1_lt : n - 1 < m := by omega
    exact isZero_Ext_of_isZero (sphereChainZ_homology_isZero m (n - 1) h_nm1_lt h_nm1_pos) _ 1
  ·
    have hn1 : n = 1 := by omega
    subst hn1
    simp only [show 1 - 1 = 0 from rfl]
    have hm2 : m ≥ 2 := by omega
    haveI := sphereChainZ_homology_zero_projective m hm2
    exact isZero_Ext_succ_of_projective _ _ 0

/-- Vanishing of the $\mathrm{Ext}^0 = \mathrm{Hom}$ term in the UCT for
$H^n(S^m; \mathbb{Z})$ when $0 < n < m$: this $\mathrm{Hom}$ vanishes because
$H_n(S^m; \mathbb{Z}) = 0$ in that range. -/
theorem sphereChainZ_ext0_isZero (m n : ℕ) (hn_lt : n < m) (hn_pos : 0 < n) :
    IsZero (((Ext ℤ (ModuleCat.{0} ℤ) 0).obj
      (Opposite.op ((sphereChainZ m).homology n))).obj (ModuleCat.of ℤ ℤ)) :=
  isZero_Ext_of_isZero (sphereChainZ_homology_isZero m n hn_lt hn_pos) _ 0

/-- Vanishing of sphere cohomology in intermediate degrees:
$H^n(S^m; \mathbb{Z}) = 0$ for $0 < n < m$. Combines the UCT short exact sequence
with the vanishing of the relevant Ext terms. -/
theorem sphere_cohom_isZero (m n : ℕ) (hn_lt : n < m) (hn_pos : 0 < n) :
    IsZero (singCohom ℤ (ModuleCat.of ℤ ℤ) (TopCat.sphere.{0} m) n) := by

  obtain ⟨S, hX₁, hX₂, hX₃, hSE, _⟩ :=
    UniversalCoefficientTheorem.cohomologyUCT ℤ (sphereChainZ m) (ModuleCat.of ℤ ℤ)
      (sphereChainZ_free m) n

  have hcohom : S.X₂ = singCohom ℤ (ModuleCat.of ℤ ℤ) (TopCat.sphere.{0} m) n := hX₂

  have hZ₁ : IsZero S.X₁ := hX₁ ▸ sphereChainZ_ext1_isZero m n hn_lt hn_pos

  have hZ₃ : IsZero S.X₃ := hX₃ ▸ sphereChainZ_ext0_isZero m n hn_lt hn_pos

  rw [← hcohom]
  exact hSE.exact.isZero_of_both_zeros (hZ₁.eq_of_src _ _) (hZ₃.eq_of_tgt _ _)


/-- Factorisation supplied by the Künneth/cup-product structure on the cohomology
of $S^p \times S^q$: the pullback $f^* : H^{p+q}(S^p \times S^q) \to H^{p+q}(S^{p+q})$
factors as a composition $g \circ h$ through $H^p(S^{p+q})$, reflecting that any
top-degree class on the product is a cup product of $p$- and $q$-dimensional classes. -/
theorem kunneth_pullback_factors (p q : ℕ)
    (f : TopCat.sphere.{0} (p + q) ⟶ TopCat.sphere.{0} p ⨯ TopCat.sphere.{0} q) :
    ∃ (g : singCohom ℤ (ModuleCat.of ℤ ℤ)
           (TopCat.sphere.{0} p ⨯ TopCat.sphere.{0} q) (p + q) ⟶
           singCohom ℤ (ModuleCat.of ℤ ℤ) (TopCat.sphere.{0} (p + q)) p)
      (h : singCohom ℤ (ModuleCat.of ℤ ℤ) (TopCat.sphere.{0} (p + q)) p ⟶
           singCohom ℤ (ModuleCat.of ℤ ℤ) (TopCat.sphere.{0} (p + q)) (p + q)),
      cohomPullback ℤ (ModuleCat.of ℤ ℤ) f (p + q) = g ≫ h := by sorry


/-- If $f^*$ factors through the (zero) group $H^p(S^{p+q})$, then $f^*$ itself
vanishes. The technical bridge between `kunneth_pullback_factors` and the main
corollary. -/
theorem pullback_zero_of_cup_factors (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q)
    (f : TopCat.sphere.{0} (p + q) ⟶ TopCat.sphere.{0} p ⨯ TopCat.sphere.{0} q)
    (hp_zero : IsZero (singCohom ℤ (ModuleCat.of ℤ ℤ) (TopCat.sphere.{0} (p + q)) p))
    (_hq_zero : IsZero (singCohom ℤ (ModuleCat.of ℤ ℤ) (TopCat.sphere.{0} (p + q)) q)) :
    cohomPullback ℤ (ModuleCat.of ℤ ℤ) f (p + q) = 0 := by


  obtain ⟨g, h, hfact⟩ := kunneth_pullback_factors p q f
  rw [hfact, hp_zero.eq_zero_of_tgt g, zero_comp]


/-- **Corollary 29.4.** For any continuous map $f : S^{p+q} \to S^p \times S^q$
with $p, q > 0$, the induced pullback on top-degree cohomology vanishes:
$$f^* : H^{p+q}(S^p \times S^q; \mathbb{Z}) \longrightarrow H^{p+q}(S^{p+q}; \mathbb{Z})
\quad \text{is the zero map.}$$
Consequence: the top cohomology class $\alpha \times \beta$ of the product cannot
be pulled back nontrivially to a sphere, ruling out an $H$-space structure on
spheres other than $S^1, S^3, S^7$ (the classical application). -/
theorem sphere_product_pullback_zero (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (f : TopCat.sphere.{0} (p + q) ⟶ TopCat.sphere.{0} p ⨯ TopCat.sphere.{0} q) :
    cohomPullback ℤ (ModuleCat.of ℤ ℤ) f (p + q) = 0 := by
  have hp_zero := sphere_cohom_isZero (p + q) p (by omega) hp
  have hq_zero := sphere_cohom_isZero (p + q) q (by omega) hq
  exact pullback_zero_of_cup_factors p q hp hq f hp_zero hq_zero

end SphereCupProduct

end CupProduct

namespace SphereHomology

open CategoryTheory AlgebraicTopology AlgebraicTopologyI

/-- Identification of the Mathlib sphere `TopCat.sphere m` with the local
`SphereHomology.Sphere m`, repeated here in the `SphereHomology` namespace for
ergonomic access. -/
noncomputable def sphereTopCatIso (m : ℕ) :
    TopCat.sphere.{0} m ≅ TopCat.of (SphereHomology.Sphere m) :=
  TopCat.isoOfHomeo Homeomorph.ulift

/-- Functoriality of the singular chain complex with $\mathbb{Z}$-coefficients:
a homeomorphism (or `TopCat`-iso) $X \simeq Y$ induces an isomorphism of chain
complexes $C_*(X; \mathbb{Z}) \simeq C_*(Y; \mathbb{Z})$. -/
noncomputable def singularChainComplexZ_iso_of_topIso {X Y : TopCat.{0}} (e : X ≅ Y) :
    singularChainComplexZ X ≅ singularChainComplexZ Y :=
  ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).mapIso e

end SphereHomology
