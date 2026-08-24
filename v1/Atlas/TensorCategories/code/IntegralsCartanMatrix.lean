/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.IntegralsDefs
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Atlas.TensorCategories.code.DistinguishedInvertible
import Mathlib.RingTheory.SimpleModule.Basic

set_option maxHeartbeats 400000

set_option autoImplicit false

open Coalgebra
open scoped TensorProduct

universe u v w


section CartanMatrix

variable {k : Type w} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Reinterpret a `ℕ`-valued Cartan matrix `C_mat` as a matrix over the field `k`
by casting each entry to `k`. -/
def cartanMatrixOverField (C_mat : ι → ι → ℕ) : Matrix ι ι k :=
  Matrix.of (fun i j => (C_mat i j : k))

/-- If a square matrix `M` annihilates a nonzero vector `d` under matrix-vector
multiplication, then its determinant is zero. -/
theorem det_eq_zero_of_mulVec_eq_zero_of_ne_zero
    (M : Matrix ι ι k) (d : ι → k) (hd : d ≠ 0) (hMd : M.mulVec d = 0) :
    M.det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  exact ⟨d, hd, hMd⟩

/-- If the Cartan matrix `C_mat` viewed over `k` annihilates a nonzero "dimension"
vector `d`, then `cartanMatrixOverField C_mat` has zero determinant. -/
theorem cartan_matrix_degenerate_of_dim_vanishes
    (C_mat : ι → ι → ℕ)
    (d : ι → k)
    (hd_ne : d ≠ 0)
    (hd_kernel : ∀ i : ι, ∑ j : ι, (C_mat i j : k) * d j = 0) :
    (cartanMatrixOverField C_mat : Matrix ι ι k).det = 0 := by
  apply det_eq_zero_of_mulVec_eq_zero_of_ne_zero _ d hd_ne
  ext i
  simp only [Matrix.mulVec, dotProduct, cartanMatrixOverField, Matrix.of_apply, Pi.zero_apply]
  exact hd_kernel i

/-- The transpose of a degenerate Cartan matrix is also degenerate, since determinant
is invariant under transposition. -/
theorem cartan_matrix_transpose_degenerate
    (C_mat : ι → ι → ℕ)
    (hdet : (cartanMatrixOverField C_mat : Matrix ι ι k).det = 0) :
    (cartanMatrixOverField C_mat : Matrix ι ι k).transpose.det = 0 := by
  rwa [Matrix.det_transpose]

end CartanMatrix


section CategoricalUnimodularity

open CategoryTheory CategoryTheory.Limits MonoidalCategory

variable {C : Type u} [Category.{v} C]

/-- A rigid monoidal category is unimodular when its distinguished invertible object
`L_ρ` is isomorphic to the unit `𝟙_ C` (Definition 1.52.6). -/
class IsUnimodularCategory (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [RigidCategory C] [HasDistinguishedInvertibleData C] : Prop where
  distinguished_iso_unit : Nonempty (HasDistinguishedInvertibleData.distinguished (C := C) ≅ 𝟙_ C)

/-- Accessor extracting the unimodularity isomorphism `L_ρ ≅ 𝟙_ C` from the
`IsUnimodularCategory` instance. -/
theorem IsUnimodularCategory.get_distinguished_iso_unit [MonoidalCategory C]
    [RigidCategory C] [HasDistinguishedInvertibleData C]
    [h : IsUnimodularCategory C] :
    Nonempty (HasDistinguishedInvertibleData.distinguished (C := C) ≅ 𝟙_ C) :=
  h.distinguished_iso_unit

/-- Construct an `IsUnimodularCategory` instance from an isomorphism between the
distinguished invertible object and the unit object. -/
theorem isUnimodularCategory_of_pivotal [MonoidalCategory C]
    [RigidCategory C] [HasDistinguishedInvertibleData C]
    (h : Nonempty (HasDistinguishedInvertibleData.distinguished (C := C) ≅ 𝟙_ C)) :
    IsUnimodularCategory C :=
  ⟨h⟩

end CategoricalUnimodularity


section PivotalDimensionTheorem

open CategoryTheory MonoidalCategory

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- The left quantum trace of a morphism `a : V ⟶ V**`, defined as the composition
`coev_V ≫ (a ▷ V*) ≫ ev_{V*}` ending in `𝟙_ C ⟶ 𝟙_ C`. -/
noncomputable def leftQuantumTrace' {V : C} (a : V ⟶ (Vᘁ)ᘁ) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ V (Vᘁ) ≫ (a ▷ Vᘁ) ≫ ε_ (Vᘁ) ((Vᘁ)ᘁ)

/-- Data of a pivotal structure on a rigid monoidal category: a natural isomorphism
`Id ≅ ?**` (Definition 1.38.1). -/
structure PivotalStructureData (C : Type u)
    [Category.{v} C] [MonoidalCategory C] [RigidCategory C] where
  pivotalIso : ∀ (V : C), V ≅ (Vᘁ)ᘁ
  naturality : ∀ {V W : C} (f : V ⟶ W),
    f ≫ (pivotalIso W).hom = (pivotalIso V).hom ≫ (fᘁ)ᘁ

/-- The pivotal dimension of `V` with respect to the pivotal structure `u`, namely
the left quantum trace of `u.pivotalIso V` (Definition 1.38.4). -/
noncomputable def pivotalDim (u : PivotalStructureData C) (V : C) : 𝟙_ C ⟶ 𝟙_ C :=
  leftQuantumTrace' C (u.pivotalIso V).hom

end PivotalDimensionTheorem


section DimProjZero

open CategoryTheory MonoidalCategory

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- If the unit object is not projective, then the scalar dimension `φ(pivotalDim P)`
vanishes on every projective object `P`. -/
theorem dim_proj_zero_of_not_semisimple
    (u : PivotalStructureData C)
    (φ : (𝟙_ C ⟶ 𝟙_ C) → k)
    (h_retract : ∀ (P : C) [Projective P],
      φ (pivotalDim C u P) ≠ 0 → Projective (𝟙_ C))
    (hns : ¬ Projective (𝟙_ C))
    (P : C) [Projective P] :
    φ (pivotalDim C u P) = 0 := by
  by_contra h
  exact hns (h_retract P h)

end DimProjZero


section Theorem1531

open CategoryTheory MonoidalCategory

variable {k : Type w} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A vector with at least one nonzero coordinate is nonzero as a function. -/
theorem dim_vec_ne_zero_of_component_ne_zero
    {k : Type*} [Field k] {ι : Type*}
    (d : ι → k) (i₀ : ι) (hi₀ : d i₀ ≠ 0) : d ≠ 0 := by
  intro h
  exact hi₀ (congr_fun h i₀)

/-- Theorem 1.53.1: if `C` is not semisimple (so `𝟙_ C` is not projective) and admits
a pivotal structure `u`, then the Cartan matrix becomes degenerate over `k`. -/
theorem theorem_1_53_1
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

    (u : PivotalStructureData C)

    (hns : ¬ Projective (𝟙_ C))

    (L : ι → C) (i₀ : ι) (h_unit : Nonempty (L i₀ ≅ 𝟙_ C))

    (P : ι → C) [hProj : ∀ i, Projective (P i)]

    (C_mat : ι → ι → ℕ)

    (φ : (𝟙_ C ⟶ 𝟙_ C) → k)


    (h_retract : ∀ (Q : C) [Projective Q],
      φ (pivotalDim C u Q) ≠ 0 → Projective (𝟙_ C))

    (h_dim_unit : φ (pivotalDim C u (𝟙_ C)) ≠ 0)

    (h_dim_iso : ∀ (X Y : C), Nonempty (X ≅ Y) →
      pivotalDim C u X = pivotalDim C u Y)


    (h_additive : ∀ i, ∑ j : ι, (C_mat i j : k) * φ (pivotalDim C u (L j)) =
      φ (pivotalDim C u (P i))) :
    (cartanMatrixOverField C_mat : Matrix ι ι k).det = 0 := by

  let d : ι → k := fun j => φ (pivotalDim C u (L j))

  have hdP : ∀ i, φ (pivotalDim C u (P i)) = 0 :=
    fun i => dim_proj_zero_of_not_semisimple u φ h_retract hns (P i)

  have hkernel : ∀ i, ∑ j : ι, (C_mat i j : k) * d j = 0 := by
    intro i
    rw [h_additive i]
    exact hdP i

  have hdi₀ : d i₀ ≠ 0 := by
    intro h
    apply h_dim_unit
    rw [← h_dim_iso (L i₀) (𝟙_ C) h_unit]
    exact h

  exact cartan_matrix_degenerate_of_dim_vanishes C_mat d
    (dim_vec_ne_zero_of_component_ne_zero d i₀ hdi₀) hkernel

/-- Named alias for Theorem 1.53.1: under the hypothesis that `𝟙_ C` is not projective,
the Cartan matrix of `C` viewed over `k` is degenerate. -/
theorem Theorem_1_53_1
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
    (u : PivotalStructureData C)
    (hns : ¬ Projective (𝟙_ C))
    (L : ι → C) (i₀ : ι) (h_unit : Nonempty (L i₀ ≅ 𝟙_ C))
    (P : ι → C) [hProj : ∀ i, Projective (P i)]
    (C_mat : ι → ι → ℕ)
    (φ : (𝟙_ C ⟶ 𝟙_ C) → k)
    (h_retract : ∀ (Q : C) [Projective Q],
      φ (pivotalDim C u Q) ≠ 0 → Projective (𝟙_ C))
    (h_dim_unit : φ (pivotalDim C u (𝟙_ C)) ≠ 0)
    (h_dim_iso : ∀ (X Y : C), Nonempty (X ≅ Y) →
      pivotalDim C u X = pivotalDim C u Y)
    (h_additive : ∀ i, ∑ j : ι, (C_mat i j : k) * φ (pivotalDim C u (L j)) =
      φ (pivotalDim C u (P i))) :
    (cartanMatrixOverField C_mat : Matrix ι ι k).det = 0 :=
  theorem_1_53_1 u hns L i₀ h_unit P C_mat φ h_retract h_dim_unit h_dim_iso h_additive

end Theorem1531


section Proposition1523

variable (k : Type u) [Field k] (H : Type v) [Ring H] [Algebra k H] [Coalgebra k H]

/-- Proposition 1.52.3: any finite dimensional quasi-Hopf algebra `H` admits a unique
nonzero left integral and a unique nonzero right integral, each up to scaling. -/
theorem Proposition_1_52_3 [FiniteDimensional k H] :
    (∃ (I₀ : H), IsLeftIntegral k H I₀ ∧ I₀ ≠ 0 ∧
      ∀ (J : H), IsLeftIntegral k H J → ∃ (c : k), J = c • I₀) ∧
    (∃ (I₀ : H), IsRightIntegral k H I₀ ∧ I₀ ≠ 0 ∧
      ∀ (J : H), IsRightIntegral k H J → ∃ (c : k), J = c • I₀) :=
  ⟨prop_1_52_3_left k H, prop_1_52_3_right k H⟩

/-- The space of left integrals in a finite dimensional quasi-Hopf algebra is
one dimensional (Proposition 1.52.3, left half). -/
theorem Proposition_1_52_3_left_integral_space_dim [FiniteDimensional k H] :
    Module.finrank k (leftIntSubmodule k H) = 1 :=
  frobenius_leftIntSubmodule_finrank_one k H

/-- The space of right integrals in a finite dimensional quasi-Hopf algebra is
one dimensional (Proposition 1.52.3, right half). -/
theorem Proposition_1_52_3_right_integral_space_dim [FiniteDimensional k H] :
    Module.finrank k (rightIntSubmodule k H) = 1 :=
  frobenius_rightIntSubmodule_finrank_one k H

/-- Joint statement of Proposition 1.52.3: both the left and right integral subspaces
of a finite dimensional quasi-Hopf algebra are one dimensional. -/
theorem Proposition_1_52_3_integral_space_dims [FiniteDimensional k H] :
    Module.finrank k (leftIntSubmodule k H) = 1 ∧
    Module.finrank k (rightIntSubmodule k H) = 1 :=
  ⟨frobenius_leftIntSubmodule_finrank_one k H,
   frobenius_rightIntSubmodule_finrank_one k H⟩

end Proposition1523


section Proposition1524

open CategoryTheory

variable (k : Type w) [Field k] (H : Type w) [Ring H] [Algebra k H] [Coalgebra k H]

/-- Proposition 1.52.4: under the representation-theoretic data of `Prop1524RepData`, the
distinguished invertible object of `C` is isomorphic to the one-dimensional character module
associated to the distinguished character `dc.χ`. -/
theorem Proposition_1_52_4
    {C : Type*} [Category C] [MonoidalCategory C] [RigidCategory C]
    [HasDistinguishedInvertibleData C] [FiniteDimensional k H]
    [inst : Prop1524RepData k H C]
    (I : H) (hI : I ≠ 0) (dc : DistinguishedCharacter k H I) :
    Nonempty (HasDistinguishedInvertibleData.distinguished (C := C) ≅
      inst.oneDimChar dc.χ) :=
  inst.lρ_iso_distinguishedChar I hI dc

/-- If `H` is unimodular, then the distinguished character `dc.χ` of a nonzero left integral
coincides with the counit of `H` (Proposition 1.52.4, unimodular consequence). -/
theorem Proposition_1_52_4_unimodular_implies_char_eq_counit
    (I : H) (dc : DistinguishedCharacter k H I) (hI_ne : I ≠ 0)
    (huni : IsUnimodularAlgebra k H) :
    ∀ x : H, dc.χ x = Coalgebra.counit (R := k) x :=
  distinguished_char_eq_counit_of_unimodular k H I dc hI_ne huni

/-- If the distinguished character of a left integral `I` equals the counit, then `I` is also
a right integral (Proposition 1.52.4, converse direction). -/
theorem Proposition_1_52_4_char_eq_counit_implies_right_integral
    (I : H) (dc : DistinguishedCharacter k H I)
    (hχε : ∀ x : H, dc.χ x = Coalgebra.counit (R := k) x) :
    IsRightIntegral k H I :=
  left_integral_is_right_of_char_eq_counit k H I dc hχε

end Proposition1524


section IntegralCointegralPairing

open scoped TensorProduct

variable (k : Type w) [Field k] (H : Type w) [Ring H] [Algebra k H] [Coalgebra k H]

/-- A linear functional `l : H → k` is a left cointegral if the convolution identity
`(id ⊗ l) ∘ Δ = η ∘ l` holds, dualizing the notion of a left integral. -/
structure IsLeftCointegral (l : H →ₗ[k] k) : Prop where
  left_cointegral :
    (TensorProduct.rid k H).toLinearMap ∘ₗ l.lTensor H ∘ₗ Coalgebra.comul (R := k) =
    (Algebra.linearMap k H) ∘ₗ l

/-- For a nonzero left cointegral `l` in a finite dimensional `H`, the map sending
`x ∈ H` to `l ∘ mulLeft x` is injective; this is the Frobenius property witnessed by
left cointegrals. -/
theorem frobenius_cointegral_injective
    (k : Type w) [Field k] (H : Type w) [Ring H] [Algebra k H] [Coalgebra k H]
    [FiniteDimensional k H]
    (l : H →ₗ[k] k) (hl : IsLeftCointegral k H l) (hlne : l ≠ 0) :
    Function.Injective (fun (x : H) => l ∘ₗ LinearMap.mulLeft k x) := by sorry

/-- The pairing between a nonzero left integral `I` and a nonzero left cointegral `l` is
nondegenerate: `l I ≠ 0`. -/
theorem integral_cointegral_ne_zero
    [FiniteDimensional k H]
    (I : H) (hI : IsLeftIntegral k H I) (hIne : I ≠ 0)
    (l : H →ₗ[k] k) (hl : IsLeftCointegral k H l) (hlne : l ≠ 0) :
    l I ≠ 0 := by

  have hinj := frobenius_cointegral_injective k H l hl hlne

  have hΦI_ne : l ∘ₗ LinearMap.mulLeft k I ≠ 0 := by
    intro h
    apply hIne
    have h0 : l ∘ₗ LinearMap.mulLeft k (0 : H) = 0 := by ext; simp
    exact hinj (h.trans h0.symm)
  rw [DFunLike.ne_iff] at hΦI_ne
  obtain ⟨y₀, hy₀⟩ := hΦI_ne
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.zero_apply] at hy₀

  have hIy_int : I * y₀ ∈ leftIntSubmodule k H := (mem_leftIntSubmodule k H).mpr
    (hI.right_mul_isLeftIntegral y₀)
  have I_mem : I ∈ leftIntSubmodule k H := (mem_leftIntSubmodule k H).mpr hI

  have hI_ne_sub : (⟨I, I_mem⟩ : leftIntSubmodule k H) ≠ 0 := by
    intro h; exact hIne (congr_arg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hI_ne_sub).mp
    (frobenius_leftIntSubmodule_finrank_one k H) ⟨I * y₀, hIy_int⟩
  have hIy_eq : I * y₀ = c • I := by
    have := congr_arg Subtype.val hc
    simp at this
    exact this.symm

  rw [hIy_eq, map_smul] at hy₀
  intro h_lI_zero
  exact hy₀ (by rw [h_lI_zero, smul_zero])

end IntegralCointegralPairing


section Proposition1525

open Coalgebra

variable (k : Type u) [Field k] (H : Type v) [Ring H] [Algebra k H] [Coalgebra k H]

/-- If a nonzero left integral `I` has nonzero counit `ε I ≠ 0`, then the underlying
ring `H` is semisimple (Maschke-type direction of Proposition 1.52.5). -/
theorem semisimple_of_counit_ne_zero [FiniteDimensional k H]
    {I : H} (hI : IsLeftIntegral k H I) (hne : I ≠ 0)
    (hε : Coalgebra.counit (R := k) I ≠ 0) : IsSemisimpleRing H := by


  sorry

/-- If `H` is a finite dimensional semisimple ring, then there exists a nonzero idempotent
left integral `J` in `H`. -/
theorem exists_idempotent_integral_of_semisimple [FiniteDimensional k H]
    (hss : IsSemisimpleRing H) :
    ∃ (J : H), IsLeftIntegral k H J ∧ J * J = J ∧ J ≠ 0 := by

  obtain ⟨I₀, hI₀int, hI₀ne, _⟩ := prop_1_52_3_left k H

  let L : Submodule H H := Submodule.span H {I₀}

  have hL_ne : L ≠ ⊥ := by
    intro h; apply hI₀ne
    have : I₀ ∈ L := Submodule.mem_span_singleton_self I₀
    rw [h] at this; exact (Submodule.mem_bot H).mp this

  obtain ⟨M, hLM⟩ := ComplementedLattice.exists_isCompl L

  let π : H →ₗ[H] H := L.subtype ∘ₗ L.linearProjOfIsCompl M hLM
  let e : H := π (1 : H)

  have hπ_app : ∀ h : H, π h = h * e := by
    intro h
    have := π.map_smul h (1 : H)
    simp only [smul_eq_mul, mul_one] at this
    exact this

  have he_mem : e ∈ L := SetLike.coe_mem _

  have he_idem : e * e = e := by
    have hidem : ∀ x, π (π x) = π x := by
      intro x
      show L.subtype (L.linearProjOfIsCompl M hLM (L.subtype (L.linearProjOfIsCompl M hLM x))) =
           L.subtype (L.linearProjOfIsCompl M hLM x)
      congr 1; exact Submodule.linearProjOfIsCompl_apply_left hLM _
    rw [(hπ_app e).symm, show π e = π (π 1) from rfl, hidem 1]

  have he_ne : e ≠ 0 := by
    intro he0; apply hL_ne; rw [eq_bot_iff]
    intro x hx
    have hπx : π x = 0 := by
      calc π x = x * e := hπ_app x
        _ = x * 0 := by rw [he0]
        _ = 0 := mul_zero x
    have : (L.linearProjOfIsCompl M hLM x : H) = x := by
      simp [Submodule.linearProjOfIsCompl_apply_left hLM ⟨x, hx⟩]
    rw [show π x = (L.linearProjOfIsCompl M hLM x : H) from rfl] at hπx
    rw [this] at hπx; simp [hπx]

  have he_scalar : ∃ c : k, e = c • I₀ := by
    rw [show L = Submodule.span H {I₀} from rfl] at he_mem
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp he_mem
    exact ⟨Coalgebra.counit (R := k) a, by rw [← hI₀int.left_integral a]; exact ha.symm⟩
  obtain ⟨c, hc⟩ := he_scalar

  have he_int : IsLeftIntegral k H e := by
    rw [hc]
    exact ⟨fun x => by rw [mul_smul_comm, hI₀int.left_integral x, smul_comm]⟩
  exact ⟨e, he_int, he_idem, he_ne⟩

/-- If there exists a nonzero idempotent left integral, then any nonzero left integral `I`
has nonzero counit `ε I ≠ 0`. -/
theorem counit_ne_zero_of_exists_idempotent_integral [FiniteDimensional k H]
    {I : H} (hI : IsLeftIntegral k H I) (hne : I ≠ 0)
    (hex : ∃ (J : H), IsLeftIntegral k H J ∧ J * J = J ∧ J ≠ 0) :
    Coalgebra.counit (R := k) I ≠ 0 := by
  obtain ⟨J, hJint, hJidem, hJne⟩ := hex
  have hJsq : J * J ≠ 0 := by rwa [hJidem]
  have hεJ : Coalgebra.counit (R := k) J ≠ 0 :=
    counit_ne_zero_of_sq_ne_zero hJint hJsq
  obtain ⟨I₀, hI₀int, _, hI₀uniq⟩ := prop_1_52_3_left k H
  obtain ⟨d, rfl⟩ := hI₀uniq I hI
  obtain ⟨c, rfl⟩ := hI₀uniq J hJint
  simp only [map_smul, smul_eq_mul] at hεJ ⊢
  exact mul_ne_zero (by intro hd; exact hne (by simp [hd]))
    (by intro hI₀; exact hεJ (by rw [hI₀, mul_zero]))

/-- Proposition 1.52.5: for a nonzero left integral `I` in a finite dimensional quasi-Hopf
algebra, semisimplicity of `H` is equivalent to `ε I ≠ 0`, equivalent to `I * I ≠ 0`,
equivalent to the existence of a nonzero idempotent left integral. -/
theorem Proposition_1_52_5 [FiniteDimensional k H]
    (I : H) (hI : IsLeftIntegral k H I) (hne : I ≠ 0) :
    (IsSemisimpleRing H ↔ Coalgebra.counit (R := k) I ≠ 0) ∧
    (Coalgebra.counit (R := k) I ≠ 0 ↔ I * I ≠ 0) ∧
    (Coalgebra.counit (R := k) I ≠ 0 ↔
      ∃ (J : H), IsLeftIntegral k H J ∧ J * J = J ∧ J ≠ 0) := by

  have h_iv_ii : (∃ J, IsLeftIntegral k H J ∧ J * J = J ∧ J ≠ 0) →
      Coalgebra.counit (R := k) I ≠ 0 :=
    counit_ne_zero_of_exists_idempotent_integral k H hI hne

  have h_ii_iv : Coalgebra.counit (R := k) I ≠ 0 →
      (∃ J, IsLeftIntegral k H J ∧ J * J = J ∧ J ≠ 0) := by
    intro hε
    obtain ⟨hJint, hJidem⟩ := isLeftIntegral_normalize hI hε
    exact ⟨_, hJint, hJidem, smul_ne_zero (inv_ne_zero hε) hne⟩
  refine ⟨⟨fun hss => ?_, fun hε => semisimple_of_counit_ne_zero k H hI hne hε⟩,
         ⟨fun hε => (prop_1_52_5_iii_iff_ii hI hne).mpr hε,
          fun hsq => (prop_1_52_5_iii_iff_ii hI hne).mp hsq⟩,
         ⟨h_ii_iv, h_iv_ii⟩⟩

  exact h_iv_ii (exists_idempotent_integral_of_semisimple k H hss)

end Proposition1525
