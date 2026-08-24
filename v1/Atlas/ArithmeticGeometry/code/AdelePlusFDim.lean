/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.AdeleQuotientDim
import Mathlib.Order.ModularLattice

open scoped RestrictedProduct
open FunctionFieldAdeleRing DiscreteValuationFamily

section Lemma22_9

variable {F : Type*} [Field F] {P : Type*} [DecidableEq P]
  {O : P → ValuationSubring F}
  (k : Type*) [Field k] [Algebra k F]
  [ConstantField k (F := F) (P := P) (O := O)]
  [FunctionFieldProperty F P O]
  [DiscreteValuationFamily P F k]
  [HasResidueFieldSurjection P F k O]

/-- The $k$-subspace $A(D) + F \subseteq \mathbb{A}_F$: the sum of the adele
divisor space $A(D)$ and the principal adeles (the image of $F$ embedded
diagonally). -/
noncomputable abbrev AF_subspace (D : P → ℤ) :
    Submodule k (FunctionFieldAdeleRing F P O) :=
  adeleSpace (F := F) (O := O) k D ⊔ principalAdeles (F := F) (P := P) (O := O) k

/-- The $k$-subspace $A(D) \cap F$ inside $\mathbb{A}_F$: elements of the
function field that satisfy the divisor bounds at every place. -/
noncomputable abbrev LF_subspace (D : P → ℤ) :
    Submodule k (FunctionFieldAdeleRing F P O) :=
  adeleSpace (F := F) (O := O) k D ⊓ principalAdeles (F := F) (P := P) (O := O) k

/-- Monotonicity of the $A(D) + F$ subspaces in the divisor: $A \le B$
implies $A(A) + F \subseteq A(B) + F$. -/
theorem AF_subspace_mono {A B : P → ℤ} (hAB : ∀ p, A p ≤ B p) :
    AF_subspace (F := F) (O := O) k A ≤ AF_subspace (F := F) (O := O) k B :=
  sup_le_sup_right (adeleSpace_mono k hAB) _

/-- Riemann-Roch space $L(D) = \{f \in F \mid \mathrm{ord}_p(f) \ge -D(p)
\text{ for all } p\}$ realized as the preimage of $A(D)$ under the diagonal
embedding $F \hookrightarrow \mathbb{A}_F$. -/
noncomputable def rrSpaceAdele (D : P → ℤ) : Submodule k F :=
  Submodule.comap (diagonalLinearMap (F := F) (P := P) (O := O) k)
    (adeleSpace (F := F) (O := O) k D)

/-- For the zero divisor, $L(0)$ consists of constants: $L(0) \subseteq k$
(via the algebra map $k \hookrightarrow F$). -/
theorem rrSpaceAdele_zero_le_constants :
  ∀ {F : Type*} [Field F] {P : Type*} [DecidableEq P]
    {O : P → ValuationSubring F}
    (k : Type*) [Field k] [Algebra k F]
    [ConstantField k (F := F) (P := P) (O := O)]
    [FunctionFieldProperty F P O]
    [DiscreteValuationFamily P F k]
    [HasResidueFieldSurjection P F k O],
    rrSpaceAdele (F := F) (O := O) k (0 : P → ℤ) ≤
      LinearMap.range (Algebra.linearMap k F) := by sorry

/-- $L(0)$ is finite-dimensional over $k$: it is contained in the
$k$-algebra-image of $k$ inside $F$. -/
theorem rrSpaceAdele_zero_finiteDimensional :
    FiniteDimensional k (rrSpaceAdele (F := F) (O := O) k (0 : P → ℤ)) := by
  have h_le := rrSpaceAdele_zero_le_constants (F := F) (O := O) k

  haveI : FiniteDimensional k (LinearMap.range (Algebra.linearMap k F)) := by
    have : LinearMap.range (Algebra.linearMap k F) ≤ ⊤ := le_top
    exact Module.Finite.range (Algebra.linearMap k F)

  exact Module.Finite.of_injective
    (Submodule.inclusion h_le)
    (Submodule.inclusion_injective h_le)

/-- Monotonicity of Riemann-Roch spaces: $D \le D'$ implies
$L(D) \subseteq L(D')$. -/
lemma rrSpaceAdele_mono {D D' : P → ℤ} (h : ∀ p, D p ≤ D' p) :
    rrSpaceAdele (F := F) (O := O) k D ≤ rrSpaceAdele (F := F) (O := O) k D' := by
  intro f hf
  simp only [rrSpaceAdele, Submodule.mem_comap] at hf ⊢
  exact adeleSpace_mono k h hf

/-- Inductive step for finite-dimensionality of $L(D)$: if $L(D)$ is
finite-dimensional and $D \le D'$, then $L(D')$ is finite-dimensional, using
Lemma 22.8 to bound $L(D')/L(D)$ inside $A(D')/A(D)$. -/
lemma rrSpaceAdele_fd_step
    (D D' : P →₀ ℤ) (h : ∀ p, D p ≤ D' p)
    (hFD_D : FiniteDimensional k (rrSpaceAdele (F := F) (O := O) k (D : P → ℤ))) :
    FiniteDimensional k (rrSpaceAdele (F := F) (O := O) k (D' : P → ℤ)) := by

  have h_adele := adeleSpace_quotient_finrank_eq (F := F) (O := O) k D D' h
  obtain ⟨hFD_adele, _⟩ := h_adele
  haveI := hFD_adele

  have h_mono : rrSpaceAdele (F := F) (O := O) k (D : P → ℤ) ≤
      rrSpaceAdele (F := F) (O := O) k (D' : P → ℤ) :=
    rrSpaceAdele_mono k h


  set L' := rrSpaceAdele (F := F) (O := O) k (D' : P → ℤ)
  set L := rrSpaceAdele (F := F) (O := O) k (D : P → ℤ)
  set N := Submodule.comap L'.subtype L with hN_def

  haveI : FiniteDimensional k ↥N := by
    exact Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe h_mono).symm


  set A' := adeleSpace (F := F) (O := O) k (D' : P → ℤ)
  set A := adeleSpace (F := F) (O := O) k (D : P → ℤ)
  set M := Submodule.comap A'.subtype A with hM_def

  have h_diag_mem : ∀ (f : ↥L'), diagonalLinearMap (F := F) (P := P) (O := O) k f.val ∈ A' := by
    intro ⟨f, hf⟩
    exact hf

  let ι : ↥L' →ₗ[k] ↥A' := {
    toFun := fun f => ⟨diagonalLinearMap k f.val, h_diag_mem f⟩
    map_add' := fun a b => by ext; simp [map_add]
    map_smul' := fun c a => by ext; simp [map_smul]
  }

  have h_ι_N : ∀ (f : ↥L') (hf : f ∈ N), ι f ∈ M := by
    intro ⟨f, hf_L'⟩ hf_N
    simp only [N, Submodule.mem_comap, Submodule.subtype_apply] at hf_N
    simp only [ι, M, Submodule.mem_comap, Submodule.subtype_apply]
    exact hf_N

  let ι_bar : (↥L' ⧸ N) →ₗ[k] (↥A' ⧸ M) :=
    N.liftQ (M.mkQ.comp ι) (fun x hx => by
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact h_ι_N x hx)

  have h_ι_inj : Function.Injective ι_bar := by
    rw [← LinearMap.ker_eq_bot]
    rw [Submodule.eq_bot_iff]
    intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
    rw [LinearMap.mem_ker] at hq
    simp only [ι_bar, Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.mkQ_apply] at hq
    rw [Submodule.Quotient.mk_eq_zero] at hq ⊢

    simp only [M, Submodule.mem_comap, Submodule.subtype_apply] at hq

    simp only [N, Submodule.mem_comap, Submodule.subtype_apply]
    exact hq

  haveI : FiniteDimensional k (↥L' ⧸ N) :=
    Module.Finite.of_injective ι_bar h_ι_inj

  exact Module.Finite.of_submodule_quotient N

/-- Lemma 22.9 (a). For any divisor $D$, the Riemann-Roch space $L(D)$ is
finite-dimensional over the constant field $k$. -/
theorem rrSpaceAdele_finiteDimensional :
  ∀ {F : Type*} [Field F] {P : Type*} [DecidableEq P]
    {O : P → ValuationSubring F}
    (k : Type*) [Field k] [Algebra k F]
    [ConstantField k (F := F) (P := P) (O := O)]
    [FunctionFieldProperty F P O]
    [DiscreteValuationFamily P F k]
    [HasResidueFieldSurjection P F k O]
    (D : P →₀ ℤ),
    FiniteDimensional k (rrSpaceAdele (F := F) (O := O) k (D : P → ℤ)) := by
  intro F _ P _ O k _ _ _ _ _ _ D

  set Dp : P →₀ ℤ := D.mapRange (fun n => max n 0) (by simp) with hDp_def

  have hDp_nonneg : ∀ p, 0 ≤ Dp p := by
    intro p; simp only [Dp, Finsupp.mapRange_apply]; exact le_max_right _ _
  have hD_le_Dp : ∀ p, D p ≤ Dp p := by
    intro p; simp only [Dp, Finsupp.mapRange_apply]; exact le_max_left _ _

  haveI h_base : FiniteDimensional k (rrSpaceAdele (F := F) (O := O) k (0 : P → ℤ)) :=
    rrSpaceAdele_zero_finiteDimensional k

  haveI h_pos : FiniteDimensional k (rrSpaceAdele (F := F) (O := O) k (Dp : P → ℤ)) := by
    have h_zero_le : ∀ p, (0 : P →₀ ℤ) p ≤ Dp p := by
      intro p; simp only [Finsupp.coe_zero, Pi.zero_apply]; exact hDp_nonneg p
    exact rrSpaceAdele_fd_step k 0 Dp h_zero_le h_base

  have h_le : rrSpaceAdele (F := F) (O := O) k (D : P → ℤ) ≤
      rrSpaceAdele (F := F) (O := O) k (Dp : P → ℤ) :=
    rrSpaceAdele_mono k hD_le_Dp
  have : (rrSpaceAdele (F := F) (O := O) k (Dp : P → ℤ)).FG := Submodule.FG.of_finite
  exact Module.Finite.of_fg (this.of_le h_le)

/-- The diagonal embedding $F \hookrightarrow \mathbb{A}_F$ is injective when
the set of places is nonempty. -/
lemma diagonalLinearMap_injective [Nonempty P] :
    Function.Injective (diagonalLinearMap (F := F) (P := P) (O := O) k) := by
  intro a b hab
  have h := FunctionFieldAdeleRing.ext_iff.mp hab
  exact h (Classical.arbitrary P)

/-- Identification of $L(D)$ with $A(D) \cap F$ under the diagonal embedding:
the image of $L(D)$ in $\mathbb{A}_F$ is precisely $A(D) \cap F$. -/
lemma rrSpaceAdele_map_eq (D : P → ℤ) :
    Submodule.map (diagonalLinearMap (F := F) (P := P) (O := O) k)
      (rrSpaceAdele (F := F) (O := O) k D) =
    adeleSpace (F := F) (O := O) k D ⊓ principalAdeles (F := F) (P := P) (O := O) k := by
  ext x
  simp only [Submodule.mem_map, rrSpaceAdele, Submodule.mem_comap, Submodule.mem_inf,
    principalAdeles, LinearMap.mem_range]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨hf, ⟨f, rfl⟩⟩
  · rintro ⟨hx, f, rfl⟩
    exact ⟨f, hx, rfl⟩

/-- $A(D) \cap F$ is finite-dimensional, as image of the finite-dimensional
$L(D)$ under the injective diagonal embedding. -/
lemma LF_subspace_finiteDimensional [Nonempty P] (D : P →₀ ℤ) :
    FiniteDimensional k
      ↥(adeleSpace (F := F) (O := O) k (D : P → ℤ) ⊓
        principalAdeles (F := F) (P := P) (O := O) k) := by
  haveI := rrSpaceAdele_finiteDimensional (F := F) (O := O) k D
  rw [← rrSpaceAdele_map_eq k (D : P → ℤ)]
  exact FiniteDimensional.instSubtypeMemSubmoduleMap k (diagonalLinearMap (F := F) (P := P) (O := O) k) _

/-- Dimension equality: $\dim_k (A(D) \cap F) = \dim_k L(D)$, since the
diagonal embedding restricts to a $k$-linear isomorphism. -/
lemma LF_subspace_finrank [Nonempty P] (D : P →₀ ℤ) :
    Module.finrank k
      ↥(adeleSpace (F := F) (O := O) k (D : P → ℤ) ⊓
        principalAdeles (F := F) (P := P) (O := O) k) =
    Module.finrank k (rrSpaceAdele (F := F) (O := O) k (D : P → ℤ)) := by
  haveI := rrSpaceAdele_finiteDimensional (F := F) (O := O) k D
  rw [← rrSpaceAdele_map_eq k (D : P → ℤ)]
  exact (Submodule.equivMapOfInjective _ (diagonalLinearMap_injective k) _).finrank_eq.symm

/-- The number $\ell(D) = \dim_k L(D)$, the $k$-dimension of the Riemann-Roch
space attached to $D$. -/
noncomputable def ellD (D : P →₀ ℤ) : ℕ :=
  Module.finrank k (rrSpaceAdele (F := F) (O := O) k (D : P → ℤ))

/-- For $A \le B$, the quotient $(A(B) \cap F) / (A(A) \cap F)$ is
finite-dimensional over $k$ (with the trivial case when $P$ is empty handled
separately). -/
lemma lemma_22_9_fd_LF_quotient (A B : P →₀ ℤ) (hAB : ∀ p, A p ≤ B p) :
    FiniteDimensional k
      (↥(adeleSpace (F := F) (O := O) k (B : P → ℤ) ⊓ principalAdeles (F := F) (P := P) (O := O) k) ⧸
        Submodule.comap
          (adeleSpace (F := F) (O := O) k (B : P → ℤ) ⊓ principalAdeles (F := F) (P := P) (O := O) k).subtype
          (adeleSpace (F := F) (O := O) k (A : P → ℤ) ⊓ principalAdeles (F := F) (P := P) (O := O) k)) := by
  by_cases hP : Nonempty P
  · haveI := hP
    haveI := LF_subspace_finiteDimensional (F := F) (O := O) k B
    exact inferInstance
  ·
    haveI : IsEmpty P := not_nonempty_iff.mp hP
    have h_eq : adeleSpace (F := F) (O := O) k (B : P → ℤ) ⊓
        principalAdeles (F := F) (P := P) (O := O) k =
      principalAdeles (F := F) (P := P) (O := O) k := by
      ext x
      simp only [Submodule.mem_inf]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨fun p => (IsEmpty.false p).elim, h⟩⟩
    have h_eq_A : adeleSpace (F := F) (O := O) k (A : P → ℤ) ⊓
        principalAdeles (F := F) (P := P) (O := O) k =
      principalAdeles (F := F) (P := P) (O := O) k := by
      ext x
      simp only [Submodule.mem_inf]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨fun p => (IsEmpty.false p).elim, h⟩⟩
    rw [h_eq, h_eq_A]
    have : Submodule.comap (principalAdeles (F := F) (P := P) (O := O) k).subtype
        (principalAdeles (F := F) (P := P) (O := O) k) = ⊤ :=
      Submodule.comap_subtype_self _
    rw [this]
    exact inferInstance

/-- Dimension of the LF-quotient: for $A \le B$,
$$\dim_k \big((A(B) \cap F) / (A(A) \cap F)\big) = \ell(B) - \ell(A).$$ -/
lemma lemma_22_9_finrank_LF_quotient (A B : P →₀ ℤ) (hAB : ∀ p, A p ≤ B p) :
    (Module.finrank k
      (↥(adeleSpace (F := F) (O := O) k (B : P → ℤ) ⊓ principalAdeles (F := F) (P := P) (O := O) k) ⧸
        Submodule.comap
          (adeleSpace (F := F) (O := O) k (B : P → ℤ) ⊓ principalAdeles (F := F) (P := P) (O := O) k).subtype
          (adeleSpace (F := F) (O := O) k (A : P → ℤ) ⊓ principalAdeles (F := F) (P := P) (O := O) k)) : ℤ) =
    (ellD (F := F) (O := O) k B : ℤ) - (ellD (F := F) (O := O) k A : ℤ) := by
  by_cases hP : Nonempty P
  · haveI := hP
    haveI := LF_subspace_finiteDimensional (F := F) (O := O) k B

    have h_rn := Submodule.finrank_quotient_add_finrank
      (Submodule.comap
        (adeleSpace (F := F) (O := O) k (B : P → ℤ) ⊓
          principalAdeles (F := F) (P := P) (O := O) k).subtype
        (adeleSpace (F := F) (O := O) k (A : P → ℤ) ⊓
          principalAdeles (F := F) (P := P) (O := O) k))

    have h_le : adeleSpace (F := F) (O := O) k (A : P → ℤ) ⊓
          principalAdeles (F := F) (P := P) (O := O) k ≤
        adeleSpace (F := F) (O := O) k (B : P → ℤ) ⊓
          principalAdeles (F := F) (P := P) (O := O) k :=
      inf_le_inf_right _ (adeleSpace_mono k hAB)
    have h_comap_rank : Module.finrank k
        ↥(Submodule.comap
          (adeleSpace (F := F) (O := O) k (B : P → ℤ) ⊓
            principalAdeles (F := F) (P := P) (O := O) k).subtype
          (adeleSpace (F := F) (O := O) k (A : P → ℤ) ⊓
            principalAdeles (F := F) (P := P) (O := O) k)) =
        Module.finrank k
          ↥(adeleSpace (F := F) (O := O) k (A : P → ℤ) ⊓
            principalAdeles (F := F) (P := P) (O := O) k) := by
      exact (Submodule.comapSubtypeEquivOfLe h_le).finrank_eq
    rw [h_comap_rank, LF_subspace_finrank k B, LF_subspace_finrank k A] at h_rn
    simp only [ellD]
    push_cast
    linarith
  ·
    haveI : IsEmpty P := not_nonempty_iff.mp hP
    have h_eq_B : adeleSpace (F := F) (O := O) k (B : P → ℤ) ⊓
        principalAdeles (F := F) (P := P) (O := O) k =
      principalAdeles (F := F) (P := P) (O := O) k := by
      ext x; simp only [Submodule.mem_inf]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨fun p => (IsEmpty.false p).elim, h⟩⟩
    have h_eq_A : adeleSpace (F := F) (O := O) k (A : P → ℤ) ⊓
        principalAdeles (F := F) (P := P) (O := O) k =
      principalAdeles (F := F) (P := P) (O := O) k := by
      ext x; simp only [Submodule.mem_inf]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨fun p => (IsEmpty.false p).elim, h⟩⟩
    rw [h_eq_B, h_eq_A, Submodule.comap_subtype_self]
    have h_rrB : rrSpaceAdele (F := F) (O := O) k (B : P → ℤ) = ⊤ := by
      ext f; simp only [rrSpaceAdele, Submodule.mem_comap, Submodule.mem_top, iff_true]
      intro p; exact (IsEmpty.false p).elim
    have h_rrA : rrSpaceAdele (F := F) (O := O) k (A : P → ℤ) = ⊤ := by
      ext f; simp only [rrSpaceAdele, Submodule.mem_comap, Submodule.mem_top, iff_true]
      intro p; exact (IsEmpty.false p).elim
    simp only [ellD]
    rw [h_rrB, h_rrA]
    simp

/-- Modular-lattice / second-isomorphism dimension identity. For submodules
$A \le B$ and any $F$ of a module $M$, the dimension of
$(B + F)/(A + F)$ plus the dimension of $(B \cap F)/(A \cap F)$ equals the
dimension of $B/A$, and finite-dimensionality is inherited. -/
theorem finrank_sup_quotient_eq {R : Type*} [DivisionRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (A B F_sub : Submodule R M) (hAB : A ≤ B)
    [hFD : FiniteDimensional R (↥B ⧸ Submodule.comap B.subtype A)]
    [hFD_inf : FiniteDimensional R (↥(B ⊓ F_sub) ⧸
        Submodule.comap (B ⊓ F_sub).subtype (A ⊓ F_sub))] :
    FiniteDimensional R (↥(B ⊔ F_sub) ⧸ Submodule.comap (B ⊔ F_sub).subtype (A ⊔ F_sub)) ∧
    Module.finrank R (↥(B ⊔ F_sub) ⧸ Submodule.comap (B ⊔ F_sub).subtype (A ⊔ F_sub)) +
      Module.finrank R (↥(B ⊓ F_sub) ⧸ Submodule.comap (B ⊓ F_sub).subtype (A ⊓ F_sub)) =
    Module.finrank R (↥B ⧸ Submodule.comap B.subtype A) := by
  set T := A ⊔ (B ⊓ F_sub) with hT_def

  have hAT : A ≤ T := le_sup_left
  have hTB : T ≤ B := sup_le hAB inf_le_left

  have h_modular : B ⊓ (A ⊔ F_sub) = T := by
    rw [sup_comm (a := A) (b := F_sub)]
    rw [← inf_sup_assoc_of_le F_sub hAB]
    rw [sup_comm]

  have hBsup : B ⊔ (A ⊔ F_sub) = B ⊔ F_sub := by
    rw [← sup_assoc, sup_eq_left.mpr hAB]

  have hABF_inf : A ⊓ (B ⊓ F_sub) = A ⊓ F_sub := by
    rw [← inf_assoc, inf_eq_left.mpr hAB]


  have e_2nd_BF := LinearMap.quotientInfEquivSupQuotient (B ⊓ F_sub) A


  have h_comap_eq_inf : Submodule.comap (B ⊓ F_sub).subtype (B ⊓ F_sub) ⊓
      Submodule.comap (B ⊓ F_sub).subtype A =
    Submodule.comap (B ⊓ F_sub).subtype (A ⊓ F_sub) := by
    rw [Submodule.comap_subtype_self, top_inf_eq]
    ext ⟨x, hx⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_inf]
    exact ⟨fun h => ⟨h, hx.2⟩, fun ⟨h, _⟩ => h⟩


  have e_TA : (↥(B ⊓ F_sub) ⧸ Submodule.comap (B ⊓ F_sub).subtype (A ⊓ F_sub)) ≃ₗ[R]
      (↥((B ⊓ F_sub) ⊔ A) ⧸ Submodule.comap ((B ⊓ F_sub) ⊔ A).subtype A) := by
    rw [← h_comap_eq_inf]; exact e_2nd_BF

  have hTA_comm : (B ⊓ F_sub) ⊔ A = T := sup_comm (a := B ⊓ F_sub) (b := A)

  haveI : FiniteDimensional R (↥T ⧸ Submodule.comap T.subtype A) := by
    rw [← hTA_comm]
    exact Module.Finite.equiv e_TA


  have e_2nd_B := LinearMap.quotientInfEquivSupQuotient B (A ⊔ F_sub)

  have h_comap_eq_T : Submodule.comap B.subtype B ⊓ Submodule.comap B.subtype (A ⊔ F_sub) =
      Submodule.comap B.subtype T := by
    rw [Submodule.comap_subtype_self, top_inf_eq]
    ext ⟨x, hx⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply]
    rw [← h_modular]
    exact ⟨fun h => ⟨hx, h⟩, fun ⟨_, h⟩ => h⟩

  have e_BT : (↥B ⧸ Submodule.comap B.subtype T) ≃ₗ[R]
      (↥(B ⊔ F_sub) ⧸ Submodule.comap (B ⊔ F_sub).subtype (A ⊔ F_sub)) := by
    rw [← h_comap_eq_T, ← hBsup]; exact e_2nd_B


  haveI : FiniteDimensional R (↥B ⧸ Submodule.comap B.subtype T) := by


    have h_le : Submodule.comap B.subtype A ≤ Submodule.comap B.subtype T :=
      Submodule.comap_mono hAT
    let f : (↥B ⧸ Submodule.comap B.subtype A) →ₗ[R]
        (↥B ⧸ Submodule.comap B.subtype T) :=
      (Submodule.comap B.subtype A).liftQ
        (Submodule.comap B.subtype T).mkQ
        (fun x hx => by
          simp only [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact h_le hx)
    have hf_surj : Function.Surjective f := by
      intro x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      refine ⟨Submodule.Quotient.mk y, ?_⟩
      simp only [f, Submodule.liftQ_apply, Submodule.mkQ_apply]
    exact Module.Finite.of_surjective f hf_surj

  haveI : FiniteDimensional R (↥(B ⊔ F_sub) ⧸ Submodule.comap (B ⊔ F_sub).subtype (A ⊔ F_sub)) :=
    Module.Finite.equiv e_BT

  have h_chain := finrank_comap_chain A T B hAT hTB
  obtain ⟨_, h_chain_eq⟩ := h_chain

  have hd_BT : Module.finrank R (↥B ⧸ Submodule.comap B.subtype T) =
    Module.finrank R (↥(B ⊔ F_sub) ⧸ Submodule.comap (B ⊔ F_sub).subtype (A ⊔ F_sub)) :=
    LinearEquiv.finrank_eq e_BT
  have hd_TA : Module.finrank R (↥T ⧸ Submodule.comap T.subtype A) =
    Module.finrank R (↥(B ⊓ F_sub) ⧸ Submodule.comap (B ⊓ F_sub).subtype (A ⊓ F_sub)) := by
    rw [← hTA_comm]; exact (LinearEquiv.finrank_eq e_TA).symm
  exact ⟨inferInstance, by omega⟩

/-- Additivity of divisor degree: $\deg(A + B) = \deg A + \deg B$. -/
lemma adeleDivisorDeg_add (A B : P →₀ ℤ) :
    adeleDivisorDeg (F := F) (k := k) (O := O) (A + B) =
    adeleDivisorDeg (F := F) (k := k) (O := O) A +
    adeleDivisorDeg (F := F) (k := k) (O := O) B := by
  simp only [adeleDivisorDeg]
  rw [Finsupp.sum_add_index (fun p => by simp) (fun p _ a b => by ring)]

/-- Behavior of divisor degree under subtraction:
$\deg(B - A) = \deg B - \deg A$. -/
lemma adeleDivisorDeg_sub (A B : P →₀ ℤ) :
    adeleDivisorDeg (F := F) (k := k) (O := O) (B - A) =
    adeleDivisorDeg (F := F) (k := k) (O := O) B -
    adeleDivisorDeg (F := F) (k := k) (O := O) A := by
  rw [sub_eq_add_neg, adeleDivisorDeg_add]
  congr 1
  simp only [adeleDivisorDeg]
  rw [Finsupp.sum_neg_index (fun p => by simp)]
  simp only [Finsupp.sum, neg_mul]
  exact Finset.sum_neg_distrib _

/-- The *Riemann defect* attached to a divisor $D$:
$\delta(D) = \deg D + 1 - \ell(D)$, whose constant value (over varying $D$) is
the genus $g$ in the Riemann-Roch theorem. -/
noncomputable def riemannDefect (D : P →₀ ℤ) : ℤ :=
  adeleDivisorDeg (F := F) (k := k) (O := O) D + 1 -
    (ellD (F := F) (O := O) k D : ℤ)

/-- Lemma 22.10. For divisors $A \le B$, the quotient
$(A(B) + F) / (A(A) + F)$ is finite-dimensional over $k$ and its dimension is
$\delta(B) - \delta(A)$, the difference of Riemann defects. Combines Lemmas
22.8 and 22.9 via the modular-lattice identity. -/
theorem AF_subspace_dim (A B : P →₀ ℤ) (hAB : ∀ p, A p ≤ B p) :
    FiniteDimensional k
      (↥(AF_subspace (F := F) (O := O) k (B : P → ℤ)) ⧸
        Submodule.comap
          (AF_subspace (F := F) (O := O) k (B : P → ℤ)).subtype
          (AF_subspace (F := F) (O := O) k (A : P → ℤ))) ∧
    (Module.finrank k
      (↥(AF_subspace (F := F) (O := O) k (B : P → ℤ)) ⧸
        Submodule.comap
          (AF_subspace (F := F) (O := O) k (B : P → ℤ)).subtype
          (AF_subspace (F := F) (O := O) k (A : P → ℤ))) : ℤ) =
    riemannDefect (F := F) (O := O) k B - riemannDefect (F := F) (O := O) k A := by

  have h228 := adeleSpace_quotient_finrank_eq (F := F) (O := O) k A B hAB
  obtain ⟨hFD_BA, hrank_BA⟩ := h228
  haveI := hFD_BA

  haveI := lemma_22_9_fd_LF_quotient (F := F) (O := O) k A B hAB
  have h_LF := lemma_22_9_finrank_LF_quotient (F := F) (O := O) k A B hAB

  set Asub := adeleSpace (F := F) (O := O) k (A : P → ℤ) with hAsub_def
  set Bsub := adeleSpace (F := F) (O := O) k (B : P → ℤ) with hBsub_def
  set Fsub := principalAdeles (F := F) (P := P) (O := O) k with hFsub_def
  have hAB_sub : Asub ≤ Bsub := adeleSpace_mono k hAB
  have h_lattice := finrank_sup_quotient_eq Asub Bsub Fsub hAB_sub
  obtain ⟨hFD_sup, h_lattice_eq⟩ := h_lattice
  refine ⟨hFD_sup, ?_⟩


  have h_deg_sub := adeleDivisorDeg_sub (F := F) (O := O) k A B
  rw [h_deg_sub] at hrank_BA
  simp only [riemannDefect]
  linarith [hrank_BA, h_LF]

end Lemma22_9
