/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.BNPair.Generalized.TypePreserving
import Atlas.Buildings.code.CoxeterGroup.ParabolicInjective

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

variable {B_idx : Type*} [Fintype B_idx] [DecidableEq B_idx]

namespace GeneralizedBNPair

variable {Gt : Type*} [Group Gt] {M : CoxeterMatrix B_idx}
variable (gbp : GeneralizedBNPair Gt M)

/-- The Borel subgroup $B \leq G$ pushed forward to $\tilde G$ along the inclusion
$G \hookrightarrow \tilde G$. -/
def Blifted : Subgroup Gt :=
  gbp.strictBNPair.B.map gbp.G.subtype

/-- The subgroup $N \leq G$ pushed forward to $\tilde G$. -/
def Nlifted : Subgroup Gt :=
  gbp.strictBNPair.N.map gbp.G.subtype

/-- The torus $T = B \cap N \leq G$ pushed forward to $\tilde G$. -/
def Tlifted : Subgroup Gt :=
  gbp.strictBNPair.T.map gbp.G.subtype

/-- The intersection $\tilde T \cap G$ inside $\tilde G$; by the axioms this coincides
with the lifted $T$. -/
def TtInterG : Subgroup Gt :=
  gbp.Tt ⊓ gbp.G

/-- The subgroup $\tilde T \cap G$ pulled back into $\tilde T$, viewed as a subgroup
of $\tilde T$. Quotienting by this yields the twist group. -/
def twistSubgroup : Subgroup gbp.Tt :=
  (gbp.Tt ⊓ gbp.G).subgroupOf gbp.Tt

/-- The **twist group** $\tilde T / (\tilde T \cap G)$, finite by axiom, which measures
the non-type-preserving part of $\tilde G$. -/
def TwistGroup := gbp.Tt ⧸ gbp.twistSubgroup

/-- An element $t \in \tilde T$ that acts trivially on types of the base apartment
lies in $G$. Specialization of the building uniqueness lemma to $\tilde T \leq \tilde B$. -/
theorem trivial_action_in_G
    (t : Gt) (ht : t ∈ gbp.Tt)
    (htrivial : ∀ (s : B_idx) (n : gbp.strictBNPair.N),
      gbp.strictBNPair.π n = M.toCoxeterSystem.simple s →
      ∃ (n' : gbp.strictBNPair.N),
        gbp.strictBNPair.π n' = M.toCoxeterSystem.simple s ∧
        ((n' : gbp.G) : Gt) = t * ((n : gbp.G) : Gt) * t⁻¹) :
    t ∈ gbp.G :=
  gbp.building_uniqueness_lemma t (gbp.Tt_le_Bt ht) htrivial

/-- **Injectivity of the type-permutation action of $\tilde T$.** If two elements
$t_1, t_2 \in \tilde T$ induce the same permutation $\sigma \in \mathrm{Sym}(S)$ on
the set of simple reflections (so their conjugation actions on $N$-lifts of simple
reflections agree at the level of $\pi$), then $t_1^{-1} t_2 \in G$.
Equivalently, the homomorphism $\tilde T / (\tilde T \cap G) \to \mathrm{Sym}(S)$
given by the type permutation is injective. -/
theorem Tt_perm_injective
    {B_idx : Type*} [Fintype B_idx] [DecidableEq B_idx]
    {Gt : Type*} [Group Gt] {M : CoxeterMatrix B_idx}
    (gbp : GeneralizedBNPair Gt M)
    (t₁ t₂ : Gt) (ht₁ : t₁ ∈ gbp.Tt) (ht₂ : t₂ ∈ gbp.Tt)
    (hsame : ∀ (s : B_idx) (n : gbp.strictBNPair.N),
      gbp.strictBNPair.π n = M.toCoxeterSystem.simple s →
      ∃ (n₁' n₂' : gbp.strictBNPair.N),
        gbp.strictBNPair.π n₁' = gbp.strictBNPair.π n₂' ∧
        ((n₁' : gbp.G) : Gt) = t₁ * ((n : gbp.G) : Gt) * t₁⁻¹ ∧
        ((n₂' : gbp.G) : Gt) = t₂ * ((n : gbp.G) : Gt) * t₂⁻¹) :
    t₁⁻¹ * t₂ ∈ gbp.G := by

  have ht12 : t₁⁻¹ * t₂ ∈ gbp.Tt := gbp.Tt.mul_mem (gbp.Tt.inv_mem ht₁) ht₂
  have ht1inv : t₁⁻¹ ∈ gbp.Tt := gbp.Tt.inv_mem ht₁

  obtain ⟨σ₁, hσ₁⟩ := gbp.Tt_stabilizes_S t₁ ht₁
  obtain ⟨σ₂, hσ₂⟩ := gbp.Tt_stabilizes_S t₂ ht₂
  obtain ⟨τ, hτ⟩ := gbp.Tt_stabilizes_S t₁⁻¹ ht1inv

  have hσ_eq : σ₁ = σ₂ := by
    ext s

    obtain ⟨n₀, hn₀⟩ := gbp.strictBNPair.π_surj (M.toCoxeterSystem.simple s)

    obtain ⟨m₁, hm₁_π, hm₁_conj⟩ := hσ₁ s n₀ hn₀

    obtain ⟨m₂, hm₂_π, hm₂_conj⟩ := hσ₂ s n₀ hn₀

    obtain ⟨n₁', n₂', hπ_eq, hn₁'_conj, hn₂'_conj⟩ := hsame s n₀ hn₀

    have hm₁_eq_n₁' : m₁ = n₁' := by
      have : ((m₁ : gbp.G) : Gt) = ((n₁' : gbp.G) : Gt) := by
        rw [hm₁_conj, hn₁'_conj]
      exact Subtype.val_injective (Subtype.val_injective this)

    have hm₂_eq_n₂' : m₂ = n₂' := by
      have : ((m₂ : gbp.G) : Gt) = ((n₂' : gbp.G) : Gt) := by
        rw [hm₂_conj, hn₂'_conj]
      exact Subtype.val_injective (Subtype.val_injective this)

    have : gbp.strictBNPair.π m₁ = gbp.strictBNPair.π m₂ := by
      rw [hm₁_eq_n₁', hm₂_eq_n₂']; exact hπ_eq

    rw [hm₁_π, hm₂_π] at this
    exact CoxeterSystem.simple_injective M.toCoxeterSystem this

  have hτσ : ∀ s, τ (σ₁ s) = s := by
    intro s
    obtain ⟨n₀, hn₀⟩ := gbp.strictBNPair.π_surj (M.toCoxeterSystem.simple s)

    obtain ⟨m₁, hm₁_π, hm₁_conj⟩ := hσ₁ s n₀ hn₀

    obtain ⟨m₃, hm₃_π, hm₃_conj⟩ := hτ (σ₁ s) m₁ hm₁_π

    have hm₃_eq_n₀ : ((m₃ : gbp.G) : Gt) = ((n₀ : gbp.G) : Gt) := by
      rw [hm₃_conj, hm₁_conj]
      group

    have : m₃ = n₀ := Subtype.val_injective (Subtype.val_injective hm₃_eq_n₀)

    rw [this, hn₀] at hm₃_π
    exact (CoxeterSystem.simple_injective M.toCoxeterSystem hm₃_π).symm

  apply trivial_action_in_G gbp (t₁⁻¹ * t₂) ht12

  intro s n hn

  obtain ⟨n₂', hn₂'_π, hn₂'_conj⟩ := hσ₂ s n hn

  obtain ⟨n₃, hn₃_π, hn₃_conj⟩ := hτ (σ₂ s) n₂' hn₂'_π

  refine ⟨n₃, ?_, ?_⟩
  ·

    rw [hn₃_π, ← hσ_eq, hτσ]
  ·
    rw [hn₃_conj, hn₂'_conj]
    group

/-- The "twisted" Bruhat cell $\sigma \cdot B \cdot w \cdot B \subseteq \tilde G$
for $\sigma \in \tilde T$ and $w \in W$: elements that can be written as
$\sigma \cdot b_1 \cdot n \cdot b_2$ with $b_i \in B$ (lifted) and $n$ an $N$-lift of $w$. -/
def bruhatCellGt (σ : Gt) (w : M.Group) : Set Gt :=
  { g : Gt | ∃ (b₁ : Gt) (_ : b₁ ∈ gbp.Blifted)
               (n : Gt) (_ : n ∈ gbp.Nlifted)
               (b₂ : Gt) (_ : b₂ ∈ gbp.Blifted),
    (∃ (n' : gbp.strictBNPair.N),
      gbp.strictBNPair.π n' = w ∧ (n' : Gt) = n) ∧
    g = σ * b₁ * n * b₂ }

/-- The left coset $\sigma B = \{\sigma b : b \in B\} \subseteq \tilde G$. -/
def sigmaB (σ : Gt) : Set Gt :=
  { g : Gt | ∃ (b : Gt) (_ : b ∈ gbp.Blifted), g = σ * b }

/-- The right coset $B\sigma = \{b\sigma : b \in B\} \subseteq \tilde G$. -/
def Bsigma (σ : Gt) : Set Gt :=
  { g : Gt | ∃ (b : Gt) (_ : b ∈ gbp.Blifted), g = b * σ }

/-- The lifted torus is contained in the lifted Borel: $T \leq B$ pushed forward. -/
theorem Tlifted_le_Blifted : gbp.Tlifted ≤ gbp.Blifted := by
  unfold Tlifted Blifted
  exact Subgroup.map_mono (gbp.strictBNPair.T_eq ▸ inf_le_left)

/-- The lifted torus is contained in the lifted $N$: $T \leq N$ pushed forward. -/
theorem Tlifted_le_Nlifted : gbp.Tlifted ≤ gbp.Nlifted := by
  unfold Tlifted Nlifted
  exact Subgroup.map_mono (gbp.strictBNPair.T_eq ▸ inf_le_right)

/-- The lifted torus $T$ is contained in the enlarged torus $\tilde T$, since
$T \leq B \leq \tilde B$ and $T \leq N \leq \tilde N$. -/
theorem T_le_Tt :
    gbp.Tlifted ≤ gbp.Tt := by
  rw [gbp.Tt_eq]
  exact le_inf
    (le_trans gbp.Tlifted_le_Blifted gbp.B_le_Bt)
    (le_trans gbp.Tlifted_le_Nlifted gbp.N_le_Nt)

end GeneralizedBNPair
