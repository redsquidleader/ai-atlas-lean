/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Reflection.AffineWeylGroups

open scoped InnerProductSpace
open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace AffineReflectionGroup

variable (W : AffineReflectionGroup E)

/-- If $w \in W$ maps every point of chamber $C$ into chamber $D$, then $w$ in fact gives a
**bijection** $C \leftrightarrow D$: the implication promotes to an iff. This relies on maximality
of chambers as connected components of the complement of the hyperplane arrangement. -/
lemma group_maps_chamber_surj
    (C D : W.arrangement.Chamber)
    (w : E ≃ᵃⁱ[ℝ] E) (hw : w ∈ W.group)
    (h_maps : ∀ x ∈ C.set, w x ∈ D.set) :
    ∀ y : E, y ∈ C.set ↔ w y ∈ D.set := by

  have hC_sub : C.set ⊆ (w : E → E) ⁻¹' D.set := fun x hx => h_maps x hx

  have hpreimage_compl : (w : E → E) ⁻¹' D.set ⊆ W.arrangement.complement := by
    intro x hx
    have hwx_compl := D.subset_complement hx
    rw [HyperplaneArrangement.complement] at hwx_compl ⊢
    simp only [Set.mem_diff, Set.mem_univ, true_and] at hwx_compl ⊢
    intro hx_union
    apply hwx_compl
    rw [HyperplaneArrangement.unionSet] at hx_union ⊢
    simp only [Set.mem_iUnion] at hx_union ⊢
    obtain ⟨ξ, hξ_mem, hx_carrier⟩ := hx_union
    obtain ⟨ξ', hξ'_mem, hξ'_char⟩ := W.stable w hw ξ hξ_mem
    exact ⟨ξ', hξ'_mem, (hξ'_char x).mpr hx_carrier⟩

  have hpreimage_conn : IsConnected ((w : E → E) ⁻¹' D.set) := by
    rw [show (w : E → E) ⁻¹' D.set = w.symm '' D.set from by
      ext x; constructor
      · intro hx; exact ⟨w x, hx, w.symm_apply_apply x⟩
      · intro ⟨d, hd, hxd⟩; rw [← hxd]; show w (w.symm d) ∈ D.set; rwa [w.apply_symm_apply]]
    exact D.isConnected.image (w.symm : E → E) w.symm.continuous.continuousOn

  have hpreimage_sub_C : (w : E → E) ⁻¹' D.set ⊆ C.set :=
    C.is_maximal _ hpreimage_compl hpreimage_conn hC_sub

  intro y
  constructor
  · exact fun hy => h_maps y hy
  · exact fun hy => hpreimage_sub_C hy

/-- **Gallery connectivity**: any two chambers $C, D$ are connected by a gallery, i.e. a list of
reflections through walls such that the composition sends $D$ to $C$. Proved by induction on the
number of separating hyperplanes. -/
theorem gallery_connectivity_axiom
    (C D : W.arrangement.Chamber) :
    ∃ (reflections : List (E ≃ᵃⁱ[ℝ] E)),
      (∀ s ∈ reflections, s * s = 1 ∧
        ∃ η ∈ W.arrangement.hyperplanes, ∀ y ∈ η.carrier, s y = y) ∧
      (∀ y : E, y ∈ D.set ↔ reflections.prod y ∈ C.set) := by

  suffices h : ∀ (n : ℕ) (C D : W.arrangement.Chamber),
      (W.separatingHyperplanes C D).ncard = n →
      ∃ (reflections : List (E ≃ᵃⁱ[ℝ] E)),
        (∀ s ∈ reflections, s * s = 1 ∧
          ∃ η ∈ W.arrangement.hyperplanes, ∀ y ∈ η.carrier, s y = y) ∧
        (∀ y : E, y ∈ D.set ↔ reflections.prod y ∈ C.set) from
    h _ C D rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro C D hCD
  by_cases heq : C.set = D.set
  ·
    refine ⟨[], fun s hs => absurd hs (List.not_mem_nil), fun y => ?_⟩
    simp only [List.prod_nil, AffineIsometryEquiv.coe_one, id]
    exact ⟨fun h => heq ▸ h, fun h => heq.symm ▸ h⟩
  ·
    obtain ⟨s, hs_group, η, hη_mem, _hη_wall, hs_fix, hs_inv, D',
            hs_maps, h_fewer⟩ :=
      wall_separation_step W C D heq


    have hs_iff : ∀ y, y ∈ C.set ↔ s y ∈ D'.set :=
      group_maps_chamber_surj W C D' s hs_group hs_maps

    have hs_iff_rev : ∀ z, z ∈ D'.set ↔ s z ∈ C.set := by
      intro z
      have h := hs_iff (s z)


      have hss : s (s z) = z := by
        have : (s * s : E ≃ᵃⁱ[ℝ] E) z = (1 : E ≃ᵃⁱ[ℝ] E) z := by rw [hs_inv]
        simp only [AffineIsometryEquiv.coe_mul, Function.comp,
          AffineIsometryEquiv.coe_one, id] at this
        exact this
      rw [hss] at h
      exact h.symm

    have h_lt : (W.separatingHyperplanes D' D).ncard < n := by omega
    obtain ⟨refls', hrefls'_props, hrefls'_map⟩ := ih _ h_lt D' D rfl


    refine ⟨s :: refls', ?_, ?_⟩
    ·
      intro t ht
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact ⟨hs_inv, η, hη_mem, hs_fix⟩
      · exact hrefls'_props t ht
    ·
      intro y
      simp only [List.prod_cons, AffineIsometryEquiv.coe_mul, Function.comp]
      constructor
      · intro hy
        exact (hs_iff_rev _).mp ((hrefls'_map y).mp hy)
      · intro hy
        exact (hrefls'_map y).mpr ((hs_iff_rev _).mpr hy)

/-- A product of elements of a subgroup $G$ is in $G$. -/
lemma list_prod_mem_group (G : Subgroup (E ≃ᵃⁱ[ℝ] E))
    (l : List (E ≃ᵃⁱ[ℝ] E)) (hl : ∀ s ∈ l, s ∈ G) :
    l.prod ∈ G := by
  induction l with
  | nil => simp
  | cons s rest ih =>
    simp only [List.prod_cons]
    exact G.mul_mem (hl s List.mem_cons_self)
      (ih (fun t ht => hl t (List.mem_cons_of_mem s ht)))

/-- Any involution $s$ that fixes a hyperplane $\eta$ from the arrangement is the reflection in $\eta$
and hence is in $W$. -/
lemma involution_fixing_hyperplane_mem_group
    (s : E ≃ᵃⁱ[ℝ] E) (η : AffineHyperplane E)
    (hη : η ∈ W.arrangement.hyperplanes)
    (hs_inv : s * s = 1) (hs_fix : ∀ y ∈ η.carrier, s y = y) :
    s ∈ W.group := by
  by_cases hs_ne : s = 1
  ·
    subst hs_ne; exact W.group.one_mem
  ·
    obtain ⟨s', hs'_mem, hs'_fix, hs'_inv, hs'_ne⟩ := W.has_reflection η hη

    have heq : s = s' := reflection_unique s s' η hs_inv hs_fix hs'_inv hs'_fix hs_ne hs'_ne
    rw [heq]; exact hs'_mem

/-- **Transitivity of $W$ on alcoves**: for any two alcoves $C, D$ there exists $w \in W$ mapping
$D$ bijectively onto $C$. Built by composing a gallery of wall reflections from gallery connectivity. -/
theorem group_transitive_on_alcoves_aux
    (C D : W.Alcove) :
    ∃ w ∈ W.group, ∀ y : E, y ∈ D.set ↔ (w : E ≃ᵃⁱ[ℝ] E) y ∈ C.set := by

  obtain ⟨refls, hrefls_props, hrefls_map⟩ :=
    gallery_connectivity_axiom W C D

  have h_all_mem : ∀ s ∈ refls, s ∈ W.group := by
    intro s hs
    obtain ⟨hs_inv, η, hη_arr, hs_fix⟩ := hrefls_props s hs
    exact involution_fixing_hyperplane_mem_group W s η hη_arr hs_inv hs_fix

  exact ⟨refls.prod, list_prod_mem_group W.group refls h_all_mem, hrefls_map⟩

end AffineReflectionGroup
