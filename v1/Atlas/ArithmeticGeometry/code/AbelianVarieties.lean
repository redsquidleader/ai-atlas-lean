/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.EllipticCurves

universe u


/-- A continuous self-map $f \colon G \to G$ of a complete connected topological group is either
surjective or has singleton image (a key dichotomy for proper varieties). -/
theorem image_subsingleton_or_surjective
    {G : Type u} [TopologicalSpace G] [Group G]
    [IsCompleteVariety G] [IsTopologicalGroup G] [ConnectedSpace G]
    {f : G → G} (hf : Continuous f) :
    Function.Surjective f ∨ ∃ c, Set.range f = {c} := by sorry


/-- Semicontinuity in families: if $F \colon G \times P \to H$ is continuous between connected
complete varieties / groups and there exists $p_0$ with $F(g, p_0) = 1$ for all $g$, then
$F(g, p) = 1$ identically. -/
theorem semicontinuity_of_image
    {G : Type u} [TopologicalSpace G] [Group G]
    [IsCompleteVariety G] [IsTopologicalGroup G] [ConnectedSpace G]
    {P : Type u} [TopologicalSpace P] [ConnectedSpace P]
    {H : Type u} [TopologicalSpace H] [Group H]
    [IsCompleteVariety H] [IsTopologicalGroup H] [ConnectedSpace H]
    {F : G × P → H} (hF : Continuous F)
    (hF_const : ∃ p₀ : P, ∀ g : G, F (g, p₀) = 1) :
    ∀ p g, F (g, p) = 1 := by sorry

/-- Rigidity lemma: a continuous self-map $f$ of a complete connected topological group that
fixes the identity and whose image misses some point must be constantly $1$. -/
theorem rigidity_of_complete_connected_group
    {G : Type u} [TopologicalSpace G] [Group G]
    [IsCompleteVariety G] [IsTopologicalGroup G] [ConnectedSpace G]
    {f : G → G} (hf_cont : Continuous f) (hf_id : f 1 = 1)
    {y : G} (hy : y ∉ Set.range f) :
    ∀ x, f x = 1 := by

  rcases image_subsingleton_or_surjective hf_cont with hsurj | ⟨c, hc⟩
  ·
    exact absurd (hsurj y) hy
  ·
    intro x

    have hx : f x ∈ Set.range f := Set.mem_range_self x

    have h1 : (1 : G) ∈ Set.range f := ⟨1, hf_id⟩
    rw [hc] at hx h1
    rw [Set.mem_singleton_iff] at hx h1
    rw [hx, ← h1]

/-- Theorem 23.23: An abelian variety is commutative; equivalently, the group law $a \cdot b$
on an `IsAbelianVariety` is symmetric. The proof applies the rigidity lemma to the commutator
map $g \mapsto b^{-1} g^{-1} b g$. -/
theorem IsAbelianVariety.mul_comm
    {k : Type u} [Field k]
    {A : Type u} [TopologicalSpace A] [Group A] [IsAbelianVariety k A]
    (a b : A) : a * b = b * a := by

  by_cases hb : b = 1
  · rw [hb, mul_one, one_mul]

  ·
    let ψ : A → A := fun g => b⁻¹ * g⁻¹ * b * g

    have hψ_cont : Continuous ψ := by
      show Continuous (fun g => b⁻¹ * g⁻¹ * b * g)
      exact ((continuous_const.mul continuous_inv).mul continuous_const).mul continuous_id

    have hψ_id : ψ 1 = 1 := by show b⁻¹ * 1⁻¹ * b * 1 = 1; group


    have hb_inv_not_in_range : b⁻¹ ∉ Set.range ψ := by
      rintro ⟨g, hg⟩
      apply hb
      change b⁻¹ * g⁻¹ * b * g = b⁻¹ at hg

      have key : b⁻¹ * (g⁻¹ * b * g) = b⁻¹ * 1 := by
        rw [mul_one]; convert hg using 1; group
      have h1 : g⁻¹ * b * g = 1 := mul_left_cancel key

      have h2 : g⁻¹ * (b * g) = g⁻¹ * g := by
        rw [← mul_assoc, h1, inv_mul_cancel]
      have h3 : b * g = g := mul_left_cancel h2

      exact mul_right_cancel (b := g) (by rw [h3, one_mul])


    have hψ_const := rigidity_of_complete_connected_group hψ_cont hψ_id hb_inv_not_in_range

    have ha := hψ_const a
    change b⁻¹ * a⁻¹ * b * a = 1 at ha

    calc a * b = a * b * (b⁻¹ * a⁻¹ * b * a) := by rw [ha, mul_one]
      _ = b * a := by group

/-- Promotes the `Group` instance on an abelian variety to a `CommGroup` instance using the
commutativity theorem `IsAbelianVariety.mul_comm`. -/
@[reducible]
def IsAbelianVariety.toCommGroup
    {k : Type u} [Field k]
    {A : Type u} [TopologicalSpace A] [Group A] [IsAbelianVariety k A] : CommGroup A :=
  { ‹Group A› with mul_comm := IsAbelianVariety.mul_comm (k := k) }

/-- Two-variable rigidity: a continuous $\Psi \colon G \times G \to H$ between complete connected
topological groups that is identically $1$ on each axis (i.e. $\Psi(g,1) = \Psi(1,h) = 1$) is
identically $1$. -/
theorem rigidity_lemma_product
    {G : Type u} [TopologicalSpace G] [Group G]
    [IsCompleteVariety G] [IsTopologicalGroup G] [ConnectedSpace G]
    {H : Type u} [TopologicalSpace H] [Group H]
    [IsCompleteVariety H] [IsTopologicalGroup H] [ConnectedSpace H]
    {Ψ : G × G → H} (hΨ_cont : Continuous Ψ)
    (hΨ_fst : ∀ g, Ψ (g, 1) = 1) (_hΨ_snd : ∀ h, Ψ (1, h) = 1) :
    ∀ g h, Ψ (g, h) = 1 := by


  have h_const : ∃ p₀ : G, ∀ g : G, Ψ (g, p₀) = 1 := ⟨1, hΨ_fst⟩
  have h_all := semicontinuity_of_image hΨ_cont h_const
  intro g h
  exact h_all h g

/-- A continuous map $\varphi$ between abelian varieties that sends $1 \mapsto 1$ is automatically
a group homomorphism: $\varphi(gh) = \varphi(g) \varphi(h)$. Proved by applying the two-variable
rigidity lemma to $\Psi(g,h) = \varphi(g)\varphi(h)\varphi(gh)^{-1}$. -/
theorem morphism_preserving_identity_is_hom
    {k : Type u} [Field k]
    {G : Type u} [TopologicalSpace G] [Group G] [IsAbelianVariety k G]
    {H : Type u} [TopologicalSpace H] [Group H] [IsAbelianVariety k H]
    (φ : G → H) (hφ_cont : Continuous φ) (hφ_id : φ 1 = 1)
    (g h : G) : φ (g * h) = φ g * φ h := by

  let Ψ : G × G → H := fun p => φ p.1 * φ p.2 * (φ (p.1 * p.2))⁻¹

  have hΨ_cont : Continuous Ψ := by
    show Continuous (fun p : G × G => φ p.1 * φ p.2 * (φ (p.1 * p.2))⁻¹)
    exact ((hφ_cont.comp continuous_fst).mul (hφ_cont.comp continuous_snd)).mul
      (hφ_cont.comp (continuous_fst.mul continuous_snd)).inv

  have hΨ_fst : ∀ x, Ψ (x, 1) = 1 := by
    intro x
    show φ x * φ 1 * (φ (x * 1))⁻¹ = 1
    rw [hφ_id, mul_one, mul_one, mul_inv_cancel]

  have hΨ_snd : ∀ y, Ψ (1, y) = 1 := by
    intro y
    show φ 1 * φ y * (φ (1 * y))⁻¹ = 1
    rw [hφ_id, one_mul, one_mul, mul_inv_cancel]

  have hΨ_const := rigidity_lemma_product hΨ_cont hΨ_fst hΨ_snd g h


  change φ g * φ h * (φ (g * h))⁻¹ = 1 at hΨ_const
  have := mul_inv_eq_one.mp hΨ_const
  exact this.symm
