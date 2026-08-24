/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.CategoryO

open scoped TensorProduct

noncomputable section

universe u

theorem textbook_axiom_internalHom_isCategoryO
    {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {V : Type u} [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V]
    (X : Type u) [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X) :
    IsCategoryO Δ rd (V →ₗ[R] X) := by
  sorry

theorem postcomp_surjective_of_free
    {R : Type u} [CommRing R]
    {V : Type u} [AddCommGroup V] [Module R V]
    [Module.Free R V]
    {X : Type u} [AddCommGroup X] [Module R X]
    {Y : Type u} [AddCommGroup Y] [Module R Y]
    (f : X →ₗ[R] Y)
    (hf : Function.Surjective f) :
    Function.Surjective (fun (φ : V →ₗ[R] X) => f.comp φ) := by
  intro ψ

  have : Module.Projective R V := Module.Projective.of_free
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property f ψ hf
  exact ⟨φ, by ext v; exact LinearMap.congr_fun hφ v⟩

theorem textbook_axiom_internalHom_categoryO_data
    {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {V : Type u} [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V] [Module.Free R V]
    (X : Type u) [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X) :
    IsCategoryO Δ rd (V →ₗ[R] X) ∧
      (∀ (Y : Type u) [AddCommGroup Y] [Module R Y]
        [LieRingModule 𝔤 Y] [LieModule R 𝔤 Y]
        (f : X →ₗ⁅R, 𝔤⁆ Y) (_ : Function.Surjective f),
        Function.Surjective (fun (φ : V →ₗ[R] X) => (f : X →ₗ[R] Y).comp φ)) := by
  refine ⟨textbook_axiom_internalHom_isCategoryO X hXO, ?_⟩
  intro Y _ _ _ _ f hf
  exact postcomp_surjective_of_free (f : X →ₗ[R] Y) hf

def lieModuleHomPostcomp
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {V : Type*} [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {N : Type*} [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (f : M →ₗ⁅R, 𝔤⁆ N) :
    (V →ₗ[R] M) →ₗ⁅R, 𝔤⁆ (V →ₗ[R] N) where
  toLinearMap :=
    { toFun := fun φ => (f : M →ₗ[R] N).comp φ
      map_add' := fun φ ψ => by ext; simp [LinearMap.add_apply]
      map_smul' := fun r φ => by ext; simp [LinearMap.smul_apply] }
  map_lie' := by
    intro x φ
    ext v
    simp only [LieHom.lie_apply, LinearMap.comp_apply,
      LieModuleHom.coe_toLinearMap]

    rw [map_sub]
    congr 1
    exact LieModuleHom.map_lie f x (φ v)

def lieModuleHomFlip
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {V : Type*} [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    {N : Type*} [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (ψ : V →ₗ⁅R, 𝔤⁆ (P →ₗ[R] N)) :
    P →ₗ⁅R, 𝔤⁆ (V →ₗ[R] N) where
  toLinearMap :=
    { toFun := fun p =>
        { toFun := fun v => ψ v p
          map_add' := fun v₁ v₂ => by simp [map_add, LinearMap.add_apply]
          map_smul' := fun r v => by simp [map_smul, LinearMap.smul_apply] }
      map_add' := fun p₁ p₂ => by ext v; simp [LinearMap.add_apply, map_add]
      map_smul' := fun r p => by ext v; simp [LinearMap.smul_apply, map_smul] }
  map_lie' := by
    intro x p
    ext v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LieHom.lie_apply]

    have h1 := LieModuleHom.map_lie ψ x v
    have h2 : (⁅x, (ψ v : P →ₗ[R] N)⁆ : P →ₗ[R] N) p = ⁅x, (ψ v) p⁆ - (ψ v) ⁅x, p⁆ :=
      LieHom.lie_apply (ψ v) x p
    have h3 : (ψ ⁅x, v⁆) p = ⁅x, (ψ v) p⁆ - (ψ v) ⁅x, p⁆ := by
      have := congr_arg (· p) h1
      dsimp at this; rw [this]
    rw [h3, sub_sub_cancel]

theorem textbook_axiom_tensorHom_adjunction_data
    {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {P : Type u} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    {V : Type u} [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V] [Module.Free R V]
    (M : Type u) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hMO : IsCategoryO Δ rd M)
    (N : Type u) [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (hNO : IsCategoryO Δ rd N)
    (f : M →ₗ⁅R, 𝔤⁆ N)
    (hf : Function.Surjective f)
    (g : TensorProduct R V P →ₗ⁅R, 𝔤⁆ N) :
    ∃ (W_M : Type u) (_ : AddCommGroup W_M) (_ : Module R W_M)
      (_ : LieRingModule 𝔤 W_M) (_ : LieModule R 𝔤 W_M)
      (hWMO : IsCategoryO Δ rd W_M)
      (W_N : Type u) (_ : AddCommGroup W_N) (_ : Module R W_N)
      (_ : LieRingModule 𝔤 W_N) (_ : LieModule R 𝔤 W_N)
      (hWNO : IsCategoryO Δ rd W_N)
      (W_f : W_M →ₗ⁅R, 𝔤⁆ W_N) (_ : Function.Surjective W_f)
      (g' : P →ₗ⁅R, 𝔤⁆ W_N),
      ∀ (h' : P →ₗ⁅R, 𝔤⁆ W_M), (∀ p, W_f (h' p) = g' p) →
        ∃ (h : TensorProduct R V P →ₗ⁅R, 𝔤⁆ M), ∀ x, f (h x) = g x := by

  obtain ⟨hMO', hM_surj⟩ := textbook_axiom_internalHom_categoryO_data (𝔤 := 𝔤) (V := V) M hMO
  obtain ⟨hNO', _⟩ := textbook_axiom_internalHom_categoryO_data (𝔤 := 𝔤) (V := V) N hNO

  let W_f_map := lieModuleHomPostcomp (V := V) f

  have hW_surj : Function.Surjective W_f_map := by
    intro φ
    obtain ⟨ψ, hψ⟩ := hM_surj N f hf φ
    exact ⟨ψ, by ext v; exact congr_arg (· v) hψ⟩

  let g_curried : V →ₗ⁅R, 𝔤⁆ (P →ₗ[R] N) :=
    (TensorProduct.LieModule.liftLie R 𝔤 V P N).symm g
  let g'_map : P →ₗ⁅R, 𝔤⁆ (V →ₗ[R] N) := lieModuleHomFlip g_curried
  refine ⟨V →ₗ[R] M, inferInstance, inferInstance, inferInstance, inferInstance, hMO',
          V →ₗ[R] N, inferInstance, inferInstance, inferInstance, inferInstance, hNO',
          W_f_map, hW_surj, g'_map, ?_⟩

  intro h' hh'


  let h'_curried : V →ₗ⁅R, 𝔤⁆ (P →ₗ[R] M) :=
    { toLinearMap :=
        { toFun := fun v =>
            { toFun := fun p => h' p v
              map_add' := fun p₁ p₂ => by simp [map_add, LinearMap.add_apply]
              map_smul' := fun r p => by simp [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
          map_add' := fun v₁ v₂ => by ext p; simp [LinearMap.add_apply]
          map_smul' := fun r v => by ext p; simp [LinearMap.smul_apply] }
      map_lie' := by
        intro x v; ext p
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LieHom.lie_apply]


        have h1 := LieModuleHom.map_lie h' x p
        have h2 : (⁅x, (h' p : V →ₗ[R] M)⁆ : V →ₗ[R] M) v = ⁅x, (h' p) v⁆ - (h' p) ⁅x, v⁆ :=
          LieHom.lie_apply (h' p) x v
        have h3 : (h' ⁅x, p⁆) v = ⁅x, (h' p) v⁆ - (h' p) ⁅x, v⁆ := by
          have := congr_arg (· v) h1
          dsimp at this; rw [this]
        rw [h3, sub_sub_cancel] }
  let h_map : TensorProduct R V P →ₗ⁅R, 𝔤⁆ M :=
    TensorProduct.LieModule.liftLie R 𝔤 V P M h'_curried
  refine ⟨h_map, ?_⟩

  intro x
  refine x.induction_on ?_ ?_ ?_
  · simp [map_zero]
  · intro v p


    show f (h_map (v ⊗ₜ[R] p)) = g (v ⊗ₜ[R] p)
    have h_eval : h_map (v ⊗ₜ[R] p) = h'_curried v p :=
      TensorProduct.LieModule.liftLie_apply (R := R) (L := 𝔤) (M := V) (N := P) (P := M) h'_curried v p
    rw [h_eval]


    change f ((h' p) v) = g (v ⊗ₜ[R] p)

    have key := hh' p


    have key_v : f ((h' p) v) = (g'_map p) v := by
      have := DFunLike.congr_fun key v
      simp only [W_f_map, lieModuleHomPostcomp, LieModuleHom.coe_mk, LinearMap.coe_mk,
        AddHom.coe_mk, LinearMap.comp_apply, LieModuleHom.coe_toLinearMap] at this
      exact this
    rw [key_v]


    show (lieModuleHomFlip g_curried p) v = g (v ⊗ₜ[R] p)
    simp only [lieModuleHomFlip, LieModuleHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]


    show g_curried v p = g (v ⊗ₜ[R] p)
    have : (TensorProduct.LieModule.liftLie R 𝔤 V P N) g_curried (v ⊗ₜ[R] p) = g_curried v p :=
      TensorProduct.LieModule.liftLie_apply (R := R) (L := 𝔤) (M := V) (N := P) (P := N) g_curried v p
    rw [← this]
    simp [g_curried]
  · intro t₁ t₂ ht₁ ht₂
    simp [map_add, ht₁, ht₂]

end
