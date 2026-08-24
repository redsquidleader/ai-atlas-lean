/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.BasedRings

/-- Proposition 1.42.9: The categorifications of the group ring `ℤ[G]` are the categories
`Vec_G^ω`, and they are parametrized by `H^3(G, k×) / Out(G)`. This bundles the three
ingredients: (i) every `Vec_G^ω` actually categorifies `ℤ[G]`; (ii) every categorification
is monoidally equivalent to some `Vec_G^ω`; and (iii) two cocycles `ω₁, ω₂` give equivalent
categorifications iff they lie in the same `Out(G)`-orbit of cohomology classes. -/
theorem Proposition_1_42_9
    (G : Type*) [DecidableEq G] [Fintype G] [Group G]
    (k : Type*) [Field k] :

    (∀ (ω : NormalizedGroupCocycle3 G kˣ),
      (∀ g h : G,
        (CG.tensorObj' (⟨g⟩ : CG G kˣ ω) (⟨h⟩ : CG G kˣ ω)).val = g * h) ∧
      (CG.unit' : CG G kˣ ω).val = (1 : G) ∧
      (∀ g : G, (CG.dualObj (⟨g⟩ : CG G kˣ ω)).val =
        (FusionRing.groupRingFusionRing G).star g)) ∧

    (∀ (categ : Categorification (FusionRing.groupRingFusionRing G) k),
      ∃ (ω : NormalizedGroupCocycle3 G kˣ),
        Nonempty (@MonoidalEquiv categ.C categ.cat categ.monoidal
          (CG G kˣ ω) _ inferInstance)) ∧

    (∀ (ω₁ ω₂ : NormalizedGroupCocycle3 G kˣ),
      CocycleOutOrbitEquiv ω₁ ω₂ ↔
        Nonempty (MonoidalEquiv (CG G kˣ ω₁) (CG G kˣ ω₂))) :=
  ⟨fun ω => Proposition_1_42_9_VecGomega_is_categorification G k ω,
   fun categ => Proposition_1_42_9_categorifications_are_VecGomega G k categ,
   fun ω₁ ω₂ => Proposition_1_42_9_parametrization G k ω₁ ω₂⟩
