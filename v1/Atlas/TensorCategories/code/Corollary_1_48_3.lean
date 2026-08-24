/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.FiniteTensorCategory

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory

universe u

namespace CategoryTheory

/-- Two finite dimensional quasi-Hopf algebras `H₁` and `H₂` over `k` are monoidally
equivalent (in the sense of their categories of finite dimensional representations) if there
is a monoidal equivalence between `QuasiRepCat k H₁` and `QuasiRepCat k H₂`. -/
def QuasiRepCatMonoidalEquiv (k : Type u) [Field k]
    (H₁ : Type u) [Ring H₁] [Algebra k H₁] [QuasiHopfAlgebra k H₁]
    (H₂ : Type u) [Ring H₂] [Algebra k H₂] [QuasiHopfAlgebra k H₂] : Prop :=
  Nonempty (QuasiRepCat k H₁ ≌ QuasiRepCat k H₂)

/-- Corollary 1.48.3 of Etingof-Gelaki-Nikshych-Ostrik: The assignment `H ↦ Rep(H)` defines
a bijection between integral finite tensor categories `C` over `k` up to monoidal equivalence,
and finite dimensional quasi-Hopf algebras `H` over `k`, up to twist equivalence and
isomorphism. -/
theorem Corollary_1_48_3 (k : Type u) [Field k] :

    (∀ {C : Type u} [Category.{u} C] [MonoidalCategory C] [Abelian C]
       [EnoughProjectives C] [Linear k C] [RigidCategory C]
       (d : FPdimFunction (C := C)),
       d.IsIntegral →
       ∃ (H : Type u) (_ : Ring H) (_ : Algebra k H) (_ : QuasiHopfAlgebra k H)
         (_ : FiniteDimensional k H),
         Nonempty (C ≌ QuasiRepCat k H)) ∧

    (∀ (H₁ : Type u) [Ring H₁] [Algebra k H₁] [QuasiHopfAlgebra k H₁]
       [FiniteDimensional k H₁]
       (H₂ : Type u) [Ring H₂] [Algebra k H₂] [QuasiHopfAlgebra k H₂]
       [FiniteDimensional k H₂],
       QuasiHopfTwistIsoEquiv k H₁ H₂ →
       QuasiRepCatMonoidalEquiv k H₁ H₂) ∧

    (∀ (H₁ : Type u) [Ring H₁] [Algebra k H₁] [QuasiHopfAlgebra k H₁]
       [FiniteDimensional k H₁]
       (H₂ : Type u) [Ring H₂] [Algebra k H₂] [QuasiHopfAlgebra k H₂]
       [FiniteDimensional k H₂],
       QuasiRepCatMonoidalEquiv k H₁ H₂ →
       QuasiHopfTwistIsoEquiv k H₁ H₂) := by
  refine ⟨?_, ?_, ?_⟩
  ·
    intro C _ _ _ _ _ _ d hint
    exact integral_exists_quasiHopf_rep k d hint
  ·
    intro H₁ _ _ _ _ H₂ _ _ _ _ hte
    exact twist_equiv_imp_quasiRepCat_equiv k H₁ H₂ hte
  ·
    intro H₁ _ _ _ _ H₂ _ _ _ _ ⟨e⟩
    exact quasiRepCat_equiv_imp_twist_equiv k H₁ H₂ e

end CategoryTheory
