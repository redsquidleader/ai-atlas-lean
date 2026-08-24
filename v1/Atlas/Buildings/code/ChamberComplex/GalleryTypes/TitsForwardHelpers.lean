/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.ChamberComplex.Folding
import Atlas.Buildings.code.ChamberComplex.UniquenessBook
import Atlas.Buildings.code.Building.CoxeterComplexFoldings
import Atlas.Buildings.code.ChamberComplex.GalleryTypes.CoxeterFolding
import Atlas.Buildings.code.CoxeterGroup.DeletionInjectivity

open scoped Classical

namespace CoxeterSystemFromDeletion

variable {B : Type*} {W : Type*} [Group W]

/-- Under the deletion-condition Coxeter system construction, the abstract simple reflection
equals the original generator $\text{gen}(s)$. -/
lemma deletion_coxeter_simple_eq_gen
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1)
    (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1)
    (hgen_surj : Subgroup.closure (Set.range gen) = ⊤)
    (hDel : SatisfiesDeletionConditionGen gen) (s : B) :
    (deletion_implies_coxeter_system gen hgen_inv hgen_ne hgen_surj hDel).simple s = gen s := by
  exact deletionCanonicalHom_apply_simple gen hgen_inv hgen_ne s

/-- The `mulEquiv` of a `CoxeterSystem` sends its abstract simple reflection to the simple
reflection of the canonical Coxeter system associated to the matrix $M$. -/
lemma mulEquiv_simple_eq_toCoxeterSystem_simple
    {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (s : B) :
    cs.mulEquiv (cs.simple s) = M.toCoxeterSystem.simple s := by


  simp [CoxeterSystem.simple, CoxeterMatrix.toCoxeterSystem]

/-- The `mulEquiv` of the deletion-condition Coxeter system maps a generator to the corresponding
simple reflection of the canonical Coxeter system. -/
lemma deletion_coxeter_mulEquiv_gen
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1)
    (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1)
    (hgen_surj : Subgroup.closure (Set.range gen) = ⊤)
    (hDel : SatisfiesDeletionConditionGen gen) (s : B) :
    (deletion_implies_coxeter_system gen hgen_inv hgen_ne hgen_surj hDel).mulEquiv (gen s) =
      (deletionCoxeterMatrix gen hgen_inv hgen_ne).toCoxeterSystem.simple s := by
  rw [← deletion_coxeter_simple_eq_gen gen hgen_inv hgen_ne hgen_surj hDel s]
  exact mulEquiv_simple_eq_toCoxeterSystem_simple _ s

end CoxeterSystemFromDeletion

variable {V : Type*} [DecidableEq V]

namespace ChamberComplex

/-- *Tits forward construction*: from a thin chamber complex with sufficient foldings, build a
generator set and labelling $\varphi : \text{chambers} \to W$ satisfying the involution, no-product,
surjectivity, deletion, bijectivity, adjacency-correspondence and facet-sharing properties — the
data needed to recognize $K$ as a Coxeter complex. -/
theorem tits_forward_construction
    (K : ChamberComplex V)
    (hThin : K.IsThin)
    (hSF : AptIsCoxeterProof.HasSufficientFoldings K) :
    ∃ (B : Type) (W : Type) (_ : Group W)
      (gen : B → W)
      (φ : Finset V → W),
      (∀ s, gen s * gen s = 1) ∧
      (∀ s t, s ≠ t → gen s * gen t ≠ 1) ∧
      (Subgroup.closure (Set.range gen) = ⊤) ∧
      (CoxeterSystemFromDeletion.SatisfiesDeletionConditionGen gen) ∧
      (∀ C, K.toSimplicialComplex.IsMaximal C →
        ∀ D, K.toSimplicialComplex.IsMaximal D → φ C = φ D → C = D) ∧
      (∀ w : W, ∃ C, K.toSimplicialComplex.IsMaximal C ∧ φ C = w) ∧
      (∀ C C', K.toSimplicialComplex.Adjacent C C' →
        ∃ s, φ C' = φ C * gen s) ∧
      (∀ C C' s, K.toSimplicialComplex.IsMaximal C →
        K.toSimplicialComplex.IsMaximal C' →
        φ C' = φ C * gen s → K.toSimplicialComplex.Adjacent C C') ∧
      (∀ F C, K.toSimplicialComplex.IsFacet F C →
        K.toSimplicialComplex.IsMaximal C →
        ∃ D, D ≠ C ∧ K.toSimplicialComplex.IsMaximal D ∧
          K.toSimplicialComplex.IsFacet F D) := by sorry

end ChamberComplex
