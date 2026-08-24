/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.TaftWilsonComponentGrouplike

open scoped TensorProduct
open Coalgebra

universe u v

variable {R : Type u} {C : Type v}
variable [Field R] [AddCommGroup C] [Module R C] [Coalgebra R C]

/-- Corollary 1.29.5 (Taft-Wilson theorem, EGNO): for a pointed coalgebra `C` over a field,
(i) the coradical `C_0` is spanned by linearly independent grouplike elements, (ii) the
quotient `C_1/C_0` decomposes as `⊕_{g,h} Prim_{g,h}(C)/k(h - g)`, and (iii) any
non-cosemisimple pointed coalgebra contains nontrivial skew-primitive elements. -/
theorem Corollary_1_29_5
    (hPointed : IsPointedCoalgebra (R := R) (C := C)) :

    (coradical (R := R) (C := C) =
      ⨆ (g : C) (_ : g ∈ grouplikes (R := R) (C := C)), Submodule.span R {g}) ∧

    (coradicalFiltration (R := R) (C := C) 1 =
      coradical ⊔ ⨆ (g : C) (_ : g ∈ grouplikes (R := R) (C := C))
        (h : C) (_ : h ∈ grouplikes (R := R) (C := C)),
        skewPrimitiveSpace g h) ∧

    (iSupIndep (fun (p : {g : C // g ∈ grouplikes (R := R) (C := C)} ×
                        {h : C // h ∈ grouplikes (R := R) (C := C)}) =>
      Submodule.map (coradical (R := R) (C := C)).mkQ (skewPrimitiveSpace p.1.1 p.2.1))) :=
  ⟨taftWilson_coradical_eq_span_grouplikes R C hPointed,
   taftWilson_C1_eq R C hPointed,
   taftWilson_directness hPointed⟩
