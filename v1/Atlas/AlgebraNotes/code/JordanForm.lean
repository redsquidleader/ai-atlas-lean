/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.Block
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.SuccPred
import Mathlib.Algebra.Polynomial.Module.FiniteDimensional
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

namespace JordanForm

open Matrix Finset Module

section NilpotentLinearMap

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

def IsNilpotentOperator (T : Module.End R M) : Prop :=
  ∃ m : ℕ, T ^ m = 0

end NilpotentLinearMap

section JordanBlock

variable {F : Type*} [Field F]

def jordanBlock (a : ℕ) (μ : F) : Matrix (Fin a) (Fin a) F :=
  Matrix.of fun (i j : Fin a) =>
    if (i : ℕ) = (j : ℕ) then μ
    else if (i : ℕ) + 1 = (j : ℕ) then 1
    else 0

end JordanBlock

section JordanNormalForm

variable {F : Type*} [Field F]

def jordanNormalForm {r : ℕ} [DecidableEq (Fin r)]
    (blockSize : Fin r → ℕ) (μ : Fin r → F) :
    Matrix ((i : Fin r) × Fin (blockSize i)) ((i : Fin r) × Fin (blockSize i)) F :=
  Matrix.blockDiagonal' (fun i => jordanBlock (blockSize i) (μ i))

noncomputable def jordanMatrix {r : ℕ} [DecidableEq (Fin r)]
    (blockSize : Fin r → ℕ) (μ : Fin r → F)
    {n : ℕ} (hsum : ∑ i : Fin r, blockSize i = n) :
    Matrix (Fin n) (Fin n) F :=
  (Matrix.reindex (finSigmaFinEquiv.trans (finCongr hsum))
    (finSigmaFinEquiv.trans (finCongr hsum)))
    (jordanNormalForm blockSize μ)

end JordanNormalForm

section JordanMatrixForm

open Polynomial Module

theorem jordan_decomposition_matrix
    {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
    {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    ∃ (r : ℕ) (blockSize : Fin r → ℕ) (hsum : ∑ i : Fin r, blockSize i = n)
      (μ : Fin r → F) (P : Matrix (Fin n) (Fin n) F),
      IsUnit P ∧
      P⁻¹ * M * P = jordanMatrix blockSize μ hsum := by
  classical

  let f : End F (Fin n → F) := Matrix.toLin' M

  have hindep := End.independent_maxGenEigenspace (R := F) f
  have hspan := End.iSup_maxGenEigenspace_eq_top (K := F) f

  have hinternal : DirectSum.IsInternal f.maxGenEigenspace :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindep hspan

  have hnilp : ∀ (μ : F) (k : ℕ), IsNilpotent
      ((f - algebraMap F (End F (Fin n → F)) μ).restrict
        (End.mapsTo_genEigenspace_of_comm
          (Algebra.mul_sub_algebraMap_commutes f μ) μ k)) :=
    fun μ k => End.isNilpotent_restrict_sub_algebraMap f μ k


  sorry

end JordanMatrixForm

end JordanForm
