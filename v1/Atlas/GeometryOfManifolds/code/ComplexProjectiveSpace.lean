/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.AdvancedKahler
import Atlas.GeometryOfManifolds.code.ManifoldDFS

set_option autoImplicit false

open scoped Manifold ContDiff

noncomputable section

/-- The setoid on nonzero vectors in $\mathbb{C}^{n+1}$: $v \sim w$ iff $w = c v$ for some $c \in \mathbb{C}^\times$, used to define $\mathbb{CP}^n$. -/
def CPnSetoid (n : ℕ) : Setoid {v : Fin (n + 1) → ℂ // v ≠ 0} where
  r v w := ∃ (c : ℂ), c ≠ 0 ∧ (∀ i, w.1 i = c * v.1 i)
  iseqv :=
    ⟨fun v => ⟨1, one_ne_zero, fun i => by simp⟩,
     fun ⟨c, hc, h⟩ => ⟨c⁻¹, inv_ne_zero hc, fun i => by
        rw [h i, inv_mul_cancel_left₀ hc]⟩,
     fun ⟨c₁, hc₁, h₁⟩ ⟨c₂, hc₂, h₂⟩ => ⟨c₂ * c₁, mul_ne_zero hc₂ hc₁, fun i => by
        rw [h₂ i, h₁ i]; ring⟩⟩

/-- Complex projective space $\mathbb{CP}^n = (\mathbb{C}^{n+1} \setminus \{0\}) / \mathbb{C}^\times$. -/
def ComplexProjectiveSpace (n : ℕ) : Type :=
  Quotient (CPnSetoid n)

/-- $\mathbb{CP}^n$ carries the quotient topology from $\mathbb{C}^{n+1} \setminus \{0\}$. -/
instance CPn_topologicalSpace (n : ℕ) : TopologicalSpace (ComplexProjectiveSpace n) :=
  instTopologicalSpaceQuotient (s := CPnSetoid n)


/-- The smooth atlas on $\mathbb{CP}^n$ making it a $(2n)$-dimensional real charted space (via affine charts $U_i = \{[z_0 : \cdots : z_n] : z_i \ne 0\}$). -/
instance CPn_chartedSpace (n : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin (2 * n))) (ComplexProjectiveSpace n) := by


  exact sorry


/-- $\mathbb{CP}^n$ is a smooth (real) manifold of dimension $2n$. -/
instance CPn_isManifold (n : ℕ) :
    IsManifold (𝓡 (2 * n)) ∞ (ComplexProjectiveSpace n) := by


  exact sorry

/-- Graded differential forms $\Omega^\bullet(\mathbb{CP}^n)$ in the DFS framework. -/
abbrev CPn_Ω (n : ℕ) : ℕ → Type :=
  ManifoldΩ (𝓡 (2 * n)) (ComplexProjectiveSpace n)

/-- Vector fields $\mathfrak{X}(\mathbb{CP}^n)$ in the DFS framework. -/
abbrev CPn_VF (n : ℕ) : Type :=
  ManifoldVF (𝓡 (2 * n)) (ComplexProjectiveSpace n)

/-- The differential-form-space structure on $\mathbb{CP}^n$. -/
noncomputable instance instCPnDFS (n : ℕ) :
    DifferentialFormSpace (CPn_Ω n) (CPn_VF n) :=
  manifoldDFS (𝓡 (2 * n)) (ComplexProjectiveSpace n)


/-- The Fubini–Study $2$-form $\omega_{\mathrm{FS}}$ on $\mathbb{CP}^n$: the canonical Kähler form, locally $\omega_{\mathrm{FS}} = \frac{i}{2} \partial \bar\partial \log(1 + |z|^2)$. -/
noncomputable def CPn_fubiniStudy (n : ℕ) : CPn_Ω n 2 := by exact sorry


/-- The canonical (integrable) almost complex structure $J$ on $\mathbb{CP}^n$ coming from its complex-manifold structure. -/
noncomputable def CPn_complexStr (n : ℕ) :
    AlmostComplexStr (Ω := CPn_Ω n) (VF := CPn_VF n) := by exact sorry


/-- The Fubini–Study form is closed: $d\omega_{\mathrm{FS}} = 0$. -/
theorem CPn_fubiniStudy_closed (n : ℕ) :
    (instCPnDFS n).d (CPn_fubiniStudy n) = 0 := by sorry


/-- The Fubini–Study form is nondegenerate: $\iota_X \omega_{\mathrm{FS}} = 0 \implies X = 0$. -/
theorem CPn_fubiniStudy_nondegenerate (n : ℕ) :
    Function.Injective (fun (X : CPn_VF n) =>
      (instCPnDFS n).ι X (CPn_fubiniStudy n)) := by sorry

/-- $(\mathbb{CP}^n, \omega_{\mathrm{FS}})$ is a symplectic manifold. -/
noncomputable def CPn_symplectic (n : ℕ) :
    @SymplecticManifold (CPn_Ω n) (CPn_VF n) (instCPnDFS n) :=
  ⟨CPn_fubiniStudy n, CPn_fubiniStudy_closed n, CPn_fubiniStudy_nondegenerate n⟩


/-- $J$-compatibility of $\omega_{\mathrm{FS}}$: $\omega_{\mathrm{FS}}(Ju, Jv) = \omega_{\mathrm{FS}}(u, v)$. -/
theorem CPn_fubiniStudy_J_preserves (n : ℕ) :
    ∀ (u v : CPn_VF n),
      (instCPnDFS n).ι ((CPn_complexStr n).J u)
        ((instCPnDFS n).ι ((CPn_complexStr n).J v) (CPn_symplectic n).ω) =
      (instCPnDFS n).ι u ((instCPnDFS n).ι v (CPn_symplectic n).ω) := by sorry


/-- The Fubini–Study form tames $J$: the map $v \mapsto \omega_{\mathrm{FS}}(Jv, \cdot)$ is injective (so $g(u,v) = \omega_{\mathrm{FS}}(u, Jv)$ is a Riemannian metric). -/
theorem CPn_fubiniStudy_taming (n : ℕ) :
    Function.Injective (fun (v : CPn_VF n) =>
      (instCPnDFS n).ι ((CPn_complexStr n).J v) (CPn_symplectic n).ω) := by sorry


/-- Vector fields on $\mathbb{CP}^n$ form a Lie algebra under the Lie bracket. -/
noncomputable instance instCPnHasLieBracket (n : ℕ) :
    HasLieBracket (CPn_Ω n) (CPn_VF n) := by exact sorry


/-- The Nijenhuis tensor $N_J$ associated to the almost complex structure $J$ on $\mathbb{CP}^n$. -/
noncomputable def CPn_nijenhuisTensor (n : ℕ) :
    NijenhuisTensor (CPn_complexStr n) := by
  exact sorry


/-- Witness that `CPn_nijenhuisTensor n` is genuinely the Nijenhuis tensor of $J$. -/
noncomputable def CPn_isNijenhuisOf (n : ℕ) :
    IsNijenhuisOf (CPn_complexStr n) (CPn_nijenhuisTensor n) := by
  exact sorry


/-- The almost complex structure $J$ on $\mathbb{CP}^n$ is integrable: $N_J = 0$ (so $\mathbb{CP}^n$ is a complex manifold, hence Kähler). -/
noncomputable def CPn_isIntegrable (n : ℕ) :
    IsIntegrable (CPn_complexStr n) (CPn_nijenhuisTensor n) := by
  exact sorry


/-- For $n \geq 1$, $\mathbb{CP}^n$ is a compact symplectic manifold. -/
@[reducible]
noncomputable def CPn_compactSymplectic (n : ℕ) (_hn : 0 < n) :
    IsCompactSymplectic (CPn_Ω n) (CPn_VF n) := by exact sorry

/-- For $n \geq 1$, the Fubini–Study form is not exact: $[\omega_{\mathrm{FS}}] \ne 0 \in H^2(\mathbb{CP}^n)$ (otherwise the symplectic form's top power $\omega^n$ would be exact, contradicting compactness). -/
theorem CPn_fubiniStudy_not_exact (n : ℕ) (hn : 0 < n) :
    ¬ DifferentialFormSpace.IsExact' (CPn_VF n) (CPn_fubiniStudy n) := by
  have h := (CPn_compactSymplectic n hn).symplectic_not_exact (CPn_symplectic n)
  exact h

/-- For $n \geq 1$, the Fubini–Study form is nonzero (an immediate consequence of non-exactness). -/
theorem CPn_fubiniStudy_nonzero (n : ℕ) (hn : 0 < n) :
    CPn_fubiniStudy n ≠ 0 := by
  intro h
  have hexact : DifferentialFormSpace.IsExact' (CPn_VF n) (CPn_fubiniStudy n) := by
    refine ⟨0, ?_⟩
    rw [h]
    exact (@DifferentialFormSpace.d_zero_val (CPn_Ω n) (CPn_VF n) (instCPnDFS n) 1).symm
  exact CPn_fubiniStudy_not_exact n hn hexact

end
