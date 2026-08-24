/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.WeilChatelet
import Atlas.ArithmeticGeometry.code.GaloisCohomology

noncomputable section

universe u

open GaloisCohomology

/-- Data witnessing the bijection between the Weil-Châtelet set of $E$-torsors over $k$ (mod
$k$-isomorphism) and the first cohomology group $H^1(G, E_{\mathrm{pts}})$: a well-defined,
injective, and surjective `cocycleMap`. -/
structure WCH1Data (k : Type u) [Field k] (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (G : Type u) [Group G] [TopologicalSpace G]
    [TopologicalSpace E_pts] [DistribMulAction G E_pts]
    [ContinuousAdd E_pts] [ContinuousNeg E_pts] [ContinuousSMul G E_pts] where
  cocycleMap : ETorsor k W E_pts → H1 G E_pts
  cocycleMap_wellDefined : ∀ (T₁ T₂ : ETorsor k W E_pts),
    ETorsor.Equiv T₁ T₂ → cocycleMap T₁ = cocycleMap T₂
  cocycleMap_injective : ∀ (T₁ T₂ : ETorsor k W E_pts),
    cocycleMap T₁ = cocycleMap T₂ → ETorsor.Equiv T₁ T₂
  cocycleMap_surjective : Function.Surjective cocycleMap

/-- Data of a Galois action on a torsor `T`: a Galois map $\sigma \mapsto \sigma_C$ acting on
points of `T`, equivariant with the $E$-action and a group homomorphism in $\sigma$, together
with a continuity condition. -/
structure GaloisActionOnTorsor (k : Type u) [Field k] (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (G : Type u) [Group G] [TopologicalSpace G]
    [TopologicalSpace E_pts] [DistribMulAction G E_pts]
    [ContinuousSMul G E_pts]
    (T : ETorsor k W E_pts) where
  σ_C : G → T.C_pts → T.C_pts
  compat : haveI := T.torsor.toAddTorsor
    ∀ (σ : G) (p : E_pts) (c : T.C_pts), σ_C σ (p +ᵥ c) = (σ • p) +ᵥ σ_C σ c
  mul_compat : ∀ (τ σ : G) (c : T.C_pts), σ_C (τ * σ) c = σ_C τ (σ_C σ c)
  cont : haveI := T.torsor.toAddTorsor
    ∀ (Q₀ : T.C_pts), Continuous (fun σ => σ_C σ Q₀ -ᵥ Q₀ : G → E_pts)

/-- The canonical cocycle attached to a torsor `T`: deferred to a `sorry`; it should produce a
continuous crossed homomorphism $G \to E_{\mathrm{pts}}$ from the Galois action on `T`. -/
noncomputable def canonical_torsor_cocycle (k : Type u) [Field k] (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (G : Type u) [Group G] [TopologicalSpace G]
    [TopologicalSpace E_pts] [DistribMulAction G E_pts]
    [ContinuousAdd E_pts] [ContinuousSMul G E_pts]
    (T : ETorsor k W E_pts) : ContCrossedHom G E_pts := by sorry

/-- Galois descent (surjectivity onto cocycles): every continuous crossed homomorphism
$\alpha \colon G \to E_{\mathrm{pts}}$ arises as the canonical cocycle of some $E$-torsor over
$k$. -/
theorem galois_descent_surjective (k : Type u) [Field k] (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (G : Type u) [Group G] [TopologicalSpace G]
    [TopologicalSpace E_pts] [DistribMulAction G E_pts]
    [ContinuousAdd E_pts] [ContinuousSMul G E_pts]
    (α : ContCrossedHom G E_pts) :
    ∃ (T : ETorsor k W E_pts), canonical_torsor_cocycle k W E_pts G T = α := by sorry

/-- Existence of a Galois action on any torsor `T`: explicit construction via twisting by the
canonical cocycle at a chosen base point. -/
noncomputable def galoisActionOnTorsor_exists (k : Type u) [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (G : Type u) [Group G] [TopologicalSpace G]
    [TopologicalSpace E_pts] [DistribMulAction G E_pts]
    [ContinuousAdd E_pts] [ContinuousSMul G E_pts]
    (T : ETorsor k W E_pts) : GaloisActionOnTorsor k W E_pts G T := by
  letI : AddTorsor E_pts T.C_pts := T.torsor.toAddTorsor
  let B : T.C_pts := T.torsor.toAddTorsor.nonempty.some
  let α_T := canonical_torsor_cocycle k W E_pts G T
  exact {
    σ_C := fun σ c => (σ • (c -ᵥ B) + α_T σ) +ᵥ B
    compat := by
      intro σ p c
      rw [vadd_vsub_assoc]
      rw [smul_add]
      rw [add_assoc]
      rw [add_vadd]
    mul_compat := by
      intro τ σ c


      congr 1
      rw [vadd_vsub]
      rw [mul_smul]
      rw [smul_add]
      have hcc : α_T (τ * σ) = τ • α_T σ + α_T τ := α_T.cocycle_condition τ σ
      rw [hcc, add_assoc]
    cont := by
      intro Q₀


      have hc1 : Continuous (fun σ : G => σ • (Q₀ -ᵥ B : E_pts)) :=
        continuous_id.smul continuous_const
      have hc2 : Continuous (fun σ : G => α_T σ) := α_T.continuous_toFun
      have hc3 : Continuous (fun σ : G => σ • (Q₀ -ᵥ B : E_pts) + α_T σ) :=
        hc1.add hc2


      convert hc3.add continuous_const using 1
      ext σ
      exact vadd_vsub_assoc _ _ _
  }

/-- Restatement of the group-action axiom for `GaloisActionOnTorsor`: $\sigma_C(\tau\sigma) = \sigma_C(\tau) \circ \sigma_C(\sigma)$. -/
theorem galoisAction_mul_compat (k : Type u) [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (G : Type u) [Group G] [TopologicalSpace G]
    [TopologicalSpace E_pts] [DistribMulAction G E_pts]
    [ContinuousSMul G E_pts]
    (T : ETorsor k W E_pts)
    (ga : GaloisActionOnTorsor k W E_pts G T)
    (τ σ : G) (c : T.C_pts) :
    ga.σ_C (τ * σ) c = ga.σ_C τ (ga.σ_C σ c) :=
  ga.mul_compat τ σ c

/-- For any base point $Q_0 \in C_T$, the function $\sigma \mapsto \sigma_C(Q_0) -_v Q_0$ is a
crossed homomorphism $G \to E_{\mathrm{pts}}$. -/
theorem cocycleCondition_of_galoisAction (k : Type u) [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (G : Type u) [Group G] [TopologicalSpace G]
    [TopologicalSpace E_pts] [DistribMulAction G E_pts]
    [ContinuousSMul G E_pts]
    (T : ETorsor k W E_pts)
    (ga : GaloisActionOnTorsor k W E_pts G T)
    (Q₀ : T.C_pts) :
    haveI := T.torsor.toAddTorsor
    IsCrossedHom (fun σ => ga.σ_C σ Q₀ -ᵥ Q₀ : G → E_pts) := by
  letI : AddTorsor E_pts T.C_pts := T.torsor.toAddTorsor
  intro τ σ

  show ga.σ_C (τ * σ) Q₀ -ᵥ Q₀ = τ • (ga.σ_C σ Q₀ -ᵥ Q₀) + (ga.σ_C τ Q₀ -ᵥ Q₀)

  rw [galoisAction_mul_compat k W E_pts G T ga τ σ Q₀]

  conv_lhs => rw [show ga.σ_C σ Q₀ = (ga.σ_C σ Q₀ -ᵥ Q₀) +ᵥ Q₀ from (vsub_vadd _ _).symm]

  rw [ga.compat τ (ga.σ_C σ Q₀ -ᵥ Q₀) Q₀]

  exact vadd_vsub_assoc _ _ _

/-- The construction of the cocycle map at the level of $E$-torsors: given a torsor $T$, choose a
base point, take the Galois-action cocycle $\sigma \mapsto \sigma_C(Q_0) -_v Q_0$, and pass to
its class in $H^1$. -/
noncomputable def cocycleMap_construction (k : Type u) [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (G : Type u) [Group G] [TopologicalSpace G]
    [TopologicalSpace E_pts] [DistribMulAction G E_pts]
    [ContinuousAdd E_pts] [ContinuousNeg E_pts] [ContinuousSMul G E_pts] :
    ETorsor k W E_pts → H1 G E_pts := fun T => by

  let ga := galoisActionOnTorsor_exists k W E_pts G T

  letI := T.torsor.toAddTorsor
  let Q₀ : T.C_pts := T.torsor.toAddTorsor.nonempty.some

  let α : G → E_pts := fun σ => ga.σ_C σ Q₀ -ᵥ Q₀

  let cch : ContCrossedHom G E_pts :=
    { toFun := α
      cocycle_condition := cocycleCondition_of_galoisAction k W E_pts G T ga Q₀
      continuous_toFun := ga.cont Q₀ }

  exact H1.mk G E_pts cch

/-- Restated compatibility: a $k$-isomorphism $e$ between torsors that intertwines the
$E$-actions also intertwines the Galois actions, when this is given as a hypothesis. -/
theorem galoisAction_kIsom_compat (k : Type u) [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (G : Type u) [Group G] [TopologicalSpace G]
    [TopologicalSpace E_pts] [DistribMulAction G E_pts]
    [ContinuousSMul G E_pts]
    {T₁ T₂ : ETorsor k W E_pts}
    (e : T₁.C_pts ≃ T₂.C_pts)
    (_hcompat : haveI := T₁.torsor.toAddTorsor; haveI := T₂.torsor.toAddTorsor;
      ∀ (p : E_pts) (q : T₁.C_pts), e (p +ᵥ q) = p +ᵥ e q)
    (ga₁ : GaloisActionOnTorsor k W E_pts G T₁)
    (ga₂ : GaloisActionOnTorsor k W E_pts G T₂)
    (hgal : ∀ σ q, e (ga₁.σ_C σ q) = ga₂.σ_C σ (e q))
    (σ : G) (q : T₁.C_pts) :
    e (ga₁.σ_C σ q) = ga₂.σ_C σ (e q) := hgal σ q

/-- A $k$-isomorphism between torsors is automatically Galois-equivariant: the proof is deferred. -/
theorem galoisEquivariance_of_kIsom (k : Type u) [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (G : Type u) [Group G] [TopologicalSpace G]
    [TopologicalSpace E_pts] [DistribMulAction G E_pts]
    [ContinuousAdd E_pts] [ContinuousSMul G E_pts]
    {T₁ T₂ : ETorsor k W E_pts}
    (e : T₁.C_pts ≃ T₂.C_pts)
    (hcompat : haveI := T₁.torsor.toAddTorsor; haveI := T₂.torsor.toAddTorsor;
      ∀ (p : E_pts) (q : T₁.C_pts), e (p +ᵥ q) = p +ᵥ e q)
    (ga₁ : GaloisActionOnTorsor k W E_pts G T₁)
    (ga₂ : GaloisActionOnTorsor k W E_pts G T₂) :
    ∀ σ q, e (ga₁.σ_C σ q) = ga₂.σ_C σ (e q) := by sorry

/-- The cocycle map is well-defined on equivalence classes of $E$-torsors: equivalent torsors
produce cohomologous cocycles, hence equal classes in $H^1$. -/
lemma cocycleMap_wellDefined_proof (k : Type u) [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (G : Type u) [Group G] [TopologicalSpace G]
    [TopologicalSpace E_pts] [DistribMulAction G E_pts]
    [ContinuousAdd E_pts] [ContinuousNeg E_pts] [ContinuousSMul G E_pts] :
    ∀ (T₁ T₂ : ETorsor k W E_pts),
      ETorsor.Equiv T₁ T₂ →
      cocycleMap_construction k W E_pts G T₁ = cocycleMap_construction k W E_pts G T₂ := by
  intro T₁ T₂ ⟨e, _hk, hcompat⟩

  let ga₁ := galoisActionOnTorsor_exists k W E_pts G T₁
  let ga₂ := galoisActionOnTorsor_exists k W E_pts G T₂

  letI := T₁.torsor.toAddTorsor
  letI := T₂.torsor.toAddTorsor
  let Q₁ : T₁.C_pts := T₁.torsor.toAddTorsor.nonempty.some
  let Q₂ : T₂.C_pts := T₂.torsor.toAddTorsor.nonempty.some


  have hgal_compat : ∀ σ q, e (ga₁.σ_C σ q) = ga₂.σ_C σ (e q) :=
    galoisEquivariance_of_kIsom k W E_pts G e hcompat ga₁ ga₂
  have hcocycle_eq : ∀ σ : G,
      ga₂.σ_C σ (e Q₁) -ᵥ (e Q₁) = (ga₁.σ_C σ Q₁ -ᵥ Q₁ : E_pts) := by
    intro σ
    rw [← galoisAction_kIsom_compat k W E_pts G e hcompat ga₁ ga₂ hgal_compat σ Q₁]
    exact ETorsor.Equiv.vsub_preserving e hcompat _ _

  show cocycleMap_construction k W E_pts G T₁ = cocycleMap_construction k W E_pts G T₂
  let α₁ : ContCrossedHom G E_pts :=
    { toFun := fun σ => ga₁.σ_C σ Q₁ -ᵥ Q₁
      cocycle_condition := cocycleCondition_of_galoisAction k W E_pts G T₁ ga₁ Q₁
      continuous_toFun := ga₁.cont Q₁ }
  let α₂ : ContCrossedHom G E_pts :=
    { toFun := fun σ => ga₂.σ_C σ Q₂ -ᵥ Q₂
      cocycle_condition := cocycleCondition_of_galoisAction k W E_pts G T₂ ga₂ Q₂
      continuous_toFun := ga₂.cont Q₂ }
  suffices H1.mk G E_pts α₁ = H1.mk G E_pts α₂ by exact this
  rw [H1.eq_iff]
  rw [mem_contPrincipalCrossedHomSubgroup_iff]
  rw [isPrincipalCrossedHom_iff]
  let P : E_pts := e Q₁ -ᵥ Q₂
  refine ⟨P, fun σ => ?_⟩
  have hα₁ : α₁ σ = ga₁.σ_C σ Q₁ -ᵥ Q₁ := rfl
  have hα₂ : α₂ σ = ga₂.σ_C σ Q₂ -ᵥ Q₂ := rfl
  have hsub : (α₁ - α₂) σ = α₁ σ - α₂ σ := by
    simp only [sub_eq_add_neg, ContCrossedHom.add_apply, ContCrossedHom.neg_apply]
  rw [hsub, hα₁, hα₂]
  rw [← hcocycle_eq σ]
  have hP : e Q₁ = P +ᵥ Q₂ := (vsub_vadd (e Q₁) Q₂).symm
  rw [hP, ga₂.compat σ P Q₂]
  simp only [vadd_vsub_vadd_comm]
  abel

/-- The cocycle map is injective on torsor equivalence classes: torsors that map to the same
class in $H^1$ are equivalent (as $k$-isomorphic torsors). -/
lemma cocycleMap_injective_proof (k : Type u) [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (G : Type u) [Group G] [TopologicalSpace G]
    [TopologicalSpace E_pts] [DistribMulAction G E_pts]
    [ContinuousAdd E_pts] [ContinuousNeg E_pts] [ContinuousSMul G E_pts] :
    ∀ (T₁ T₂ : ETorsor k W E_pts),
      cocycleMap_construction k W E_pts G T₁ = cocycleMap_construction k W E_pts G T₂ →
      ETorsor.Equiv T₁ T₂ := by
  intro T₁ T₂ heq


  letI := T₁.torsor.toAddTorsor
  letI := T₂.torsor.toAddTorsor
  obtain ⟨q₁⟩ := T₁.torsor.nonempty
  obtain ⟨q₂⟩ := T₂.torsor.nonempty

  let e : T₁.C_pts ≃ T₂.C_pts :=
    (Equiv.vaddConst q₁).symm.trans (Equiv.vaddConst q₂)


  refine ⟨e, ⟨IsKRationalMap.of_torsor_translation_of_cohomologous q₁ q₂ heq⟩, ?_⟩

  intro p q
  simp only [e, Equiv.trans_apply, Equiv.coe_vaddConst_symm, Equiv.coe_vaddConst,
    vadd_vsub_assoc, add_vadd]

/-- For any continuous crossed homomorphism $\alpha$, there is a torsor $T$ and a point
$Q_0 \in C_T$ such that the Galois action on $T$ realises $\alpha$ as $\sigma \mapsto
\sigma_C(Q_0) -_v Q_0$. -/
theorem galoisDescent_torsor_exists (k : Type u) [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (G : Type u) [Group G] [TopologicalSpace G]
    [TopologicalSpace E_pts] [DistribMulAction G E_pts]
    [ContinuousAdd E_pts] [ContinuousNeg E_pts] [ContinuousSMul G E_pts]
    (α : ContCrossedHom G E_pts) :
    ∃ (T : ETorsor k W E_pts) (Q₀ : T.C_pts),
      haveI := T.torsor.toAddTorsor
      let ga := galoisActionOnTorsor_exists k W E_pts G T
      ∀ σ : G, ga.σ_C σ Q₀ -ᵥ Q₀ = α σ := by


  obtain ⟨T, hT⟩ := galois_descent_surjective k W E_pts G α


  letI : AddTorsor E_pts T.C_pts := T.torsor.toAddTorsor
  let B : T.C_pts := T.torsor.toAddTorsor.nonempty.some
  refine ⟨T, B, fun σ => ?_⟩


  show (galoisActionOnTorsor_exists k W E_pts G T).σ_C σ B -ᵥ B = α σ

  simp only [galoisActionOnTorsor_exists]


  rw [vsub_self, smul_zero, zero_add, vadd_vsub, hT]

/-- For each continuous crossed homomorphism $\alpha$, there is an $E$-torsor $T$ whose image
under `cocycleMap_construction` is the class of $\alpha$ in $H^1$. -/
theorem galoisDescent_torsor_of_cocycle (k : Type u) [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (G : Type u) [Group G] [TopologicalSpace G]
    [TopologicalSpace E_pts] [DistribMulAction G E_pts]
    [ContinuousAdd E_pts] [ContinuousNeg E_pts] [ContinuousSMul G E_pts]
    (α : ContCrossedHom G E_pts) :
    ∃ (T : ETorsor k W E_pts), cocycleMap_construction k W E_pts G T = H1.mk G E_pts α := by


  obtain ⟨T, Q₀, hQ₀⟩ := galoisDescent_torsor_exists k W E_pts G α
  refine ⟨T, ?_⟩


  show cocycleMap_construction k W E_pts G T = H1.mk G E_pts α
  unfold cocycleMap_construction


  letI := T.torsor.toAddTorsor
  let ga := galoisActionOnTorsor_exists k W E_pts G T
  let Q₀' : T.C_pts := T.torsor.toAddTorsor.nonempty.some

  let α_Q₀ : ContCrossedHom G E_pts :=
    { toFun := fun σ => ga.σ_C σ Q₀ -ᵥ Q₀
      cocycle_condition := cocycleCondition_of_galoisAction k W E_pts G T ga Q₀
      continuous_toFun := ga.cont Q₀ }

  let α_Q₀' : ContCrossedHom G E_pts :=
    { toFun := fun σ => ga.σ_C σ Q₀' -ᵥ Q₀'
      cocycle_condition := cocycleCondition_of_galoisAction k W E_pts G T ga Q₀'
      continuous_toFun := ga.cont Q₀' }

  have hα_eq : ∀ σ : G, α_Q₀ σ = α σ := hQ₀
  have hα_ext : α_Q₀ = α := by
    ext σ
    exact hα_eq σ


  suffices H1.mk G E_pts α_Q₀' = H1.mk G E_pts α by exact this
  rw [← hα_ext]
  rw [H1.eq_iff]
  rw [mem_contPrincipalCrossedHomSubgroup_iff]
  rw [isPrincipalCrossedHom_iff]
  let P' : E_pts := Q₀' -ᵥ Q₀
  refine ⟨P', fun σ => ?_⟩
  have hsub : (α_Q₀' - α_Q₀) σ = α_Q₀' σ - α_Q₀ σ := by
    simp only [sub_eq_add_neg, ContCrossedHom.add_apply, ContCrossedHom.neg_apply]
  rw [hsub]
  show σ • P' - P' = (ga.σ_C σ Q₀' -ᵥ Q₀') - (ga.σ_C σ Q₀ -ᵥ Q₀)
  have hP' : Q₀' = P' +ᵥ Q₀ := (vsub_vadd Q₀' Q₀).symm
  rw [hP', ga.compat σ P' Q₀]
  simp only [vadd_vsub_vadd_comm]
  abel

/-- The cocycle map $\mathrm{ETorsor}(k, W, E) \to H^1(G, E_{\mathrm{pts}})$ is surjective. -/
lemma cocycleMap_surjective_proof (k : Type u) [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (G : Type u) [Group G] [TopologicalSpace G]
    [TopologicalSpace E_pts] [DistribMulAction G E_pts]
    [ContinuousAdd E_pts] [ContinuousNeg E_pts] [ContinuousSMul G E_pts] :
    Function.Surjective (cocycleMap_construction k W E_pts G) := by
  intro h

  obtain ⟨α, rfl⟩ := Quotient.exists_rep h

  exact galoisDescent_torsor_of_cocycle k W E_pts G α

/-- Bundled `WCH1Data`: the cocycle map together with its well-definedness, injectivity, and
surjectivity proofs. -/
noncomputable def WCH1Data.mk' (k : Type u) [Field k] (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (G : Type u) [Group G] [TopologicalSpace G]
    [TopologicalSpace E_pts] [DistribMulAction G E_pts]
    [ContinuousAdd E_pts] [ContinuousNeg E_pts] [ContinuousSMul G E_pts] :
    WCH1Data k W E_pts G where
  cocycleMap := cocycleMap_construction k W E_pts G
  cocycleMap_wellDefined := cocycleMap_wellDefined_proof k W E_pts G
  cocycleMap_injective := cocycleMap_injective_proof k W E_pts G
  cocycleMap_surjective := cocycleMap_surjective_proof k W E_pts G

/-- The Weil-Châtelet set is in bijection with $H^1(G, E_{\mathrm{pts}})$: existence of a
bijection $\mathrm{WC}(E/k) \simeq H^1$. -/
theorem wc_equiv_h1 {k : Type u} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
    {E_pts : Type u} [AddCommGroup E_pts]
    {G : Type u} [Group G] [TopologicalSpace G]
    [TopologicalSpace E_pts] [DistribMulAction G E_pts]
    [ContinuousAdd E_pts] [ContinuousNeg E_pts] [ContinuousSMul G E_pts] :
    ∃ (f : WC k W E_pts → H1 G E_pts), Function.Bijective f := by

  let data := WCH1Data.mk' k W E_pts G

  have hwd : ∀ (T₁ T₂ : ETorsor k W E_pts),
      T₁ ≈ T₂ → data.cocycleMap T₁ = data.cocycleMap T₂ :=
    data.cocycleMap_wellDefined

  let f : WC k W E_pts → H1 G E_pts :=
    Quotient.lift data.cocycleMap hwd
  refine ⟨f, ?_, ?_⟩
  ·
    intro a b hab
    induction a using Quotient.ind
    induction b using Quotient.ind
    exact Quotient.sound (data.cocycleMap_injective _ _ hab)
  ·
    intro h
    obtain ⟨T, hT⟩ := data.cocycleMap_surjective h
    exact ⟨Quotient.mk _ T, hT⟩

/-- Explicit bijection $\mathrm{WC}(E/k) \simeq H^1(G, E_{\mathrm{pts}})$ given a choice of
`WCH1Data`. -/
noncomputable def wc_h1_setEquiv {k : Type u} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
    {E_pts : Type u} [AddCommGroup E_pts]
    {G : Type u} [Group G] [TopologicalSpace G]
    [TopologicalSpace E_pts] [DistribMulAction G E_pts]
    [ContinuousAdd E_pts] [ContinuousNeg E_pts] [ContinuousSMul G E_pts]
    (data : WCH1Data k W E_pts G) :
    WC k W E_pts ≃ H1 G E_pts := by
  have hwd : ∀ (T₁ T₂ : ETorsor k W E_pts),
      T₁ ≈ T₂ → data.cocycleMap T₁ = data.cocycleMap T₂ :=
    data.cocycleMap_wellDefined
  let f : WC k W E_pts → H1 G E_pts :=
    Quotient.lift data.cocycleMap hwd
  have hbij : Function.Bijective f := by
    constructor
    · intro a b hab
      induction a using Quotient.ind
      induction b using Quotient.ind
      exact Quotient.sound (data.cocycleMap_injective _ _ hab)
    · intro h
      obtain ⟨T, hT⟩ := data.cocycleMap_surjective h
      exact ⟨Quotient.mk _ T, hT⟩
  exact Equiv.ofBijective f hbij

/-- Transport the abelian group structure on $H^1$ to `WC` via the bijection of
`wc_h1_setEquiv`, making `WC k W E_pts` into an `AddCommGroup`. -/
@[reducible] noncomputable def WC.addCommGroupOfData {k : Type u} [Field k]
    {W : WeierstrassCurve k} [W.IsElliptic]
    {E_pts : Type u} [AddCommGroup E_pts]
    {G : Type u} [Group G] [TopologicalSpace G]
    [TopologicalSpace E_pts] [DistribMulAction G E_pts]
    [ContinuousAdd E_pts] [ContinuousNeg E_pts] [ContinuousSMul G E_pts]
    (data : WCH1Data k W E_pts G) :
    AddCommGroup (WC k W E_pts) :=
  (wc_h1_setEquiv data).addCommGroup

/-- The Weil-Châtelet group is isomorphic, as an additive group, to $H^1(G, E_{\mathrm{pts}})$,
once we transport the group structure via the bijection of `wc_h1_setEquiv`. -/
noncomputable def wc_h1_equiv {k : Type u} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
    {E_pts : Type u} [AddCommGroup E_pts]
    {G : Type u} [Group G] [TopologicalSpace G]
    [TopologicalSpace E_pts] [DistribMulAction G E_pts]
    [ContinuousAdd E_pts] [ContinuousNeg E_pts] [ContinuousSMul G E_pts]
    (data : WCH1Data k W E_pts G) :
    letI := WC.addCommGroupOfData data
    WC k W E_pts ≃+ H1 G E_pts :=
  letI := WC.addCommGroupOfData data
  (wc_h1_setEquiv data).addEquiv

/-- Corollary 26.25: the Weil-Châtelet set $\mathrm{WC}(E/k)$ admits an abelian group structure
under which it is isomorphic to $H^1(\mathrm{Gal}(\bar k/k), E(\bar k))$. -/
theorem corollary_26_25 {k : Type u} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
    {E_pts : Type u} [AddCommGroup E_pts]
    {G : Type u} [Group G] [TopologicalSpace G]
    [TopologicalSpace E_pts] [DistribMulAction G E_pts]
    [ContinuousAdd E_pts] [ContinuousNeg E_pts] [ContinuousSMul G E_pts] :
    ∃ (grp : AddCommGroup (WC k W E_pts)),
      Nonempty (@AddEquiv (WC k W E_pts) (H1 G E_pts) grp.toAdd (inferInstance : Add (H1 G E_pts))) := by


  let data := WCH1Data.mk' k W E_pts G

  exact ⟨WC.addCommGroupOfData data, ⟨wc_h1_equiv data⟩⟩


end
