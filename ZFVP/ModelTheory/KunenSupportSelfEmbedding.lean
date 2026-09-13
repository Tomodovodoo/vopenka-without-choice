import ZFVP.ModelTheory.KunenBoundedJonsson
import ZFVP.ModelTheory.SupportStageEmbeddingAction
import ZFVP.ModelTheory.LimitCriticalPoint
import ZFVP.SetTheory.BoundedRankCriterionWitnesses
import ZFVP.SetTheory.BoundedOrdinalOmega
import ZFVP.SetTheory.FiniteDictionaryReflection

/-! Kunen's contradiction at a rank stage that is only closed under successors.

Every earlier form of Kunen's theorem in this development asks the stage to be in `C(1)` or
`C(2)`, so that the Pi-one properties of the critical sequence transfer along the embedding by
correctness. Stages of the form `V_{lam+omega}`, which is what Bagaria's Theorem 4.3 hands to
Vopenka's principle in the Pi-one case, are never in `C(1)`: a `C(1)` ordinal is a limit of
limits. This module redoes the argument with correctness replaced by the closure properties a
successor-closed rank stage above `omega` really has.

The two Pi-one properties that were transferred by correctness, being an initial ordinal and
satisfying the rank criterion, are here written as bounded formulas with a second argument for a
rank stage that holds all the witnesses. For an ordinal `alpha` the stage `V_{alpha+omega}` holds
every injection of `alpha` into a smaller ordinal and every cofinal map into `alpha` from a set of
small rank, so the bounded readings at that stage say exactly what the unbounded ones say, and a
bounded formula transfers along any coded embedding between transitive sets. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Being an initial ordinal, with the injections quantified inside a second argument. -/
def boundedInitialOrdinalFormula : SetTheorySemisentence 2 :=
  “δ W. !IsOrdinal.dfn δ ∧ ∀ α ∈ δ, ∀ g ∈ W, ¬!boundedInjectionFormula g δ α”

theorem boundedInitialOrdinalFormula_bounded : IsBoundedSetFormula boundedInitialOrdinalFormula :=
  .and (isOrdinalFormula_bounded.subst _)
    (.all (.bvar 0) (.all (.bvar 2) (boundedInjectionFormula_bounded.subst _).neg))

/-- The rank criterion, with the counterexample cofinal maps quantified inside a second
argument. -/
def boundedRankCriterionFormula : SetTheorySemisentence 2 :=
  “α W. !limitAboveOmegaFormula α ∧ ¬!boundedLowRankCofinalWitnessFormula W α”

theorem boundedRankCriterionFormula_bounded : IsBoundedSetFormula boundedRankCriterionFormula :=
  .and (limitAboveOmegaFormula_bounded.subst _)
    (boundedLowRankCofinalWitnessFormula_bounded.subst _).neg

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedInitialOrdinalFormula (δ W : V) :
    boundedInitialOrdinalFormula.Evalb ![δ, W] ↔
      IsOrdinal δ ∧ ∀ α ∈ δ, ∀ g ∈ W, ¬(g ∈ α ^ δ ∧ Injective g) := by
  simp [boundedInitialOrdinalFormula]

theorem eval_boundedRankCriterionFormula (α W : V) :
    boundedRankCriterionFormula.Evalb ![α, W] ↔
      (IsOrdinal α ∧ (ω : V) ∈ α ∧ ∀ x ∈ α, succ x ∈ α) ∧
        ¬boundedLowRankCofinalWitnessFormula.Evalb ![W, α] := by
  simp [boundedRankCriterionFormula, eval_limitAboveOmegaFormula, Semiformula.eval_substs,
    Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]

/-! ### The stage `V_{alpha+omega}` holds all the witnesses -/

/-- Members of an ordinal sit in the rank stage of that ordinal. -/
private theorem mem_hierarchy_of_mem_ordinal {lam x : V} [IsOrdinal lam] (hx : x ∈ lam) :
    x ∈ hierarchy lam := by
  have : IsOrdinal x := IsOrdinal.of_mem hx
  exact ordinal_mem_hierarchy_iff.mpr hx

/-- A set of Kuratowski pairs of members of an ordinal sits in the third stage above it. -/
private theorem pairs_mem_hierarchy_three {lam r : V} [IsOrdinal lam]
    (hr : ∀ p ∈ r, ∃ x ∈ lam, ∃ y ∈ lam, p = ⟨x, y⟩ₖ) :
    r ∈ hierarchy (succ (succ (succ lam))) := by
  rw [hierarchy_succ, mem_power_iff]
  intro p hp
  obtain ⟨x, hx, y, hy, rfl⟩ := hr p hp
  exact kpair_mem_hierarchy_succ_succ (mem_hierarchy_of_mem_ordinal hx)
    (mem_hierarchy_of_mem_ordinal hy)

/-- The third successor of an ordinal is below the ordinal plus `omega`. -/
theorem succ_three_mem_ordinalAdd_omega (lam : V) [IsOrdinal lam] :
    succ (succ (succ lam)) ∈ ordinalAdd lam (ω : V) :=
  ordinalAdd_omega_succ_closed lam (ordinalAdd_omega_succ_closed lam
    (ordinalAdd_omega_succ_closed lam (ordinalAdd_omega_gt lam)))

/-- An internal function between subsets of an ordinal sits in the stage of the ordinal plus
`omega`. -/
theorem function_mem_hierarchy_ordinalAdd_omega {lam X Y r : V} [IsOrdinal lam]
    (hX : X ⊆ lam) (hY : Y ⊆ lam) (hr : r ∈ Y ^ X) : r ∈ hierarchy (ordinalAdd lam (ω : V)) := by
  refine mem_hierarchy_of_mem_stage (succ_three_mem_ordinalAdd_omega lam) ?_
  refine pairs_mem_hierarchy_three (fun p hp ↦ ?_)
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hr p hp)
  exact ⟨x, hX x hx, y, hY y hy, rfl⟩

/-- The bounded reading of `IsInitialOrdinal` at the stage of the ordinal plus `omega` says
exactly that the ordinal is initial. -/
theorem initialOrdinal_iff_bounded {δ : V} [IsOrdinal δ] :
    IsInitialOrdinal δ ↔
      boundedInitialOrdinalFormula.Evalb ![δ, hierarchy (ordinalAdd δ (ω : V))] := by
  rw [eval_boundedInitialOrdinalFormula]
  constructor
  · rintro ⟨ho, hn⟩
    exact ⟨ho, fun α hα g _ hg ↦ hn α hα ⟨g, hg.1, hg.2⟩⟩
  · rintro ⟨ho, hn⟩
    refine ⟨ho, fun α hα hbad ↦ ?_⟩
    obtain ⟨g, hg, hinj⟩ := hbad
    have hαsub : α ⊆ δ := IsOrdinal.toIsTransitive.transitive α hα
    exact hn α hα g
      (function_mem_hierarchy_ordinalAdd_omega (fun _ hx ↦ hx) hαsub hg) ⟨hg, hinj⟩

/-- The bounded reading of the rank criterion at the stage of the ordinal plus `omega` says
exactly that the ordinal satisfies the rank criterion. -/
theorem rankCriterion_iff_bounded {α : V} [IsOrdinal α] :
    IsRankCriterionHeight α ↔
      boundedRankCriterionFormula.Evalb ![α, hierarchy (ordinalAdd α (ω : V))] := by
  rw [eval_boundedRankCriterionFormula]
  constructor
  · rintro ⟨ho, hωα, hs, hn⟩
    exact ⟨⟨ho, hωα, hs⟩, fun hw ↦ boundedLowRankCofinalWitnessFormula_sound hw hn⟩
  · rintro ⟨⟨ho, hωα, hs⟩, hn⟩
    refine ⟨ho, hωα, hs, ?_⟩
    by_contra hbad
    exact hn (boundedLowRankCofinalWitnessFormula_complete
      (fun _ hβ ↦ ordinalAdd_omega_succ_closed α hβ) (ordinalAdd_omega_gt α) hbad)

/-! ### The critical sequence at a successor-closed stage -/

namespace SupportCriticalSequence

variable {θ B f κ : V} [IsOrdinal θ] [IsTransitive B]
  (hω : (ω : V) ∈ θ) (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
  (h : IsCodedMembershipEmbedding (hierarchy θ) B f)
  (hκ : IsCriticalPoint (hierarchy θ) f κ)
  (hlim : criticalLimit f κ ∈ θ)

/-- Every stage of the critical sequence is a subset of the critical limit, whatever the stage
happens to be. -/
theorem iterate_subset_limit (f κ : V) {n : V} (hn : n ∈ (ω : V)) :
    criticalIterate f κ n ⊆ criticalLimit f κ :=
  fun _ hx ↦ (mem_criticalLimit_iff f κ _).mpr ⟨n, hn, hx⟩

include hω hsucc h hκ hlim

/-- The critical limit is an ordinal, since it lies in one. -/
theorem limit_ordinal : IsOrdinal (criticalLimit f κ) := IsOrdinal.of_mem hlim

/-- Each stage of the critical sequence is an ordinal in the source stage that the embedding
moves upwards. The stage stays inside `hierarchy θ` because it is an ordinal below the critical
limit, which is assumed to lie in `θ`. -/
theorem iterate_spec {n : V} (hn : n ∈ (ω : V)) :
    IsOrdinal (criticalIterate f κ n) ∧ criticalIterate f κ n ∈ hierarchy θ ∧
      criticalIterate f κ n ∈ f ‘ (criticalIterate f κ n) := by
  let := hierarchy_transitive θ
  have hlamord : IsOrdinal (criticalLimit f κ) := IsOrdinal.of_mem hlim
  have hstage : ∀ x : V, IsOrdinal x → x ⊆ criticalLimit f κ → x ∈ hierarchy θ := by
    intro x hxo hxs
    let := hxo
    rcases IsOrdinal.subset_iff.mp hxs with he | hl
    · exact ordinal_mem_hierarchy_iff.mpr (he.symm ▸ hlim)
    · exact ordinal_mem_hierarchy_iff.mpr (IsOrdinal.toIsTransitive.mem_trans hl hlim)
  have key : ∀ n ∈ (ω : V), IsOrdinal (criticalIterate f κ n) ∧
      criticalIterate f κ n ∈ hierarchy θ ∧
      criticalIterate f κ n ∈ f ‘ (criticalIterate f κ n) := by
    apply naturalNumber_induction (fun n ↦ IsOrdinal (criticalIterate f κ n) ∧
      criticalIterate f κ n ∈ hierarchy θ ∧
      criticalIterate f κ n ∈ f ‘ (criticalIterate f κ n)) (by definability)
    · simpa using And.intro hκ.ordinal (And.intro hκ.mem_domain (hκ.lt_value h))
    · intro m hm ih
      rw [criticalIterate_succ f κ hm]
      have hsub : f ‘ (criticalIterate f κ m) ⊆ criticalLimit f κ := by
        rw [← criticalIterate_succ f κ hm]
        exact iterate_subset_limit f κ (ω_succ_closed hm)
      have hord : IsOrdinal (f ‘ (criticalIterate f κ m)) := h.value_ordinal ih.1 ih.2.1
      have hmem : f ‘ (criticalIterate f κ m) ∈ hierarchy θ := hstage _ hord hsub
      exact ⟨hord, hmem, (h.value_mem_iff ih.2.1 hmem).mpr ih.2.2⟩
  exact key n hn

theorem iterate_increasing {n : V} (hn : n ∈ (ω : V)) :
    criticalIterate f κ n ∈ criticalIterate f κ (succ n) := by
  rw [criticalIterate_succ f κ hn]
  exact (iterate_spec hω hsucc h hκ hlim hn).2.2

theorem iterate_mem_limit {n : V} (hn : n ∈ (ω : V)) :
    criticalIterate f κ n ∈ criticalLimit f κ :=
  (mem_criticalLimit_iff f κ _).mpr
    ⟨succ n, ω_succ_closed hn, iterate_increasing hω hsucc h hκ hlim hn⟩

theorem criticalPoint_mem_limit : κ ∈ criticalLimit f κ := by
  simpa using iterate_mem_limit hω hsucc h hκ hlim (by simp : (0 : V) ∈ ω)

theorem omega_mem_limit : (ω : V) ∈ criticalLimit f κ := by
  let := hierarchy_isSequenceSupport hω hsucc
  let := IsOrdinal.of_mem hlim
  exact IsOrdinal.toIsTransitive.mem_trans (hκ.omega_lt h)
    (criticalPoint_mem_limit hω hsucc h hκ hlim)

theorem sequence_function : criticalSequence f κ ∈ (criticalLimit f κ) ^ (ω : V) :=
  definableGraph_mem_function_of_mapsTo _ _ _ (by definability)
    (fun _ hn ↦ iterate_mem_limit hω hsucc h hκ hlim hn)

theorem cofinal : IsCofinalMap (criticalLimit f κ) (ω : V) (criticalSequence f κ) := by
  refine ⟨sequence_function hω hsucc h hκ hlim, ?_⟩
  intro x hx
  obtain ⟨n, hn, hxn⟩ := (mem_criticalLimit_iff f κ x).mp hx
  let := (iterate_spec hω hsucc h hκ hlim hn).1
  exact ⟨n, hn, (criticalSequence_value f κ hn).symm ▸ IsOrdinal.toIsTransitive.transitive x hxn⟩

theorem limit_succ_closed {x : V} (hx : x ∈ criticalLimit f κ) : succ x ∈ criticalLimit f κ := by
  let := IsOrdinal.of_mem hlim
  let := IsOrdinal.of_mem hx
  obtain ⟨n, hn, hxn⟩ := (mem_criticalLimit_iff f κ x).mp hx
  let := (iterate_spec hω hsucc h hκ hlim hn).1
  let := (iterate_spec hω hsucc h hκ hlim (ω_succ_closed hn)).1
  have hs : succ x ⊆ criticalIterate f κ n := by
    intro y hy
    rcases mem_succ_iff.mp hy with rfl | hy
    · exact hxn
    · exact IsOrdinal.toIsTransitive.mem_trans hy hxn
  have hsn : succ x ∈ criticalIterate f κ (succ n) := by
    rcases IsOrdinal.subset_iff.mp hs with he | hl
    · exact he.symm ▸ iterate_increasing hω hsucc h hκ hlim hn
    · exact IsOrdinal.toIsTransitive.mem_trans hl (iterate_increasing hω hsucc h hκ hlim hn)
  exact (mem_criticalLimit_iff f κ _).mpr ⟨succ n, ω_succ_closed hn, hsn⟩

end SupportCriticalSequence

/-! ### Transfer of the rank criterion along the embedding -/

/-- A coded embedding commutes with adding `omega` to an ordinal. -/
theorem value_ordinalAdd_omega {A B f α : V} [IsTransitive A] [IsTransitive B]
    (h : IsCodedMembershipEmbedding A B f) (hα : IsOrdinal α) (hαA : α ∈ A)
    (hsA : ordinalAdd α (ω : V) ∈ A) :
    f ‘ (ordinalAdd α (ω : V)) = ordinalAdd (f ‘ α) (ω : V) := by
  have h0 := (eval_boundedOrdinalOmegaFormula (ordinalAdd α (ω : V)) α).mpr ⟨hα, rfl⟩
  have he := (h.bounded_formula_iff boundedOrdinalOmegaFormula_bounded
    ![ordinalAdd α (ω : V), α]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hsA, hαA])).mp h0
  have hvec : (fun i ↦ f ‘ ((![ordinalAdd α (ω : V), α] : Fin 2 → V) i)) =
      ![f ‘ (ordinalAdd α (ω : V)), f ‘ α] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
  rw [hvec] at he
  exact ((eval_boundedOrdinalOmegaFormula _ _).mp he).2

/-- A rank stage closed under successors moves the rank criterion along a coded self-embedding.
The witnesses that would refute the criterion at `alpha` all lie in `V_{alpha+omega}`, and the
embedding sends that stage to `V_{f(alpha)+omega}`. -/
theorem support_value_rankCriterion {θ f α : V} [IsOrdinal θ]
    (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
    (h : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy θ) f)
    (hα : IsOrdinal α) (hαθ : α ∈ θ) (hAθ : ordinalAdd α (ω : V) ∈ θ)
    (hr : IsRankCriterionHeight α) : IsRankCriterionHeight (f ‘ α) := by
  let := hα
  let := hierarchy_transitive θ
  have hαH : α ∈ hierarchy θ := ordinal_subset_hierarchy θ _ hαθ
  have hAH : ordinalAdd α (ω : V) ∈ hierarchy θ := ordinal_subset_hierarchy θ _ hAθ
  have hWH : hierarchy (ordinalAdd α (ω : V)) ∈ hierarchy θ := hierarchy_mem hAθ
  have hb := rankCriterion_iff_bounded.mp hr
  have he := (h.bounded_formula_iff boundedRankCriterionFormula_bounded
    ![α, hierarchy (ordinalAdd α (ω : V))]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hαH, hWH])).mp hb
  have hvec : (fun i ↦ f ‘ ((![α, hierarchy (ordinalAdd α (ω : V))] : Fin 2 → V) i)) =
      ![f ‘ α, hierarchy (ordinalAdd (f ‘ α) (ω : V))] := by
    funext i
    refine Fin.cases rfl (fun j ↦ Fin.cases ?_ (fun t ↦ Fin.elim0 t) j) i
    show f ‘ (hierarchy (ordinalAdd α (ω : V))) = hierarchy (ordinalAdd (f ‘ α) (ω : V))
    rw [(limitRankEmbedding_value_hierarchy hsucc hsucc h inferInstance hAH).2,
      value_ordinalAdd_omega h hα hαH hAH]
  rw [hvec] at he
  let := h.value_ordinal hα hαH
  exact rankCriterion_iff_bounded.mpr he

/-- An ordinal with no cofinal maps from sets of smaller rank is an initial ordinal. -/
theorem initialOrdinal_of_noLowRankCofinalMaps {κ : V} [IsOrdinal κ]
    (hn : NoLowRankCofinalMaps κ) : IsInitialOrdinal κ := by
  refine ⟨inferInstance, ?_⟩
  intro α hα hbad
  obtain ⟨g, hg, hr⟩ := surjection_of_injection hbad ⟨α, hα⟩
  let := IsFunction.of_mem hg
  refine hn α (ordinal_subset_hierarchy κ _ hα) g ⟨hg, ?_⟩
  intro β hβ
  obtain ⟨x, hxβ⟩ := mem_range_iff.mp (hr.symm ▸ hβ)
  exact ⟨x, (mem_of_mem_functions hg hxβ).1, (value_eq_of_kpair_mem hxβ).symm ▸ subset_refl β⟩

/-- A rank criterion height is an initial ordinal. -/
theorem IsRankCriterionHeight.initialOrdinal {κ : V} (hκ : IsRankCriterionHeight κ) :
    IsInitialOrdinal κ := by
  let := hκ.1
  exact initialOrdinal_of_noLowRankCofinalMaps hκ.2.2.2

/-! ### The critical limit of a self-embedding of a successor-closed stage -/

namespace SupportCriticalSequence

variable {θ f κ : V} [IsOrdinal θ]
  (hω : (ω : V) ∈ θ) (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
  (h : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy θ) f)
  (hκ : IsCriticalPoint (hierarchy θ) f κ)
  (hlim : criticalLimit f κ ∈ θ)

include hω hsucc h hκ hlim

/-- Each stage of the critical sequence has room for `omega` more ordinals below `θ`. -/
theorem iterate_add_omega_mem {n : V} (hn : n ∈ (ω : V)) :
    ordinalAdd (criticalIterate f κ n) (ω : V) ∈ θ := by
  let := hierarchy_transitive θ
  let := IsOrdinal.of_mem hlim
  let := (iterate_spec hω hsucc h hκ hlim hn).1
  have hsub : ordinalAdd (criticalIterate f κ n) (ω : V) ⊆ criticalLimit f κ :=
    ordinalAdd_omega_subset_of_successor_closed (iterate_mem_limit hω hsucc h hκ hlim hn)
      (fun _ hx ↦ limit_succ_closed hω hsucc h hκ hlim hx)
  rcases IsOrdinal.subset_iff.mp hsub with he | hl
  · exact he.symm ▸ hlim
  · exact IsOrdinal.toIsTransitive.mem_trans hl hlim

/-- Every stage of the critical sequence satisfies the rank criterion. -/
theorem iterate_rankCriterion {n : V} (hn : n ∈ (ω : V)) :
    IsRankCriterionHeight (criticalIterate f κ n) := by
  let := hierarchy_isSequenceSupport hω hsucc
  let := hierarchy_transitive θ
  have hall : ∀ n ∈ (ω : V), IsRankCriterionHeight (criticalIterate f κ n) := by
    apply naturalNumber_induction (fun n ↦ IsRankCriterionHeight (criticalIterate f κ n))
      (by definability)
    · simpa using limitRankEmbedding_criticalPoint_rankCriterion hsucc h hκ (hκ.omega_lt h)
    · intro m hm ih
      let := (iterate_spec hω hsucc h hκ hlim hm).1
      rw [criticalIterate_succ f κ hm]
      exact support_value_rankCriterion hsucc h inferInstance
        (ordinal_mem_hierarchy_iff.mp (iterate_spec hω hsucc h hκ hlim hm).2.1)
        (iterate_add_omega_mem hω hsucc h hκ hlim hm) ih
  exact hall n hn

theorem iterate_initial {n : V} (hn : n ∈ (ω : V)) :
    IsInitialOrdinal (criticalIterate f κ n) :=
  (iterate_rankCriterion hω hsucc h hκ hlim hn).initialOrdinal

/-- The critical limit is an initial ordinal. -/
theorem limit_initial : IsInitialOrdinal (criticalLimit f κ) := by
  let := hierarchy_transitive θ
  let := IsOrdinal.of_mem hlim
  refine ⟨inferInstance, ?_⟩
  intro α hα hinj
  obtain ⟨n, hn, hαn⟩ := (mem_criticalLimit_iff f κ α).mp hα
  have hsub : criticalIterate f κ n ⊆ criticalLimit f κ :=
    IsOrdinal.toIsTransitive.transitive _ (iterate_mem_limit hω hsucc h hκ hlim hn)
  exact (iterate_initial hω hsucc h hκ hlim hn).2 α hαn ((cardLE_of_subset hsub).trans hinj)

theorem iterate_inaccessible {n : V} (hn : n ∈ (ω : V)) :
    IsChoicelessInaccessible (criticalIterate f κ n) :=
  isChoicelessInaccessible_iff_rankCriterionHeight.mpr
    (iterate_rankCriterion hω hsucc h hκ hlim hn)

/-- The critical limit is a strong limit. -/
theorem limit_power_cardLE (hAC : InternalChoice V) {α : V} (hα : α ∈ criticalLimit f κ) :
    ℘ α ≤# criticalLimit f κ := by
  obtain ⟨n, hn, hαn⟩ := (mem_criticalLimit_iff f κ α).mp hα
  let := hierarchy_transitive θ
  let := IsOrdinal.of_mem hlim
  have hsub : criticalIterate f κ n ⊆ criticalLimit f κ :=
    IsOrdinal.toIsTransitive.transitive _ (iterate_mem_limit hω hsucc h hκ hlim hn)
  exact ((iterate_inaccessible hω hsucc h hκ hlim hn).power_cardLE hAC hαn).trans
    (cardLE_of_subset hsub)

/-- Under choice the critical limit carries an omega-Jonsson function inside the stage. -/
theorem exists_omegaJonsson_criticalLimit (hAC : InternalChoice V) :
    ∃ F ∈ hierarchy θ, IsOmegaJonsson F (criticalLimit f κ) := by
  let := hierarchy_transitive θ
  let := IsOrdinal.of_mem hlim
  have hlimH : criticalLimit f κ ∈ hierarchy θ := ordinal_mem_hierarchy_iff.mpr hlim
  obtain ⟨F, hFsub, hFJ⟩ := exists_omegaJonsson hAC (limit_initial hω hsucc h hκ hlim)
    (omega_mem_limit hω hsucc h hκ hlim)
    ⟨criticalSequence f κ, sequence_function hω hsucc h hκ hlim, cofinal hω hsucc h hκ hlim⟩
    (fun _ hα ↦ limit_power_cardLE hω hsucc h hκ hlim hAC hα)
  exact ⟨F, subset_mem_hierarchy_limit hsucc
    (prod_mem_hierarchy_limit hsucc (power_mem_hierarchy_limit hsucc hlimH) hlimH) hFsub, hFJ⟩

end SupportCriticalSequence

/-! ### The critical limit is fixed -/

/-- The critical limit of a coded embedding between two rank stages is fixed, as soon as it lies
inside the source stage. The critical sequence is a map from `omega` into the source stage that
`f` sends to the shifted sequence, and `f` fixes `omega` pointwise, so the value of `f` at the
supremum of the range is the supremum of the range of the image. -/
theorem criticalLimit_value_eq {θ θ' f κ : V} [IsOrdinal θ] [IsOrdinal θ']
    (hω : (ω : V) ∈ θ) (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
    (h : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy θ') f)
    (hκ : IsCriticalPoint (hierarchy θ) f κ)
    (h_in_stage : criticalLimit f κ ∈ θ) :
    f ‘ (criticalLimit f κ) = criticalLimit f κ := by
  let := hierarchy_transitive θ
  let := hierarchy_transitive θ'
  let : IsSequenceSupport (hierarchy θ) := hierarchy_isSequenceSupport hω hsucc
  let := IsOrdinal.of_mem h_in_stage
  have hlimH : criticalLimit f κ ∈ hierarchy θ := ordinal_mem_hierarchy_iff.mpr h_in_stage
  have hωH : (ω : V) ∈ hierarchy θ := IsCodingSupport.omega_mem
  have hseq : criticalSequence f κ ∈ hierarchy θ :=
    (hierarchy_transitive θ).mem_trans
      (SupportCriticalSequence.sequence_function hω hsucc h hκ h_in_stage)
      (function_mem_hierarchy_limit hsucc hωH hlimH)
  have himg : ∀ n ∈ (ω : V), (f ‘ (criticalSequence f κ)) ‘ n = criticalIterate f κ (succ n) := by
    intro n hn
    have hv := h.value_apply hseq hωH (criticalSequence_isFunction f κ)
      (criticalSequence_domain f κ) hn
    rw [h.value_natural hn, criticalSequence_value f κ hn] at hv
    exact hv.trans (criticalIterate_succ f κ hn).symm
  have hmap := h.value_cofinalMap hseq hωH hlimH
    (SupportCriticalSequence.cofinal hω hsucc h hκ h_in_stage)
  rw [h.value_omega hωH] at hmap
  apply SetTheory.subset_antisymm
  · intro x hx
    obtain ⟨n, hn, hxn⟩ := hmap.2 x hx
    rw [himg n hn] at hxn
    let := (SupportCriticalSequence.iterate_spec hω hsucc h hκ h_in_stage (ω_succ_closed hn)).1
    let := h.value_ordinal inferInstance hlimH
    let := IsOrdinal.of_mem hx
    rcases IsOrdinal.subset_iff.mp hxn with he | hl
    · exact he.symm ▸
        SupportCriticalSequence.iterate_mem_limit hω hsucc h hκ h_in_stage (ω_succ_closed hn)
    · exact IsOrdinal.toIsTransitive.mem_trans hl
        (SupportCriticalSequence.iterate_mem_limit hω hsucc h hκ h_in_stage (ω_succ_closed hn))
  · exact h.ordinal_subset_value inferInstance hlimH

/-! ### Kunen's contradiction at a successor-closed stage -/

/-- Domains of members of a successor-closed rank stage stay in the stage. -/
theorem domain_mem_hierarchy_limit {θ x : V} [IsOrdinal θ] (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
    (hx : x ∈ hierarchy θ) : domain x ∈ hierarchy θ := by
  apply subset_mem_hierarchy_limit hsucc
    (sUnion_mem_hierarchy_limit hsucc (sUnion_mem_hierarchy_limit hsucc hx))
  intro z hz
  exact (mem_sep_iff.mp hz).1

/-- Enlarging the codomain of an internal function. -/
private theorem mem_function_mono' {g X Y Y' : V} (hg : g ∈ Y ^ X) (hY : Y ⊆ Y') : g ∈ Y' ^ X := by
  refine mem_function_iff.mpr ⟨fun p hp ↦ ?_, (mem_function_iff.mp hg).2⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp ((mem_function_iff.mp hg).1 p hp)
  exact kpair_mem_iff.mpr ⟨hx, hY y hy⟩

/-- The image of an omega-Jonsson function under a coded self-embedding of a successor-closed
rank stage is omega-Jonsson for the image of the ordinal, provided the stage reaches past `lam`
by three successors. -/
theorem IsOmegaJonsson.value_support {θ f F lam : V} [IsOrdinal θ]
    (hω : (ω : V) ∈ θ) (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
    (h : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy θ) f)
    (hF : F ∈ hierarchy θ) (hlam : lam ∈ hierarchy θ) (hlamord : IsOrdinal lam)
    (hωlam : (ω : V) ⊆ lam) (h2 : succ (succ lam) ∈ θ) (hJ : IsOmegaJonsson F lam) :
    IsOmegaJonsson (f ‘ F) (f ‘ lam) := by
  let := hlamord
  let := hierarchy_transitive θ
  have hωθ : (ω : V) ∈ hierarchy θ := ordinal_subset_hierarchy θ _ hω
  have h1δ : succ lam ∈ θ := IsOrdinal.toIsTransitive.mem_trans (mem_succ_self (succ lam)) h2
  have h3δ : succ (succ (succ lam)) ∈ θ := hsucc _ h2
  have h1H : succ lam ∈ hierarchy θ := ordinal_mem_hierarchy_iff.mpr h1δ
  have h2H : succ (succ lam) ∈ hierarchy θ := ordinal_mem_hierarchy_iff.mpr h2
  have h3H : succ (succ (succ lam)) ∈ hierarchy θ := ordinal_mem_hierarchy_iff.mpr h3δ
  have hvsucc : f ‘ (succ (succ (succ lam))) = succ (succ (succ (f ‘ lam))) := by
    rw [h.value_succ h2H h3H, h.value_succ h1H h2H, h.value_succ hlam h1H]
  have hvW := (limitRankEmbedding_value_hierarchy hsucc hsucc h
    (IsOrdinal.succ (h := IsOrdinal.succ (h := IsOrdinal.succ))) h3H).2
  rw [hvsucc] at hvW
  have hvord : IsOrdinal (f ‘ lam) :=
    (limitRankEmbedding_value_hierarchy hsucc hsucc h hlamord hlam).1
  have hvω : (ω : V) ⊆ f ‘ lam := by
    have := h.value_subset hωθ hlam hωlam
    rwa [h.value_omega hωθ] at this
  have hv : ∀ i, (![F, lam, hierarchy (succ (succ (succ lam)))] : Fin 3 → V) i ∈ hierarchy θ := by
    intro i
    refine Fin.cases hF (fun j ↦ Fin.cases hlam (fun t ↦ Fin.cases ?_ (fun s ↦ Fin.elim0 s) t) j) i
    exact hierarchy_mem h3δ
  have hiff := h.bounded_defined_iff boundedOmegaJonssonFormula_bounded
    (fun v ↦ BoundedOmegaJonsson (v 0) (v 1) (v 2))
    ![F, lam, hierarchy (succ (succ (succ lam)))] hv
  have himg := hiff.mp ((boundedOmegaJonsson_iff hlamord hωlam).mpr hJ)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at himg
  rw [show (![F, lam, hierarchy (succ (succ (succ lam)))] : Fin 3 → V) 2 =
    hierarchy (succ (succ (succ lam))) from rfl, hvW] at himg
  exact (boundedOmegaJonsson_iff hvord hvω).mp himg

/-- Kunen's contradiction at a rank stage closed under successors: a coded self-embedding whose
critical limit plus two successors sits inside the stage rules out an omega-Jonsson function for
that limit inside the stage. -/
theorem false_of_omegaJonsson_criticalLimit_support {θ f κ F : V} [IsOrdinal θ]
    (hω : (ω : V) ∈ θ) (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
    (h : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy θ) f)
    (hκ : IsCriticalPoint (hierarchy θ) f κ)
    (hlim2 : succ (succ (criticalLimit f κ)) ∈ θ)
    (hF : F ∈ hierarchy θ) (hJ : IsOmegaJonsson F (criticalLimit f κ)) : False := by
  let := hierarchy_transitive θ
  set lam : V := criticalLimit f κ with hlamdef
  have hωH : (ω : V) ∈ hierarchy θ := ordinal_subset_hierarchy θ _ hω
  have hlamθ : lam ∈ θ :=
    IsOrdinal.toIsTransitive.mem_trans (mem_succ_self lam)
      (IsOrdinal.toIsTransitive.mem_trans (mem_succ_self (succ lam)) hlim2)
  have hlamord : IsOrdinal lam := IsOrdinal.of_mem hlamθ
  let := hlamord
  have hlim : lam ∈ hierarchy θ := ordinal_mem_hierarchy_iff.mpr hlamθ
  have hωlam : (ω : V) ⊆ lam := IsOrdinal.toIsTransitive.transitive _
    (SupportCriticalSequence.omega_mem_limit hω hsucc h hκ hlamθ)
  have hfix : f ‘ lam = lam := criticalLimit_value_eq hω hsucc h hκ hlamθ
  have hκlam : κ ∈ lam := SupportCriticalSequence.criticalPoint_mem_limit hω hsucc h hκ hlamθ
  -- the pointwise image of the fixed limit
  set A : V := imageSet f lam with hAdef
  have hAsub : A ⊆ lam := h.imageSet_subset_of_value_eq hlim hfix
  have hAcard : lam ≤# A := h.cardLE_imageSet hlim
  -- the restriction of `f` to `lam` and its inverse
  have hr : f ↾ lam ∈ A ^ lam := h.restrict_mem_function hlim
  have hrinj : Injective (f ↾ lam) := h.restrict_injective
  have hrange : range (f ↾ lam) = A := rfl
  have hc : converseGraph (f ↾ lam) ∈ lam ^ A := by
    simpa only [hrange] using converseGraph_mem_function hr hrinj
  set c : V := converseGraph (f ↾ lam) with hcdef
  have hlamdom : lam ⊆ domain f := h.subset_domain hlim
  have hrval : ∀ ξ ∈ lam, (f ↾ lam) ‘ ξ = f ‘ ξ := by
    let := IsFunction.of_mem h.function
    exact fun ξ hξ ↦ value_restrict (hlamdom ξ hξ) hξ
  -- the image function is omega-Jonsson for the same limit
  have hJ' : IsOmegaJonsson (f ‘ F) lam := by
    have := hJ.value_support hω hsucc h hF hlim hlamord hωlam hlim2
    rwa [hfix] at this
  obtain ⟨u, hu, huA, ⟨e, he, hre⟩, hval⟩ := hJ'.2.2 A hAsub hAcard κ hκlam
  -- pull the enumeration of `u` back along the inverse of `f ↾ lam`
  let := IsFunction.of_mem he
  have heA : e ∈ A ^ (ω : V) := mem_function_mono' he huA
  have hgb : compose e c ∈ lam ^ (ω : V) := compose_function heA hc
  let := IsFunction.of_mem hgb
  set b : V := range (compose e c) with hbdef
  have hbfun : compose e c ∈ b ^ (ω : V) :=
    function_mem_of_isFunction' (domain_eq_of_mem_function hgb) rfl
  have hblam : b ⊆ lam := range_subset_of_mem_function hgb
  have hbδ : b ∈ hierarchy θ := subset_mem_hierarchy_limit hsucc hlim hblam
  have hgbδ : compose e c ∈ hierarchy θ :=
    (hierarchy_transitive θ).mem_trans hbfun (function_mem_hierarchy_limit hsucc hωH hbδ)
  -- values of the pulled back enumeration
  have hgbval : ∀ n ∈ (ω : V), (compose e c) ‘ n = c ‘ (e ‘ n) :=
    fun n hn ↦ value_compose_of_mem_function heA hc hn
  -- `f` maps `b` onto `u` pointwise
  have himg : imageSet f b = u := by
    apply SetTheory.subset_antisymm
    · intro y hy
      obtain ⟨ξ, hξ, rfl⟩ := (h.mem_imageSet_value_iff hbδ y).mp hy
      obtain ⟨n, hn⟩ := mem_range_iff.mp hξ
      have hnω : n ∈ (ω : V) := by
        simpa [domain_eq_of_mem_function hgb] using mem_domain_of_kpair_mem hn
      have hξv : ξ = c ‘ (e ‘ n) := (value_eq_of_kpair_mem hn).symm.trans (hgbval n hnω)
      have hen : e ‘ n ∈ u := function_value_mem he hnω
      have hrec : (f ↾ lam) ‘ (c ‘ (e ‘ n)) = e ‘ n :=
        value_converseGraph_value hr hrinj (by rw [hrange]; exact huA _ hen)
      rw [hξv, ← hrval _ (function_value_mem hc (huA _ hen)), hrec]
      exact hen
    · intro y hy
      obtain ⟨n, hn⟩ := mem_range_iff.mp (hre.symm ▸ hy)
      have hnω : n ∈ (ω : V) := by
        simpa [domain_eq_of_mem_function he] using mem_domain_of_kpair_mem hn
      have hyv : e ‘ n = y := value_eq_of_kpair_mem hn
      have hcy : c ‘ y ∈ lam := function_value_mem hc (huA _ (hyv ▸ function_value_mem he hnω))
      refine (h.mem_imageSet_value_iff hbδ y).mpr ⟨c ‘ y, ?_, ?_⟩
      · rw [hbdef, ← hyv, ← hgbval n hnω]
        exact value_mem_range hgb (by simpa [domain_eq_of_mem_function hgb] using hnω)
      · rw [← hrval _ hcy]
        exact value_converseGraph_value hr hrinj
          (by rw [hrange, ← hyv]; exact huA _ (function_value_mem he hnω))
  have hvb : f ‘ b = u := by
    rw [h.value_eq_imageSet_of_omega_surjection hωH hbδ hgbδ hbfun rfl]
    exact himg
  -- transfer membership in the domain back through `f`
  have hFfun : IsFunction F := hJ.1
  have hdomF : domain F ∈ hierarchy θ := domain_mem_hierarchy_limit hsucc hF
  have hdomval := h.value_function_domain hF hdomF hFfun rfl
  have hbdom : b ∈ domain F := by
    have : f ‘ b ∈ f ‘ (domain F) := by rw [hvb]; rw [hdomval.2] at hu; exact hu
    exact (h.value_mem_iff hbδ hdomF).mp this
  -- the critical point lands in the pointwise image of the limit
  have happ : (f ‘ F) ‘ (f ‘ b) = f ‘ (F ‘ b) :=
    h.value_apply hF hdomF hFfun rfl hbdom
  have hκv : f ‘ (F ‘ b) = κ := by rw [← happ, hvb]; exact hval
  have hFb : F ‘ b ∈ lam := (hJ.2.1 b hbdom).2
  exact criticalPoint_not_mem_imageSet h hκ hlamord hlim
    ((h.mem_imageSet_value_iff hlim κ).mpr ⟨F ‘ b, hFb, hκv⟩)

/-- Kunen's contradiction under choice at a rank stage closed under successors: no coded
self-embedding of `V_θ` has its critical limit plus two successors inside `θ`. -/
theorem false_of_support_selfEmbedding (hAC : InternalChoice V) {θ f κ : V} [IsOrdinal θ]
    (hω : (ω : V) ∈ θ) (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
    (h : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy θ) f)
    (hκ : IsCriticalPoint (hierarchy θ) f κ)
    (hlim2 : succ (succ (criticalLimit f κ)) ∈ θ) : False := by
  have hlamθ : criticalLimit f κ ∈ θ :=
    IsOrdinal.toIsTransitive.mem_trans (mem_succ_self (criticalLimit f κ))
      (IsOrdinal.toIsTransitive.mem_trans (mem_succ_self (succ (criticalLimit f κ))) hlim2)
  obtain ⟨F, hF, hFJ⟩ :=
    SupportCriticalSequence.exists_omegaJonsson_criticalLimit hω hsucc h hκ hlamθ hAC
  exact false_of_omegaJonsson_criticalLimit_support hω hsucc h hκ hlim2 hF hFJ

/-! ### Restriction to the stage of the critical limit -/

/-- Restriction of a coded embedding between successor-closed rank stages to a smaller
successor-closed rank stage. The truth table for the smaller stage is a subset of that stage
times the formula family, so it already lies in the source stage; no correctness and no ZF model
condition on the smaller stage is needed. -/
theorem supportEmbedding_restrict_stage {θ θ' f η : V} [IsOrdinal θ] [IsOrdinal θ'] [IsOrdinal η]
    (hω : (ω : V) ∈ θ) (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
    (hω' : (ω : V) ∈ θ') (hsucc' : ∀ ξ ∈ θ', succ ξ ∈ θ')
    (h : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy θ') f)
    (hωη : (ω : V) ∈ η) (hsuccη : ∀ ξ ∈ η, succ ξ ∈ η) (hηθ : η ∈ θ)
    (hFη : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy η) :
    IsCodedMembershipEmbedding (hierarchy η) (hierarchy (f ‘ η)) (f ↾ (hierarchy η)) := by
  let := hierarchy_transitive θ
  let := hierarchy_transitive θ'
  let := hierarchy_isSequenceSupport hω hsucc
  let := hierarchy_isSequenceSupport hωη hsuccη
  have hVη : hierarchy η ∈ hierarchy θ := hierarchy_mem hηθ
  have hFθ : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy θ :=
    (hierarchy_transitive θ).mem_trans hFη hVη
  have hr := h.restrict_of_truthTable hVη hFη (identity_mem_hierarchy_limit hsuccη hFη)
    (membershipModelTruthTable_mem_hierarchy_limit hsucc (ordinal_subset_hierarchy θ _ hω)
      hVη hFθ)
    (membershipModelTruthTable_correct _)
  rwa [(supportEmbedding_value_hierarchy hω hsucc hω' hsucc' h inferInstance
    (ordinal_subset_hierarchy θ _ hηθ)).2] at hr

/-- Every critical iterate stays below a fixed ordinal above the critical point. -/
theorem criticalIterate_mem_fixed_ordinal_support {θ B f η κ : V} [IsOrdinal θ] [IsTransitive B]
    (h : IsCodedMembershipEmbedding (hierarchy θ) B f)
    (hηθ : η ∈ hierarchy θ) (hfix : f ‘ η = η) (hκη : κ ∈ η) :
    ∀ n ∈ (ω : V), criticalIterate f κ n ∈ η := by
  let := hierarchy_transitive θ
  have hsub : η ⊆ hierarchy θ := IsTransitive.transitive η hηθ
  apply naturalNumber_induction (fun n ↦ criticalIterate f κ n ∈ η) (by definability)
  · simpa using hκη
  · intro n hn ih
    rw [criticalIterate_succ f κ hn, ← hfix]
    exact (h.value_mem_iff (hsub _ ih) hηθ).mpr ih

/-- The restriction to the stage of a fixed ordinal produces the same critical iterates. -/
theorem criticalIterate_restrict_eq {θ B f η κ : V} [IsOrdinal θ] [IsOrdinal η] [IsTransitive B]
    (h : IsCodedMembershipEmbedding (hierarchy θ) B f)
    (hηθ : η ∈ hierarchy θ) (hfix : f ‘ η = η) (hκη : κ ∈ η) :
    ∀ n ∈ (ω : V), criticalIterate (f ↾ (hierarchy η)) κ n = criticalIterate f κ n := by
  let := hierarchy_transitive θ
  have : IsFunction f := IsFunction.of_mem h.function
  have hsub : η ⊆ hierarchy θ := IsTransitive.transitive η hηθ
  have hstage : ∀ x ∈ η, x ∈ hierarchy η := by
    intro x hx
    let := IsOrdinal.of_mem hx
    exact ordinal_mem_hierarchy_iff.mpr hx
  have hbelow := criticalIterate_mem_fixed_ordinal_support h hηθ hfix hκη
  apply naturalNumber_induction
    (fun n ↦ criticalIterate (f ↾ (hierarchy η)) κ n = criticalIterate f κ n) (by definability)
  · simp
  · intro n hn ih
    rw [criticalIterate_succ (f ↾ (hierarchy η)) κ hn, criticalIterate_succ f κ hn, ih]
    exact value_restrict
      (by rw [domain_eq_of_mem_function h.function]; exact hsub _ (hbelow n hn))
      (hstage _ (hbelow n hn))

/-- The restriction to the stage of a fixed ordinal has the same critical limit. -/
theorem criticalLimit_restrict_eq {θ B f η κ : V} [IsOrdinal θ] [IsOrdinal η] [IsTransitive B]
    (h : IsCodedMembershipEmbedding (hierarchy θ) B f)
    (hηθ : η ∈ hierarchy θ) (hfix : f ‘ η = η) (hκη : κ ∈ η) :
    criticalLimit (f ↾ (hierarchy η)) κ = criticalLimit f κ := by
  have hit := criticalIterate_restrict_eq h hηθ hfix hκη
  apply mem_ext
  intro x
  rw [mem_criticalLimit_iff, mem_criticalLimit_iff]
  constructor
  · rintro ⟨n, hn, hx⟩
    exact ⟨n, hn, hit n hn ▸ hx⟩
  · rintro ⟨n, hn, hx⟩
    exact ⟨n, hn, (hit n hn).symm ▸ hx⟩

/-- Kunen's contradiction in the shape the Pi-one case of Bagaria's Theorem 4.3 needs: under
choice there is no coded embedding of `V_{lam+omega}` into `V_{lam'+omega}` whose critical limit
lies below `lam`. The critical limit is fixed, hence so is the ordinal `criticalLimit + omega`,
and the restriction of the embedding to that stage is a self-embedding to which Kunen's theorem
applies. -/
theorem false_of_criticalLimit_mem (hAC : InternalChoice V) {lam lam' f κ : V}
    [IsOrdinal lam] [IsOrdinal lam']
    (hωlam : (ω : V) ∈ lam) (hsucclam : ∀ ξ ∈ lam, succ ξ ∈ lam)
    (hωlam' : (ω : V) ∈ lam') (hsucclam' : ∀ ξ ∈ lam', succ ξ ∈ lam')
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy (ordinalAdd (ω : V) (ω : V)))
    (h : IsCodedMembershipEmbedding (hierarchy (ordinalAdd lam (ω : V)))
      (hierarchy (ordinalAdd lam' (ω : V))) f)
    (hκ : IsCriticalPoint (hierarchy (ordinalAdd lam (ω : V))) f κ)
    (hδ : criticalLimit f κ ∈ lam) : False := by
  set θ : V := ordinalAdd lam (ω : V) with hθdef
  set θ' : V := ordinalAdd lam' (ω : V) with hθ'def
  let := hierarchy_transitive θ
  let := hierarchy_transitive θ'
  let := hκ.ordinal
  have hlamθ : lam ∈ θ := ordinalAdd_omega_gt lam
  have hω : (ω : V) ∈ θ := IsOrdinal.toIsTransitive.mem_trans hωlam hlamθ
  have hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ := fun _ hξ ↦ ordinalAdd_omega_succ_closed lam hξ
  have hω' : (ω : V) ∈ θ' :=
    IsOrdinal.toIsTransitive.mem_trans hωlam' (ordinalAdd_omega_gt lam')
  have hsucc' : ∀ ξ ∈ θ', succ ξ ∈ θ' := fun _ hξ ↦ ordinalAdd_omega_succ_closed lam' hξ
  -- the critical limit and the stage it generates
  set lam0 : V := criticalLimit f κ with hlam0def
  have hlam0θ : lam0 ∈ θ := IsOrdinal.toIsTransitive.mem_trans hδ hlamθ
  let := IsOrdinal.of_mem hlam0θ
  have hlam0H : lam0 ∈ hierarchy θ := ordinal_mem_hierarchy_iff.mpr hlam0θ
  have hfix0 : f ‘ lam0 = lam0 := criticalLimit_value_eq hω hsucc h hκ hlam0θ
  have hωlam0 : (ω : V) ∈ lam0 := SupportCriticalSequence.omega_mem_limit hω hsucc h hκ hlam0θ
  have hκlam0 : κ ∈ lam0 :=
    SupportCriticalSequence.criticalPoint_mem_limit hω hsucc h hκ hlam0θ
  have hsucclam0 : ∀ ξ ∈ lam0, succ ξ ∈ lam0 :=
    fun _ hξ ↦ SupportCriticalSequence.limit_succ_closed hω hsucc h hκ hlam0θ hξ
  set η : V := ordinalAdd lam0 (ω : V) with hηdef
  have hlam0η : lam0 ∈ η := ordinalAdd_omega_gt lam0
  have hηsub : η ⊆ lam := ordinalAdd_omega_subset_of_successor_closed hδ hsucclam
  have hηθ : η ∈ θ := by
    rcases IsOrdinal.subset_iff.mp hηsub with he | hl
    · exact he.symm ▸ hlamθ
    · exact IsOrdinal.toIsTransitive.mem_trans hl hlamθ
  have hηH : η ∈ hierarchy θ := ordinal_mem_hierarchy_iff.mpr hηθ
  have hωη : (ω : V) ∈ η := IsOrdinal.toIsTransitive.mem_trans hωlam0 hlam0η
  have hsuccη : ∀ ξ ∈ η, succ ξ ∈ η := fun _ hξ ↦ ordinalAdd_omega_succ_closed lam0 hξ
  have hκη : κ ∈ η := IsOrdinal.toIsTransitive.mem_trans hκlam0 hlam0η
  -- the embedding fixes that stage
  have hfix : f ‘ η = η := by
    rw [hηdef, value_ordinalAdd_omega h inferInstance hlam0H hηH, hfix0]
  -- the formula family sits inside the smaller stage
  have hFη : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy η := by
    refine hierarchy_mono (fun x hx ↦ ?_) _ hF
    exact subset_ordinalAdd lam0 (ω : V) x
      (ordinalAdd_omega_subset_of_successor_closed hωlam0 hsucclam0 x hx)
  -- the restriction is a self-embedding of the smaller stage
  have hg : IsCodedMembershipEmbedding (hierarchy η) (hierarchy η) (f ↾ (hierarchy η)) := by
    have hr := supportEmbedding_restrict_stage hω hsucc hω' hsucc' h hωη hsuccη hηθ hFη
    rwa [hfix] at hr
  have hκg : IsCriticalPoint (hierarchy η) (f ↾ (hierarchy η)) κ := by
    let := hierarchy_transitive η
    exact hκ.restrict h.function
      (IsTransitive.transitive (hierarchy η) (hierarchy_mem hηθ))
      (ordinal_mem_hierarchy_iff.mpr hκη)
  have heq : criticalLimit (f ↾ (hierarchy η)) κ = lam0 :=
    criticalLimit_restrict_eq h hηH hfix hκη
  refine false_of_support_selfEmbedding hAC hωη hsuccη hg hκg ?_
  rw [heq]
  exact ordinalAdd_omega_succ_closed lam0 (ordinalAdd_omega_succ_closed lam0 hlam0η)

end ZFVP
