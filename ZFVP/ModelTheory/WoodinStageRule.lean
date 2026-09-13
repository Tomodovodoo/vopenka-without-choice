import ZFVP.ModelTheory.WoodinInverseCodeDefinability
import ZFVP.ModelTheory.WoodinIterationInitial
import ZFVP.ModelTheory.WoodinDirectIteration
import ZFVP.ModelTheory.WoodinInverseStagePreservation
import ZFVP.ModelTheory.WoodinHistoryBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinStageRule (θ s K : V) : V := by
  classical
  exact if θ = ∅ then ⟨woodinInitialCode, woodinInitialCardinals⟩ₖ else
    if θ = succ (⋃ˢ θ) then
      ⟨woodinIterationSuccessor (⋃ˢ θ) s K, woodinIterationCardinalNext (⋃ˢ θ) s K⟩ₖ else
    if IsChoicelessInaccessible (woodinLimitCardinal K) then
      ⟨forcingDirectCode θ s, forcingFamilyNext θ K (woodinLimitCardinal K)⟩ₖ else
      ⟨woodinInverseSourceCode θ s K, woodinInverseCardinalNext θ s K⟩ₖ

instance woodinStageRule_definable : ℒₛₑₜ-function₃[V] woodinStageRule := by
  classical
  have h : ℒₛₑₜ-relation₄ (fun z θ s K : V ↦
      (θ = ∅ ∧ z = ⟨woodinInitialCode, woodinInitialCardinals⟩ₖ) ∨
      (θ ≠ ∅ ∧ θ = succ (⋃ˢ θ) ∧
        z = ⟨woodinIterationSuccessor (⋃ˢ θ) s K, woodinIterationCardinalNext (⋃ˢ θ) s K⟩ₖ) ∨
      (θ ≠ ∅ ∧ θ ≠ succ (⋃ˢ θ) ∧ IsChoicelessInaccessible (woodinLimitCardinal K) ∧
        z = ⟨forcingDirectCode θ s, forcingFamilyNext θ K (woodinLimitCardinal K)⟩ₖ) ∨
      (θ ≠ ∅ ∧ θ ≠ succ (⋃ˢ θ) ∧ ¬IsChoicelessInaccessible (woodinLimitCardinal K) ∧
        z = ⟨woodinInverseSourceCode θ s K, woodinInverseCardinalNext θ s K⟩ₖ)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = woodinStageRule (v 1) (v 2) (v 3) ↔ _
  unfold woodinStageRule
  split_ifs <;> tauto

theorem woodinStageRule_initial (s K : V) :
    woodinStageRule ∅ s K = ⟨woodinInitialCode, woodinInitialCardinals⟩ₖ := by
  simp [woodinStageRule]

theorem woodinStageRule_successor (k s K : V) [IsOrdinal k] :
    woodinStageRule (succ k) s K =
      ⟨woodinIterationSuccessor k s K, woodinIterationCardinalNext k s K⟩ₖ := by
  have hn : succ k ≠ (∅ : V) := by
    intro he
    have hm := mem_succ_self k
    rw [he] at hm
    exact not_mem_empty hm
  simp [woodinStageRule, hn, sUnion_succ_of_transitive]

theorem woodinStageRule_valid {δ θ s K : V} [IsOrdinal θ]
    (hδ : IsWoodinSupercompact δ) (hθ : θ ∈ δ) (h : IsWoodinIteration δ θ s K)
    (hc : HasWoodinQuotientClosure θ s K)
    (hinverse : θ ≠ ∅ → (∀ i ∈ θ, succ i ∈ θ) →
      ¬IsChoicelessInaccessible (woodinLimitCardinal K) →
      ∀ i ∈ θ, IterationQuotientClosedBelow (forcingInverseCode θ s) i θ (K ‘ i)) :
    IsWoodinIteration δ (succ θ) (kpair.π₁ (woodinStageRule θ s K))
      (kpair.π₂ (woodinStageRule θ s K)) := by
  classical
  by_cases hzero : θ = ∅
  · subst θ
    simpa only [woodinStageRule_initial, kpair.π₁_kpair, kpair.π₂_kpair] using woodinInitialCode_iteration hδ
  by_cases hsucc : θ = succ (⋃ˢ θ)
  · have hk : ⋃ˢ θ ∈ θ :=
      (congrArg (fun x : V ↦ (⋃ˢ θ) ∈ x) hsucc).mpr (mem_succ_self (⋃ˢ θ))
    let := IsOrdinal.of_mem hk
    have hh : IsWoodinIteration δ (succ (⋃ˢ θ)) s K := hsucc ▸ h
    have he : woodinStageRule θ s K =
        ⟨woodinIterationSuccessor (⋃ˢ θ) s K, woodinIterationCardinalNext (⋃ˢ θ) s K⟩ₖ := by
      simp only [woodinStageRule, ite_eq_right hzero, ite_eq_left hsucc]
    rw [he]
    simpa only [kpair.π₁_kpair, kpair.π₂_kpair, ← hsucc] using hh.successor hδ
  have hlim := ordinal_limit_of_not_successor hsucc
  have h0 : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left
    (fun he ↦ hzero he.symm)
  by_cases hinac : IsChoicelessInaccessible (woodinLimitCardinal K)
  · simp only [woodinStageRule, ite_eq_right hzero, ite_eq_right hsucc, ite_eq_left hinac,
      kpair.π₁_kpair, kpair.π₂_kpair]
    exact h.direct hc hδ.inaccessible.regular hθ h0 hlim hinac
  · simp only [woodinStageRule, ite_eq_right hzero, ite_eq_right hsucc, ite_eq_right hinac,
      kpair.π₁_kpair, kpair.π₂_kpair]
    exact h.inverse_source_of_quotient_closure hδ hθ h0 hlim hinac (hinverse hzero hlim hinac)

theorem woodinStageRule_code_extends {θ s K : V} [IsOrdinal θ]
    (h : IsForcingIterationCode θ s) (hzero : θ ≠ ∅) :
    ForcingCodeExtends s (kpair.π₁ (woodinStageRule θ s K)) := by
  classical
  by_cases hsucc : θ = succ (⋃ˢ θ)
  · have hk : ⋃ˢ θ ∈ θ :=
      (congrArg (fun x : V ↦ (⋃ˢ θ) ∈ x) hsucc).mpr (mem_succ_self (⋃ˢ θ))
    let := IsOrdinal.of_mem hk
    simp only [woodinStageRule, ite_eq_right hzero, ite_eq_left hsucc, kpair.π₁_kpair]
    exact woodinIterationSuccessor_extends (hsucc ▸ h) K
  · simp only [woodinStageRule, ite_eq_right hzero, ite_eq_right hsucc]
    split
    · rw [kpair.π₁_kpair]
      unfold forcingDirectCode
      exact forcingThreadCode_extends h _
    · rw [kpair.π₁_kpair]
      unfold woodinInverseSourceCode
      exact forcingInverseSourceCollapseCode_extends h _ _

theorem woodinStageRule_cardinals_extend {θ s K : V} [IsOrdinal θ]
    (h : IsIterationTable θ K) (hzero : θ ≠ ∅) :
    K ⊆ kpair.π₂ (woodinStageRule θ s K) := by
  classical
  by_cases hsucc : θ = succ (⋃ˢ θ)
  · simp only [woodinStageRule, ite_eq_right hzero, ite_eq_left hsucc, kpair.π₂_kpair]
    exact forcingFamilyNext_extends (hsucc ▸ h) _
  · simp only [woodinStageRule, ite_eq_right hzero, ite_eq_right hsucc]
    split
    · rw [kpair.π₂_kpair]
      exact forcingFamilyNext_extends h _
    · rw [kpair.π₂_kpair]
      exact forcingFamilyNext_extends h _

end ZFVP
