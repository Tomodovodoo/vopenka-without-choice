import ZFVP.ModelTheory.WoodinSparseAutomorphismExtensionRows
import ZFVP.ModelTheory.WoodinSparseInitialDisplacement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSparseDirectFamilyAutomorphism (θ H : V) : V :=
  woodinSparseDirectAutomorphism θ (woodinSparsePrefixCode θ) H

instance woodinSparseDirectFamilyAutomorphism_definable : ℒₛₑₜ-function₂[V] woodinSparseDirectFamilyAutomorphism := by
  unfold woodinSparseDirectFamilyAutomorphism
  apply Language.DefinableFunction₃.comp <;> definability

noncomputable def woodinSparseAutomorphismExtensionRow (f θ H : V) : V := by
  classical
  exact if θ = ∅ then f else if θ = succ (⋃ˢ θ) then woodinSparseSuccessorAutomorphism (⋃ˢ θ) (H ‘ (⋃ˢ θ))
    else if IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)) then
      woodinSparseDirectFamilyAutomorphism θ H
    else woodinSparseCompletedFamilyAutomorphism θ H

instance woodinSparseAutomorphismExtensionRow_definable (f : V) :
    ℒₛₑₜ-function₂[V] (woodinSparseAutomorphismExtensionRow f) := by
  classical
  have h : ℒₛₑₜ-relation₃[V] (fun z θ H ↦
    (θ = ∅ ∧ z = f) ∨
    (θ ≠ ∅ ∧ θ = succ (⋃ˢ θ) ∧ z = woodinSparseSuccessorAutomorphism (⋃ˢ θ) (H ‘ (⋃ˢ θ))) ∨
    (θ ≠ ∅ ∧ θ ≠ succ (⋃ˢ θ) ∧ IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)) ∧
      z = woodinSparseDirectFamilyAutomorphism θ H) ∨
    (θ ≠ ∅ ∧ θ ≠ succ (⋃ˢ θ) ∧ ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)) ∧
      z = woodinSparseCompletedFamilyAutomorphism θ H)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = woodinSparseAutomorphismExtensionRow f (v 1) (v 2) ↔ _
  unfold woodinSparseAutomorphismExtensionRow
  split_ifs <;> tauto

theorem woodinSparseAutomorphismExtensionRow_spec {Ω f : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)
    (hf : IsForcingAutomorphism woodinSparseInitialCarrier woodinSparseInitialOrder f)
    (hft : f ‘ ∅ = ∅) :
    ∀ θ ∈ succ Ω, ∀ H, IsIterationTable θ H →
      IsCoherentForcingAutomorphismFamily θ (woodinSparseStageCode Ω) H →
      (∀ i ∈ θ, (H ‘ i) ‘ ((forcingCodet (woodinSparseStageCode Ω)) ‘ i) =
        (forcingCodet (woodinSparseStageCode Ω)) ‘ i) →
      IsCoherentAutomorphismRow θ (woodinSparseStageCode Ω) H (woodinSparseAutomorphismExtensionRow f θ H) := by
  let := hΩ.inaccessible.1
  have hc := woodinSparseStageCode_endpoint_valid hΩ hAC
  intro θ hθ H _ hm ht
  let := IsOrdinal.of_mem hθ
  have hsub : θ ⊆ Ω := (IsOrdinal.subset_iff).mpr (mem_succ_iff.mp hθ)
  have hs := woodinSparseStageCode_valid hΩ hAC hsub
  have he := woodinSparseStageCode_extends_endpoint hΩ hAC hsub
  apply IsCoherentAutomorphismRow.of_code_extension (hc := hs) (hd := hc) (he := he)
  by_cases h0 : θ = ∅
  · subst θ
    rw [woodinSparseAutomorphismExtensionRow, ite_eq_left rfl]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rwa [(woodinSparseStageCode_initial (V := V)).1, (woodinSparseStageCode_initial (V := V)).2]
    · rwa [woodinSparseStageCode_top hΩ hAC (empty_subset Ω)]
    · intro i hi
      exact (not_mem_empty hi).elim
    · intro i hi
      exact (not_mem_empty hi).elim
  have hpref := woodinSparsePrefixCode_valid hΩ hAC hsub
  have hep := woodinSparsePrefixCode_extends_endpoint hΩ hAC hsub
  have hmp := hm.of_code_extension hc hpref hep
  have htp : ∀ i ∈ θ, (H ‘ i) ‘ ((forcingCodet (woodinSparsePrefixCode θ)) ‘ i) =
      (forcingCodet (woodinSparsePrefixCode θ)) ‘ i := by
    intro i hi
    rw [hpref.tablet.value_of_subset hc.tablet hep.subt hi]
    exact ht i hi
  have ht0 : ∀ i ∈ θ, (H ‘ i) ‘ ∅ = ∅ := by
    intro i hi
    simpa only [woodinSparsePrefixCode_top hΩ hAC hsub hi] using htp i hi
  rw [woodinSparseAutomorphismExtensionRow, ite_eq_right h0]
  by_cases hsucc : θ = succ (⋃ˢ θ)
  · rw [ite_eq_left hsucc]
    generalize hkdef : ⋃ˢ θ = k at hsucc ⊢
    subst θ
    let := IsOrdinal.of_mem (mem_succ_self k)
    have hk : succ k ∈ Ω := by
      rcases mem_succ_iff.mp hθ with heq | hk
      · exact ((woodinEndpoint_branch hΩ hAC).2.1 (by rw [← heq, hkdef])).elim
      · exact hk
    exact woodinSparseSuccessorAutomorphism_row hΩ hAC hk hmp htp
  rw [ite_eq_right hsucc]
  by_cases hn : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))
  · rw [ite_eq_left hn]
    exact woodinSparseDirectAutomorphism_row hΩ hAC hsub h0 hsucc hn hmp ht0
  · rw [ite_eq_right hn]
    have hθΩ : θ ∈ Ω := by
      rcases mem_succ_iff.mp hθ with heq | hθΩ
      · subst θ
        exact (hn (woodinEndpoint_branch hΩ hAC).2.2).elim
      · exact hθΩ
    exact woodinSparseCompletedFamilyAutomorphism_row hΩ hAC hθΩ h0 hsucc hn hmp ht0

theorem woodinSparseInitialAutomorphism_extends {Ω f : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)
    (hf : IsForcingAutomorphism woodinSparseInitialCarrier woodinSparseInitialOrder f)
    (hft : f ‘ ∅ = ∅) :
    ∃ H, IsIterationTable (succ Ω) H ∧
      IsCoherentForcingAutomorphismFamily (succ Ω) (woodinSparseStageCode Ω) H ∧ H ‘ ∅ = f := by
  let := hΩ.inaccessible.1
  let F := fun H : V ↦ woodinSparseAutomorphismExtensionRow f (domain H) H
  have hF : ℒₛₑₜ-function₁ F := by dsimp only [F]; definability
  have hc := woodinSparseStageCode_endpoint_valid hΩ hAC
  have hstep : ∀ θ ∈ succ Ω, ∀ H, IsIterationTable θ H →
      IsCoherentForcingAutomorphismFamily θ (woodinSparseStageCode Ω) H →
      (∀ i ∈ θ, (H ‘ i) ‘ ((forcingCodet (woodinSparseStageCode Ω)) ‘ i) =
        (forcingCodet (woodinSparseStageCode Ω)) ‘ i) →
      IsCoherentAutomorphismRow θ (woodinSparseStageCode Ω) H (F H) := by
    intro θ hθ H hH hm ht
    dsimp only [F]
    rw [hH.domain_eq]
    exact woodinSparseAutomorphismExtensionRow_spec hΩ hAC hf hft θ hθ H hH hm ht
  have hh := coherentAutomorphismRec_family F hF hc hstep (subset_refl (succ Ω))
  refine ⟨coherentAutomorphismHistory F hF (succ Ω), hh.1, hh.2.1, ?_⟩
  have hz : (∅ : V) ∈ succ Ω := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (empty_subset Ω))
  rw [coherentAutomorphismHistory_value F hF hz, coherentAutomorphismRec_rule F hF]
  dsimp only [F]
  rw [(coherentAutomorphismHistory_table F hF ∅).domain_eq, woodinSparseAutomorphismExtensionRow, ite_eq_left rfl]

end ZFVP
