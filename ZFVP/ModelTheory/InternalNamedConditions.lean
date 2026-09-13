import ZFVP.ModelTheory.InternalNamedCompleteTheory
import ZFVP.ModelTheory.InternalHenkinSourceNames
import ZFVP.SetTheory.FiniteNaturalSets
import ZFVP.SetTheory.FinitePartialFunctions
import ZFVP.SetTheory.SchroederBernstein

/-! The actual countable poset of finite named requirements and its decision
dense sets. Unused names are obtained from a sparse naming of the background. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

noncomputable def namedFiniteConditions (L M j B : V) : V :=
  {A ∈ ℘ (namedFormulaSet L (ω : V)) ; IsInternallyFinite A ∧ FinitelySourceRealized L M j (B ∪ A)}

theorem mem_namedFiniteConditions (L M j B A : V) : A ∈ namedFiniteConditions L M j B ↔
    A ⊆ namedFormulaSet L (ω : V) ∧ IsInternallyFinite A ∧ FinitelySourceRealized L M j (B ∪ A) := by
  simp only [namedFiniteConditions, mem_sep_iff, mem_power_iff]

instance namedFiniteConditions_definable : ℒₛₑₜ-function₄[V] namedFiniteConditions := by
  have h : ℒₛₑₜ-relation₅[V] (fun P L M j B ↦ ∀ A, A ∈ P ↔
      A ⊆ namedFormulaSet L (ω : V) ∧ IsInternallyFinite A ∧ FinitelySourceRealized L M j (B ∪ A)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = namedFiniteConditions (v 1) (v 2) (v 3) (v 4) ↔ _
  rw [mem_ext_iff]
  simp only [mem_namedFiniteConditions]

theorem empty_mem_namedFiniteConditions {L M j B : V} (hB : FinitelySourceRealized L M j B) :
    (∅ : V) ∈ namedFiniteConditions L M j B := by
  apply (mem_namedFiniteConditions _ _ _ _ _).mpr
  exact ⟨fun _ hp ↦ False.elim (not_mem_empty hp), internallyFinite_empty, by simpa using hB⟩

theorem namedFiniteConditions_countable (hAC : InternalChoice V) {L M j B : V}
    (hS : IsInternallyCountable (namedFormulaSet L (ω : V))) :
    IsInternallyCountable (namedFiniteConditions L M j B) := by
  have hs := Schmerl.internallyCountable_finiteSequences hAC hS
  apply internallyCountable_subset (internallyCountable_repl range (by definability) hs)
  intro A hA
  obtain ⟨hAS, hAfin, _⟩ := (mem_namedFiniteConditions _ _ _ _ _).mp hA
  obtain ⟨n, hn, hAn⟩ := hAfin
  obtain ⟨e, he, _, her⟩ := exists_bijection_of_cardEQ (And.intro hAn.2 hAn.1)
  exact (repl_spec _).mpr ⟨e,
    (mem_finiteSequences_iff _ _).mpr ⟨n, hn, mem_function_of_mem_function_of_subset he hAS⟩, her.symm⟩

theorem namedFiniteCondition_extend {L M j B A p : V} (hA : A ∈ namedFiniteConditions L M j B)
    (hp : p ∈ namedFormulaSet L (ω : V))
    (h : FinitelySourceRealized L M j ((B ∪ A) ∪ {p})) :
    A ∪ {p} ∈ namedFiniteConditions L M j B := by
  obtain ⟨hAS, hAfin, _⟩ := (mem_namedFiniteConditions _ _ _ _ _).mp hA
  apply (mem_namedFiniteConditions _ _ _ _ _).mpr
  refine ⟨?_, internallyFinite_union hAfin (by simpa using internallyFinite_insert internallyFinite_empty p), ?_⟩
  · intro q hq
    rcases mem_union_iff.mp hq with hq | hq
    · exact hAS q hq
    · simpa only [mem_singleton_iff.mp hq] using hp
  · simpa only [union_assoc] using h

noncomputable def namedDecisionDense (P L p : V) : V := {A ∈ P ; p ∈ A ∨ namedNegation L p ∈ A}

instance namedDecisionDense_definable : ℒₛₑₜ-function₃[V] namedDecisionDense := by
  have h : ℒₛₑₜ-relation₄[V] (fun D P L p ↦ ∀ A, A ∈ D ↔ A ∈ P ∧ (p ∈ A ∨ namedNegation L p ∈ A)) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [namedDecisionDense, mem_sep_iff]
  rfl

theorem namedDecisionDense_dense {L M j B p : V} (hL : IsLanguageCode L)
    (hp : p ∈ namedFormulaSet L (ω : V)) :
    ForcingDense (namedFiniteConditions L M j B) (reverseInclusionOrder (namedFiniteConditions L M j B))
      (namedDecisionDense (namedFiniteConditions L M j B) L p) := by
  refine ⟨fun _ hA ↦ (mem_sep_iff.mp hA).1, fun A hA ↦ ?_⟩
  have hAF := ((mem_namedFiniteConditions _ _ _ _ _).mp hA).2.2
  rcases hAF.decide hL hp with h | h
  · have hnew := namedFiniteCondition_extend hA hp h
    exact ⟨A ∪ {p}, mem_sep_iff.mpr ⟨hnew, Or.inl (by simp)⟩,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hnew, hA, fun _ hx ↦ mem_union_iff.mpr (Or.inl hx)⟩⟩
  · have hnew := namedFiniteCondition_extend hA (namedNegation_mem hL hp) h
    exact ⟨A ∪ {namedNegation L p}, mem_sep_iff.mpr ⟨hnew, Or.inr (by simp)⟩,
      (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hnew, hA, fun _ hx ↦ mem_union_iff.mpr (Or.inl hx)⟩⟩

def HasFreshBackgroundNames (j B : V) : Prop :=
  ∀ S, IsInternallyFinite S → S ⊆ (ω : V) →
    ∃ k ∈ (ω : V), k ∉ range j ∧ k ∉ namedTheorySupport B ∧ k ∉ S

instance hasFreshBackgroundNames_definable : ℒₛₑₜ-relation[V] HasFreshBackgroundNames := by
  unfold HasFreshBackgroundNames
  definability

theorem freshBackgroundNames_of_sparse {D e j B : V} (he : IsSparseInternalNaming D e)
    (hj : range j ⊆ range e) (hB : namedTheorySupport B ⊆ range e) : HasFreshBackgroundNames j B := by
  intro S hS hSω
  obtain ⟨n, hn, hSn⟩ := internallyFinite_naturals_bounded hS hSω
  obtain ⟨k, hk, hnk, hke⟩ := he.2.2 n hn
  exact ⟨k, hk, fun hh ↦ hke (hj k hh), fun hh ↦ hke (hB k hh),
    fun hh ↦ mem_irrefl k (hnk k (hSn k hh))⟩

theorem freshName_for_condition {L M j B A n b : V} (hL : IsLanguageCode L)
    (hA : A ∈ namedFiniteConditions L M j B) (hn : n ∈ (ω : V)) (hb : b ∈ (ω : V) ^ n)
    (hfr : HasFreshBackgroundNames j B) :
    ∃ k ∈ (ω : V), k ∉ range j ∧ k ∉ namedTheorySupport (B ∪ A) ∧ k ∉ range b := by
  obtain ⟨hAS, hAfin, _⟩ := (mem_namedFiniteConditions _ _ _ _ _).mp hA
  have hbvalid := (pair_mem_namedFormulaSet_iff hL).mpr ⟨(formulaSet_constants hL hn ∅).1, hb⟩
  have hbfin : IsInternallyFinite (range b) := by
    simpa only [namedFormulaSupport, kpair.π₂_kpair] using namedFormulaSupport_finite hL hbvalid
  obtain ⟨k, hk, hkj, hkB, hkS⟩ := hfr (namedTheorySupport A ∪ range b)
    (internallyFinite_union (namedTheorySupport_finite hL hAS hAfin) hbfin) (by
      intro x hx
      rcases mem_union_iff.mp hx with hx | hx
      · exact namedTheorySupport_subset hL hAS x hx
      · exact range_subset_of_mem_function hb x hx)
  refine ⟨k, hk, hkj, ?_, fun hh ↦ hkS (mem_union_iff.mpr (Or.inr hh))⟩
  intro hh
  obtain ⟨p, hp, hkp⟩ := (mem_namedTheorySupport (B ∪ A) k).mp hh
  rcases mem_union_iff.mp hp with hp | hp
  · exact hkB ((mem_namedTheorySupport B k).mpr ⟨p, hp, hkp⟩)
  · exact hkS (mem_union_iff.mpr (Or.inl ((mem_namedTheorySupport A k).mpr ⟨p, hp, hkp⟩)))

end ZFVP
