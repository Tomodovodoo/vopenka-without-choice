import ZFVP.ModelTheory.InternalNamedConditions
import ZFVP.ModelTheory.GroundForcingGeneric
import ZFVP.SetTheory.FiniteDirectedUnions

/-! The actual union of a filter of finite named conditions is finitely
realizable. Meeting decision sets makes this union complete. -/

set_option autoImplicit false

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsForcingFilter.inclusion_directed {P G : V}
    (hG : IsForcingFilter P (reverseInclusionOrder P) G) :
    ∀ A ∈ G, ∀ B ∈ G, ∃ C ∈ G, A ⊆ C ∧ B ⊆ C := by
  intro A hA B hB
  obtain ⟨C, hC, hCA, hCB⟩ := hG.2.2.2 A hA B hB
  exact ⟨C, hC, ((pair_mem_reverseInclusionOrder _ _ _).mp hCA).2.2,
    ((pair_mem_reverseInclusionOrder _ _ _).mp hCB).2.2⟩

theorem IsForcingFilter.finite_subset_sUnion {P G S : V}
    (hG : IsForcingFilter P (reverseInclusionOrder P) G)
    (hS : IsInternallyFinite S) (hSG : S ⊆ ⋃ˢ G) : ∃ A ∈ G, S ⊆ A :=
  internallyFinite_subset_directed_sUnion ⟨hG.2.1⟩ hG.inclusion_directed hS hSG

theorem finitelySourceRealized_directed_sUnion {L M j B G : V} (hne : IsNonempty G)
    (hdir : ∀ A ∈ G, ∀ C ∈ G, ∃ D ∈ G, A ⊆ D ∧ C ⊆ D)
    (hreal : ∀ A ∈ G, FinitelySourceRealized L M j (B ∪ A)) :
    FinitelySourceRealized L M j (B ∪ ⋃ˢ G) := by
  obtain ⟨A₀, hA₀⟩ := hne
  refine ⟨?_, fun S hS hSBG ↦ ?_⟩
  · intro q hq
    rcases mem_union_iff.mp hq with hq | hq
    · exact (hreal A₀ hA₀).1 q (mem_union_iff.mpr (Or.inl hq))
    · obtain ⟨A, hA, hqA⟩ := mem_sUnion_iff.mp hq
      exact (hreal A hA).1 q (mem_union_iff.mpr (Or.inr hqA))
  · have hfin : IsInternallyFinite (S ∩ ⋃ˢ G) :=
      internallyFinite_subset hS (fun _ hq ↦ (mem_inter_iff.mp hq).1)
    obtain ⟨A, hA, hSA⟩ := internallyFinite_subset_directed_sUnion ⟨A₀, hA₀⟩ hdir hfin
      (fun _ hq ↦ (mem_inter_iff.mp hq).2)
    apply (hreal A hA).2 S hS
    intro q hq
    rcases mem_union_iff.mp (hSBG q hq) with hqB | hqG
    · exact mem_union_iff.mpr (Or.inl hqB)
    · exact mem_union_iff.mpr (Or.inr (hSA q (mem_inter_iff.mpr ⟨hq, hqG⟩)))

theorem namedConditionFilter_sUnion_finite {L M j B G : V}
    (hG : IsForcingFilter (namedFiniteConditions L M j B)
      (reverseInclusionOrder (namedFiniteConditions L M j B)) G) :
    FinitelySourceRealized L M j (B ∪ ⋃ˢ G) :=
  finitelySourceRealized_directed_sUnion ⟨hG.2.1⟩ hG.inclusion_directed
    (fun A hA ↦ ((mem_namedFiniteConditions _ _ _ _ _).mp (hG.1 A hA)).2.2)

theorem namedConditionFilter_sUnion_valid {L M j B G : V}
    (hG : IsForcingFilter (namedFiniteConditions L M j B)
      (reverseInclusionOrder (namedFiniteConditions L M j B)) G) :
    ⋃ˢ G ⊆ namedFormulaSet L (ω : V) :=
  fun q hq ↦ (namedConditionFilter_sUnion_finite hG).1 q (mem_union_iff.mpr (Or.inr hq))

theorem namedDecisionDense_sUnion {P L G q : V}
    (hmeet : ∃ A ∈ G, A ∈ namedDecisionDense P L q) :
    q ∈ ⋃ˢ G ∨ namedNegation L q ∈ ⋃ˢ G := by
  obtain ⟨A, hA, hD⟩ := hmeet
  rcases (mem_sep_iff.mp hD).2 with hq | hq
  · exact Or.inl (mem_sUnion_iff.mpr ⟨A, hA, hq⟩)
  · exact Or.inr (mem_sUnion_iff.mpr ⟨A, hA, hq⟩)

theorem namedConditionFilter_sUnion_complete {P L G : V}
    (hmeet : ∀ q ∈ namedFormulaSet L (ω : V), ∃ A ∈ G, A ∈ namedDecisionDense P L q) :
    ∀ q ∈ namedFormulaSet L (ω : V), q ∈ ⋃ˢ G ∨ namedNegation L q ∈ ⋃ˢ G :=
  fun q hq ↦ namedDecisionDense_sUnion (hmeet q hq)

theorem FinitelySourceRealized.not_both {L M j T q : V} (h : FinitelySourceRealized L M j T)
    (hL : IsLanguageCode L) (hq : q ∈ namedFormulaSet L (ω : V)) :
    q ∈ T → namedNegation L q ∈ T → False := by
  intro hqT hnT
  obtain ⟨f, hf, hh⟩ := h.2 {q, namedNegation L q}
    (by simpa using internallyFinite_insert (internallyFinite_insert internallyFinite_empty (namedNegation L q)) q)
    (by
      intro p hp
      have hp' : p = q ∨ p = namedNegation L q := by simpa using hp
      rcases hp' with rfl | rfl <;> assumption)
  exact ((namedHolds_negation hL hf.1 hq).mp (hh _ (by simp))) (hh q (by simp))

theorem namedConditionFilter_sUnion_isCompleteNamedTheory {L M j B G : V}
    (hL : IsLanguageCode L)
    (hG : IsForcingFilter (namedFiniteConditions L M j B)
      (reverseInclusionOrder (namedFiniteConditions L M j B)) G)
    (hdec : ∀ q ∈ namedFormulaSet L (ω : V),
      ∃ A ∈ G, A ∈ namedDecisionDense (namedFiniteConditions L M j B) L q)
    (hwit : ∀ n ∈ (ω : V), ∀ φ ∈ formulaSet L ∅ (succ n), ∀ b ∈ (ω : V) ^ n,
      ∃ A ∈ G, namedNegation L ⟨⟨n, existsCode φ⟩ₖ, b⟩ₖ ∈ A ∨
        ∃ k ∈ (ω : V), ⟨⟨succ n, φ⟩ₖ, assignmentPrepend n b k⟩ₖ ∈ A) :
    IsCompleteNamedTheory L M j B (⋃ˢ G) := by
  have hfin := namedConditionFilter_sUnion_finite hG
  refine ⟨hfin, namedConditionFilter_sUnion_complete hdec, ?_⟩
  intro n hn φ hφ b hb hex
  obtain ⟨A, hA, hh⟩ := hwit n hn φ hφ b hb
  rcases hh with hh | ⟨k, hk, hkw⟩
  · exact False.elim (hfin.not_both hL
      ((pair_mem_namedFormulaSet_iff hL).mpr ⟨(formulaSet_quantifiers hL hn hφ).2, hb⟩)
      (mem_union_iff.mpr (Or.inr hex))
      (mem_union_iff.mpr (Or.inr (mem_sUnion_iff.mpr ⟨A, hA, hh⟩))))
  · exact ⟨k, hk, mem_sUnion_iff.mpr ⟨A, hA, hkw⟩⟩

end ZFVP
