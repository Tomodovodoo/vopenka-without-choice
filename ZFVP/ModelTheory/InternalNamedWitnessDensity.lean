import ZFVP.ModelTheory.InternalNamedSupport

/-! A fresh name witnesses a consistent existential while preserving finite
satisfiability of the entire fixed-name background theory. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem FinitelySourceRealized.fresh_witness {L M j B n φ b k : V}
    (hL : IsLanguageCode L) (hj : j ∈ (ω : V) ^ structureDomain M)
    (hn : n ∈ (ω : V)) (hφ : φ ∈ formulaSet L ∅ (succ n)) (hb : b ∈ (ω : V) ^ n)
    (hk : k ∈ (ω : V)) (hkj : k ∉ range j) (hkB : k ∉ namedTheorySupport B) (hkb : k ∉ range b)
    (h : FinitelySourceRealized L M j (B ∪ {⟨⟨n, existsCode φ⟩ₖ, b⟩ₖ})) :
    FinitelySourceRealized L M j (B ∪ {⟨⟨succ n, φ⟩ₖ, assignmentPrepend n b k⟩ₖ}) := by
  have hB : FinitelySourceRealized L M j B := h.mono (fun _ hp ↦ mem_union_iff.mpr (Or.inl hp))
  have hexvalid : ⟨⟨n, existsCode φ⟩ₖ, b⟩ₖ ∈ namedFormulaSet L (ω : V) :=
    (pair_mem_namedFormulaSet_iff hL).mpr ⟨(formulaSet_quantifiers hL hn hφ).2, hb⟩
  have hwvalid : ⟨⟨succ n, φ⟩ₖ, assignmentPrepend n b k⟩ₖ ∈ namedFormulaSet L (ω : V) :=
    (pair_mem_namedFormulaSet_iff hL).mpr ⟨hφ, assignmentPrepend_mem_function hn hb hk⟩
  apply (finitelySourceRealized_insert_iff hB.1 hwvalid).mpr
  intro S hS hSB
  obtain ⟨f, hf, hs, he⟩ := (finitelySourceRealized_insert_iff hB.1 hexvalid).mp h S hS hSB
  rw [namedHolds_pair, satisfies_exists hL hn hφ (compose_function hb hf.1)] at he
  obtain ⟨x, hx, hφx⟩ := he
  have hg := nameAssignmentUpdate_mem (k := k) hf.1 hx
  refine ⟨nameAssignmentUpdate f k x, hf.update hj hkj hx, ?_, ?_⟩
  · intro p hp
    apply (namedHolds_update_fresh hL hf.1 (hB.1 p (hSB p hp)) hx ?_).mpr (hs p hp)
    exact fun hkp ↦ hkB ((mem_namedTheorySupport B k).mpr ⟨p, hSB p hp, hkp⟩)
  · rw [namedHolds_pair, compose_assignmentPrepend hn hb hg hk,
      compose_nameAssignmentUpdate_fresh hf.1 hb hx hkb, nameAssignmentUpdate_at f x hk]
    exact hφx

theorem FinitelySourceRealized.decide_or_fresh_witness {L M j B n φ b k : V}
    (hL : IsLanguageCode L) (hj : j ∈ (ω : V) ^ structureDomain M)
    (hn : n ∈ (ω : V)) (hφ : φ ∈ formulaSet L ∅ (succ n)) (hb : b ∈ (ω : V) ^ n)
    (hk : k ∈ (ω : V)) (hkj : k ∉ range j) (hkB : k ∉ namedTheorySupport B) (hkb : k ∉ range b)
    (hB : FinitelySourceRealized L M j B) :
    FinitelySourceRealized L M j (B ∪ {namedNegation L ⟨⟨n, existsCode φ⟩ₖ, b⟩ₖ}) ∨
      FinitelySourceRealized L M j (B ∪ {⟨⟨succ n, φ⟩ₖ, assignmentPrepend n b k⟩ₖ}) := by
  have hp := (pair_mem_namedFormulaSet_iff hL).mpr ⟨(formulaSet_quantifiers hL hn hφ).2, hb⟩
  rcases hB.decide hL hp with h | h
  · exact Or.inr (h.fresh_witness hL hj hn hφ hb hk hkj hkB hkb)
  · exact Or.inl h

end ZFVP
