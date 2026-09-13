import ZFVP.ModelTheory.InternalNamedWitnessDensity

/-! Constructor truth follows from an actual complete, witnessed set of named
formulas whose finite fragments remain realizable over the source. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

structure IsCompleteNamedTheory (L M j B T : V) : Prop where
  finite : FinitelySourceRealized L M j (B ∪ T)
  complete : ∀ p ∈ namedFormulaSet L (ω : V), p ∈ T ∨ namedNegation L p ∈ T
  witnesses : ∀ n ∈ (ω : V), ∀ φ ∈ formulaSet L ∅ (succ n), ∀ b ∈ (ω : V) ^ n,
    ⟨⟨n, existsCode φ⟩ₖ, b⟩ₖ ∈ T → ∃ k ∈ (ω : V), ⟨⟨succ n, φ⟩ₖ, assignmentPrepend n b k⟩ₖ ∈ T

namespace IsCompleteNamedTheory

variable {L M j B T : V} (h : IsCompleteNamedTheory L M j B T)

include h

theorem valid : T ⊆ namedFormulaSet L (ω : V) :=
  fun p hp ↦ h.finite.1 p (mem_union_iff.mpr (Or.inr hp))

theorem finite_realization {S : V} (hS : IsInternallyFinite S) (hST : S ⊆ T) :
    ∃ f, SourceNaming M j f ∧ ∀ p ∈ S, NamedHolds L M f p :=
  h.finite.2 S hS (fun p hp ↦ mem_union_iff.mpr (Or.inr (hST p hp)))

theorem consequence (hL : IsLanguageCode L) {A p : V}
    (hA : IsInternallyFinite A) (hAT : A ⊆ T) (hp : p ∈ namedFormulaSet L (ω : V))
    (hs : ∀ f, SourceNaming M j f → (∀ q ∈ A, NamedHolds L M f q) → NamedHolds L M f p) : p ∈ T := by
  rcases h.complete p hp with hpT | hnpT
  · exact hpT
  · exfalso
    obtain ⟨f, hf, hh⟩ := h.finite_realization (internallyFinite_insert hA (namedNegation L p)) (by
      intro q hq
      rcases mem_insert.mp hq with rfl | hq
      · exact hnpT
      · exact hAT q hq)
    have hnp := (namedHolds_negation hL hf.1 hp).mp (hh _ (mem_insert.mpr (Or.inl rfl)))
    exact hnp (hs f hf (fun q hq ↦ hh q (mem_insert.mpr (Or.inr hq))))

theorem consequence_one (hL : IsLanguageCode L) {p q : V}
    (hpT : p ∈ T) (hq : q ∈ namedFormulaSet L (ω : V))
    (hs : ∀ f, SourceNaming M j f → NamedHolds L M f p → NamedHolds L M f q) : q ∈ T := by
  apply h.consequence hL (by simpa using internallyFinite_insert internallyFinite_empty p)
    (fun r hr ↦ (mem_singleton_iff.mp hr) ▸ hpT) hq
  intro f hf hh
  exact hs f hf (hh p (by simp))

theorem consequence_two (hL : IsLanguageCode L) {p q r : V}
    (hpT : p ∈ T) (hqT : q ∈ T) (hr : r ∈ namedFormulaSet L (ω : V))
    (hs : ∀ f, SourceNaming M j f → NamedHolds L M f p → NamedHolds L M f q → NamedHolds L M f r) : r ∈ T := by
  apply h.consequence hL (by
    simpa using internallyFinite_insert (internallyFinite_insert internallyFinite_empty q) p)
    (by
      intro x hx
      have hx' : x = p ∨ x = q := by simpa using hx
      rcases hx' with rfl | rfl <;> assumption) hr
  intro f hf hh
  exact hs f hf (hh p (by simp)) (hh q (by simp))

theorem negation_mem_iff (hL : IsLanguageCode L) {p : V} (hp : p ∈ namedFormulaSet L (ω : V)) :
    namedNegation L p ∈ T ↔ p ∉ T := by
  constructor
  · intro hn hpT
    obtain ⟨f, hf, hh⟩ := h.finite_realization
      (by simpa using internallyFinite_insert (internallyFinite_insert internallyFinite_empty p) (namedNegation L p))
      (by
        intro q hq
        have hq' : q = namedNegation L p ∨ q = p := by simpa using hq
        rcases hq' with rfl | rfl <;> assumption)
    exact ((namedHolds_negation hL hf.1 hp).mp (hh _ (by simp))) (hh p (by simp))
  · intro hpT
    exact (h.complete p hp).resolve_left hpT

theorem truth_mem (hL : IsLanguageCode L) {n b : V} (hn : n ∈ (ω : V)) (hb : b ∈ (ω : V) ^ n) :
    ⟨⟨n, truthCode⟩ₖ, b⟩ₖ ∈ T := by
  apply h.consequence hL internallyFinite_empty (fun _ hx ↦ False.elim (not_mem_empty hx))
    ((pair_mem_namedFormulaSet_iff hL).mpr ⟨(formulaSet_constants hL hn ∅).1, hb⟩)
  intro f hf _
  exact (namedHolds_pair _ _ _ _ _ _).mpr ((satisfies_truth hL hn).mpr (compose_function hb hf.1))

theorem falsity_not_mem (hL : IsLanguageCode L) {n b : V} (hn : n ∈ (ω : V)) (_hb : b ∈ (ω : V) ^ n) :
    ⟨⟨n, falsityCode⟩ₖ, b⟩ₖ ∉ T := by
  intro hp
  obtain ⟨f, _, hh⟩ := h.finite_realization
    (by simpa using internallyFinite_insert internallyFinite_empty ⟨⟨n, falsityCode⟩ₖ, b⟩ₖ)
    (by intro q hq; exact (mem_singleton_iff.mp hq) ▸ hp)
  have hs := hh ⟨⟨n, falsityCode⟩ₖ, b⟩ₖ (by simp)
  exact not_satisfies_falsity hL hn ((namedHolds_pair L M f n falsityCode b).mp hs)

theorem and_mem_iff (hL : IsLanguageCode L) {n φ ψ b : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet L ∅ n) (hψ : ψ ∈ formulaSet L ∅ n) (hb : b ∈ (ω : V) ^ n) :
    ⟨⟨n, andCode φ ψ⟩ₖ, b⟩ₖ ∈ T ↔ ⟨⟨n, φ⟩ₖ, b⟩ₖ ∈ T ∧ ⟨⟨n, ψ⟩ₖ, b⟩ₖ ∈ T := by
  have hvφ := (pair_mem_namedFormulaSet_iff hL).mpr ⟨hφ, hb⟩
  have hvψ := (pair_mem_namedFormulaSet_iff hL).mpr ⟨hψ, hb⟩
  constructor
  · intro hp
    constructor
    · apply h.consequence_one hL hp hvφ
      intro f hf hs
      rw [namedHolds_pair, satisfies_and hL hn hφ hψ (compose_function hb hf.1)] at hs
      exact (namedHolds_pair _ _ _ _ _ _).mpr hs.1
    · apply h.consequence_one hL hp hvψ
      intro f hf hs
      rw [namedHolds_pair, satisfies_and hL hn hφ hψ (compose_function hb hf.1)] at hs
      exact (namedHolds_pair _ _ _ _ _ _).mpr hs.2
  · rintro ⟨hp, hq⟩
    apply h.consequence_two hL hp hq
      ((pair_mem_namedFormulaSet_iff hL).mpr ⟨(formulaSet_binary hL hn hφ hψ).1, hb⟩)
    intro f hf hs ht
    rw [namedHolds_pair, satisfies_and hL hn hφ hψ (compose_function hb hf.1)]
    exact ⟨(namedHolds_pair _ _ _ _ _ _).mp hs, (namedHolds_pair _ _ _ _ _ _).mp ht⟩

theorem or_mem_iff (hL : IsLanguageCode L) {n φ ψ b : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet L ∅ n) (hψ : ψ ∈ formulaSet L ∅ n) (hb : b ∈ (ω : V) ^ n) :
    ⟨⟨n, orCode φ ψ⟩ₖ, b⟩ₖ ∈ T ↔ ⟨⟨n, φ⟩ₖ, b⟩ₖ ∈ T ∨ ⟨⟨n, ψ⟩ₖ, b⟩ₖ ∈ T := by
  have hvφ := (pair_mem_namedFormulaSet_iff hL).mpr ⟨hφ, hb⟩
  have hvψ := (pair_mem_namedFormulaSet_iff hL).mpr ⟨hψ, hb⟩
  have hvo := (pair_mem_namedFormulaSet_iff hL).mpr ⟨(formulaSet_binary hL hn hφ hψ).2, hb⟩
  constructor
  · intro hp
    rcases h.complete _ hvφ with hleft | hnleft
    · exact Or.inl hleft
    · apply Or.inr
      apply h.consequence_two hL hp hnleft hvψ
      intro f hf hs ht
      have hnφ := (namedHolds_negation hL hf.1 hvφ).mp ht
      rw [namedHolds_pair, satisfies_or hL hn hφ hψ (compose_function hb hf.1)] at hs
      exact (namedHolds_pair _ _ _ _ _ _).mpr (hs.resolve_left (fun hh ↦ hnφ ((namedHolds_pair _ _ _ _ _ _).mpr hh)))
  · intro hh
    rcases hh with hp | hp
    · apply h.consequence_one hL hp hvo
      intro f hf hs
      rw [namedHolds_pair, satisfies_or hL hn hφ hψ (compose_function hb hf.1)]
      exact Or.inl ((namedHolds_pair _ _ _ _ _ _).mp hs)
    · apply h.consequence_one hL hp hvo
      intro f hf hs
      rw [namedHolds_pair, satisfies_or hL hn hφ hψ (compose_function hb hf.1)]
      exact Or.inr ((namedHolds_pair _ _ _ _ _ _).mp hs)

theorem exists_mem_iff (hL : IsLanguageCode L) {n φ b : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet L ∅ (succ n)) (hb : b ∈ (ω : V) ^ n) :
    ⟨⟨n, existsCode φ⟩ₖ, b⟩ₖ ∈ T ↔ ∃ k ∈ (ω : V), ⟨⟨succ n, φ⟩ₖ, assignmentPrepend n b k⟩ₖ ∈ T := by
  constructor
  · exact h.witnesses n hn φ hφ b hb
  · rintro ⟨k, hk, hp⟩
    apply h.consequence_one hL hp
      ((pair_mem_namedFormulaSet_iff hL).mpr ⟨(formulaSet_quantifiers hL hn hφ).2, hb⟩)
    intro f hf hs
    rw [namedHolds_pair, compose_assignmentPrepend hn hb hf.1 hk] at hs
    rw [namedHolds_pair, satisfies_exists hL hn hφ (compose_function hb hf.1)]
    exact ⟨f ‘ k, function_value_mem hf.1 hk, hs⟩

theorem all_mem_iff (hL : IsLanguageCode L) {n φ b : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet L ∅ (succ n)) (hb : b ∈ (ω : V) ^ n) :
    ⟨⟨n, allCode φ⟩ₖ, b⟩ₖ ∈ T ↔ ∀ k ∈ (ω : V), ⟨⟨succ n, φ⟩ₖ, assignmentPrepend n b k⟩ₖ ∈ T := by
  constructor
  · intro hp k hk
    apply h.consequence_one hL hp
      ((pair_mem_namedFormulaSet_iff hL).mpr ⟨hφ, assignmentPrepend_mem_function hn hb hk⟩)
    intro f hf hs
    rw [namedHolds_pair, satisfies_all hL hn hφ (compose_function hb hf.1)] at hs
    rw [namedHolds_pair, compose_assignmentPrepend hn hb hf.1 hk]
    exact hs _ (function_value_mem hf.1 hk)
  · intro hall
    rcases h.complete _ ((pair_mem_namedFormulaSet_iff hL).mpr ⟨(formulaSet_quantifiers hL hn hφ).1, hb⟩) with hp | hp
    · exact hp
    · exfalso
      rw [namedNegation_pair, negateFormula_all hL hn hφ] at hp
      obtain ⟨k, hk, hneg⟩ := (h.exists_mem_iff hL hn (negateFormula_mem hL hφ) hb).mp hp
      have hv := (pair_mem_namedFormulaSet_iff hL).mpr ⟨hφ, assignmentPrepend_mem_function hn hb hk⟩
      have he : namedNegation L ⟨⟨succ n, φ⟩ₖ, assignmentPrepend n b k⟩ₖ ∈ T := by
        simpa only [namedNegation_pair] using hneg
      exact ((h.negation_mem_iff hL hv).mp he) (hall k hk)

end IsCompleteNamedTheory
end ZFVP
