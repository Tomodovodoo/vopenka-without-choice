import ZFVP.ModelTheory.SchmerlInternalCodedChainUnion
import ZFVP.Syntax.FormulaInduction

/-! Each stage is elementary in the actual internal union, for every
internal formula and every internal finite assignment. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsInternalRelationalChain

variable {L θ C : V} (h : IsInternalRelationalChain L θ C)

include h

theorem stage_satisfies_iff {i j n φ b : V} (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j)
    (hn : n ∈ (ω : V)) (hφ : φ ∈ formulaSet L ∅ n) (hb : b ∈ structureDomain (C ‘ i) ^ n) :
    Satisfies L ∅ (C ‘ i) ∅ n φ b ↔ Satisfies L ∅ (C ‘ j) ∅ n φ b := by
  have he := (h.elementary i hi j hj hij).satisfies_iff hn hφ hb
  rwa [graph_compose_identity hb] at he

theorem satisfies_union_iff {i n φ b : V} (hi : i ∈ θ) (_hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet L ∅ n) (hb : b ∈ structureDomain (C ‘ i) ^ n) :
    Satisfies L ∅ (C ‘ i) ∅ n φ b ↔ Satisfies L ∅ (codedChainUnion L θ C) ∅ n φ b := by
  let : ℒₛₑₜ-function₄[V] satisfactionGraph := satisfactionGraphFormula_defined.to_definable
  have hL := (h.valid i hi).language
  have hbUnion {i n b : V} (hi : i ∈ θ) (hb : b ∈ structureDomain (C ‘ i) ^ n) :
      b ∈ structureDomain (codedChainUnion L θ C) ^ n := by
    rw [structureDomain_codedChainUnion]
    exact mem_function_of_mem_function_of_subset hb (codedChainCarrier_includes hi)
  have hall : ∀ n φ, φ ∈ formulaSet L ∅ n → ∀ i ∈ θ, ∀ b ∈ structureDomain (C ‘ i) ^ n,
      (Satisfies L ∅ (C ‘ i) ∅ n φ b ↔ Satisfies L ∅ (codedChainUnion L θ C) ∅ n φ b) := by
    apply formulaSet_induction hL ∅
      (fun n φ ↦ ∀ i ∈ θ, ∀ b ∈ structureDomain (C ‘ i) ^ n,
        (Satisfies L ∅ (C ‘ i) ∅ n φ b ↔ Satisfies L ∅ (codedChainUnion L θ C) ∅ n φ b))
      (by unfold Satisfies; definability)
    · intro n hn
      constructor
      · intro i hi b hb
        rw [satisfies_truth hL hn, satisfies_truth hL hn]
        exact iff_of_true hb (hbUnion hi hb)
      · intro i _ b _
        exact iff_of_false (not_satisfies_falsity hL hn) (not_satisfies_falsity hL hn)
    · intro n hn r args ha
      constructor
      · intro i hi b hb
        rw [satisfies_atom hL hn ha hb, satisfies_atom hL hn ha (hbUnion hi hb)]
        exact (h.stage_substructure hi).atomicHolds_iff hn hb ha
      · intro i hi b hb
        rw [satisfies_negAtom hL hn ha hb, satisfies_negAtom hL hn ha (hbUnion hi hb)]
        exact not_congr ((h.stage_substructure hi).atomicHolds_iff hn hb ha)
    · intro n hn φ ψ hφ hψ ihφ ihψ
      constructor
      · intro i hi b hb
        rw [satisfies_and hL hn hφ hψ hb, satisfies_and hL hn hφ hψ (hbUnion hi hb)]
        exact and_congr (ihφ i hi b hb) (ihψ i hi b hb)
      · intro i hi b hb
        rw [satisfies_or hL hn hφ hψ hb, satisfies_or hL hn hφ hψ (hbUnion hi hb)]
        exact or_congr (ihφ i hi b hb) (ihψ i hi b hb)
    · intro n hn φ hφ ih
      constructor
      · intro i hi b hb
        constructor
        · intro hs
          apply (satisfies_all hL hn hφ (hbUnion hi hb)).mpr
          intro x hx
          rw [structureDomain_codedChainUnion] at hx
          obtain ⟨j, hj, hxj⟩ := (mem_codedChainCarrier _ _ _).mp hx
          obtain ⟨k, hk, hik, hjk⟩ := h.common hi hj
          have hbk := mem_function_of_mem_function_of_subset hb (h.increasing i hi k hk hik)
          have hxk := h.increasing j hj k hk hjk x hxj
          have hsk := (h.stage_satisfies_iff hi hk hik hn (formulaSet_quantifiers hL hn hφ).1 hb).mp hs
          exact (ih k hk _ (assignmentPrepend_mem_function hn hbk hxk)).mp
            ((satisfies_all hL hn hφ hbk).mp hsk x hxk)
        · intro hs
          apply (satisfies_all hL hn hφ hb).mpr
          intro x hx
          have hxU : x ∈ structureDomain (codedChainUnion L θ C) := by
            rw [structureDomain_codedChainUnion]
            exact codedChainCarrier_includes hi x hx
          exact (ih i hi _ (assignmentPrepend_mem_function hn hb hx)).mpr
            ((satisfies_all hL hn hφ (hbUnion hi hb)).mp hs x hxU)
      · intro i hi b hb
        constructor
        · intro hs
          obtain ⟨x, hx, hxs⟩ := (satisfies_exists hL hn hφ hb).mp hs
          apply (satisfies_exists hL hn hφ (hbUnion hi hb)).mpr
          refine ⟨x, ?_, (ih i hi _ (assignmentPrepend_mem_function hn hb hx)).mp hxs⟩
          rw [structureDomain_codedChainUnion]
          exact codedChainCarrier_includes hi x hx
        · intro hs
          obtain ⟨x, hx, hxs⟩ := (satisfies_exists hL hn hφ (hbUnion hi hb)).mp hs
          rw [structureDomain_codedChainUnion] at hx
          obtain ⟨j, hj, hxj⟩ := (mem_codedChainCarrier _ _ _).mp hx
          obtain ⟨k, hk, hik, hjk⟩ := h.common hi hj
          have hbk := mem_function_of_mem_function_of_subset hb (h.increasing i hi k hk hik)
          have hxk := h.increasing j hj k hk hjk x hxj
          apply (h.stage_satisfies_iff hi hk hik hn (formulaSet_quantifiers hL hn hφ).2 hb).mpr
          exact (satisfies_exists hL hn hφ hbk).mpr
            ⟨x, hxk, (ih k hk _ (assignmentPrepend_mem_function hn hbk hxk)).mpr hxs⟩
  exact hall n φ hφ i hi b hb

theorem stage_elementary {i : V} (hi : i ∈ θ) :
    IsCodedElementaryEmbedding L (C ‘ i) (codedChainUnion L θ C)
      (SetTheory.identity (structureDomain (C ‘ i))) := by
  refine ⟨h.valid i hi, h.union_valid, ?_, ?_⟩
  · rw [structureDomain_codedChainUnion]
    exact mem_function_of_mem_function_of_subset (identity_mem_function _) (codedChainCarrier_includes hi)
  · intro n hn φ hφ b hb
    rw [graph_compose_identity hb]
    exact h.satisfies_union_iff hi hn hφ hb

theorem union_satisfies_iff_exists_stage {n φ b : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet L ∅ n) (hb : b ∈ structureDomain (codedChainUnion L θ C) ^ n) :
    Satisfies L ∅ (codedChainUnion L θ C) ∅ n φ b ↔
      ∃ i ∈ θ, b ∈ structureDomain (C ‘ i) ^ n ∧ Satisfies L ∅ (C ‘ i) ∅ n φ b := by
  constructor
  · intro hs
    obtain ⟨i, hi, hbi⟩ := h.assignment_stage hn (by simpa only [structureDomain_codedChainUnion] using hb)
    exact ⟨i, hi, hbi, (h.satisfies_union_iff hi hn hφ hbi).mpr hs⟩
  · rintro ⟨i, hi, hbi, hs⟩
    exact (h.satisfies_union_iff hi hn hφ hbi).mp hs

end IsInternalRelationalChain
end ZFVP.Schmerl
