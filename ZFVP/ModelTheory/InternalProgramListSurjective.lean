import ZFVP.ModelTheory.InternalProgramListExt
import ZFVP.ModelTheory.StandardProgramLists
import ZFVP.Syntax.BoundedAssignments

/-! Every internally finite sequence of naturals has a unique natural-number code. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem function_prepend_decompose {A s n : V} (hn : n ∈ (ω : V)) (hs : s ∈ A ^ SetTheory.succ n) :
    ∃ t x, t ∈ A ^ n ∧ x ∈ A ∧ s = assignmentPrepend n t x := by
  have : IsFunction s := IsFunction.of_mem hs
  let t := definableGraph n (fun i : V ↦ s ‘ (SetTheory.succ i)) (by definability)
  have ht : t ∈ A ^ n := by
    apply definableGraph_mem_function_of_mapsTo
    intro i hi
    exact function_value_mem hs (succ_mem_succ_of_natural_mem hn hi)
  refine ⟨t, s ‘ (0 : V), ht, function_value_mem hs (zero_mem_succ_natural hn), ?_⟩
  apply assignmentPrepend_eq_of_pairs hn hs
  · apply kpair_value_mem
    simpa only [domain_eq_of_mem_function hs] using zero_mem_succ_natural hn
  · intro i hi
    have hv : t ‘ i = s ‘ (SetTheory.succ i) := value_definableGraph _ _ _ hi
    rw [hv]
    apply kpair_value_mem
    simpa only [domain_eq_of_mem_function hs] using succ_mem_succ_of_natural_mem hn hi

@[simp] theorem decodedNaturalList_zero : decodedNaturalList (0 : V) = ∅ := by
  have h := decodedNaturalList_encode_tuple (V := V) []
  simpa [standardTuple, zero_def] using h

theorem decodedNaturalList_surjective_function {n s : V} (hn : n ∈ (ω : V))
    (hs : s ∈ (ω : V) ^ n) : ∃ x ∈ (ω : V), decodedNaturalList x = s := by
  have h : ∀ n ∈ (ω : V), ∀ s ∈ (ω : V) ^ n, ∃ x ∈ (ω : V), decodedNaturalList x = s := by
    apply naturalNumber_induction (fun n : V ↦ ∀ s ∈ (ω : V) ^ n, ∃ x ∈ (ω : V), decodedNaturalList x = s)
      (by definability)
    · intro s hs
      have : IsFunction s := IsFunction.of_mem hs
      have he : s = ∅ := by
        apply functions_eq_of_domain_values
        · simp [domain_eq_of_mem_function hs, zero_def]
        · intro i hi
          simp [domain_eq_of_mem_function hs, zero_def] at hi
      exact ⟨0, by simp [zero_def], by simp [he]⟩
    · intro n hn ih s hs
      obtain ⟨t, x, ht, hx, he⟩ := function_prepend_decompose hn hs
      obtain ⟨c, hc, hct⟩ := ih t ht
      have hlen : listLength.evalSet c = n := by
        have hd := congrArg domain hct
        simpa only [domain_decodedNaturalList, domain_eq_of_mem_function ht] using hd
      refine ⟨SetTheory.succ (naturalSquarePair x c), ω_succ_closed (naturalSquarePair_natural hx hc), ?_⟩
      rw [decodedNaturalList_cons hx hc, hlen, hct]
      exact he.symm
  exact h n hn s hs

theorem decodedNaturalList_surjective {s : V} (hs : s ∈ finiteSequences (ω : V)) :
    ∃ x ∈ (ω : V), decodedNaturalList x = s := by
  obtain ⟨n, hn, hs⟩ := (mem_finiteSequences_iff _ _).mp hs
  exact decodedNaturalList_surjective_function hn hs

theorem decodedNaturalList_unique_code {s : V} (hs : s ∈ finiteSequences (ω : V)) :
    ∃! x, x ∈ (ω : V) ∧ decodedNaturalList x = s := by
  obtain ⟨x, hx, he⟩ := decodedNaturalList_surjective hs
  refine ⟨x, ⟨hx, he⟩, ?_⟩
  rintro y ⟨hy, hey⟩
  exact decodedNaturalList_injective hy hx (hey.trans he.symm)

end ZFVP
