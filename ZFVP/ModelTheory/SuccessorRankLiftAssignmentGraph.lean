import ZFVP.ModelTheory.SuccessorRankLiftTruth
import ZFVP.ModelTheory.SuccessorRankLiftDomain

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace SuccessorRankLiftData
variable {A B : ForcingContext V} {δ ε e π : V} (L : SuccessorRankLiftData A B δ ε e)
  (hπ : IsForcingRetraction A.P A.R B.P B.R π)
  (hG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P)

theorem source_sequence_mem_graph_domain {n b : V} (hb : b ∈ lowRankNameSet A.P δ ^ n) :
    B.sequenceValue b (fun i hi ↦ (A.nameSequence_of_mem_function (A.lowRankNameSet_names δ) hb i hi).mono hπ.inclusion) ∈
      domain (L.graph hπ) ^ B.check n := by
  have hh := B.sequenceValue_mem_function b
    (fun i hi ↦ (A.nameSequence_of_mem_function (A.lowRankNameSet_names δ) hb i hi).mono hπ.inclusion)
    (A := domain (L.graph hπ)) (by
      intro i hi
      have hiv := function_value_mem hb (domain_eq_of_mem_function hb ▸ hi)
      exact (L.graph_domain hπ _).mpr ⟨⟨b ‘ i, A.lowRankNameSet_names δ _ hiv⟩,
        (mem_lowRankNameSet A.P δ _).mp hiv |>.1, rfl⟩)
  simpa only [domain_eq_of_mem_function hb] using hh

include hG in
theorem graph_compose_sequence {n b : V} (hn : n ∈ (ω : V)) (hb : b ∈ lowRankNameSet A.P δ ^ n) :
    compose (B.sequenceValue b
      (fun i hi ↦ (A.nameSequence_of_mem_function (A.lowRankNameSet_names δ) hb i hi).mono hπ.inclusion)) (L.graph hπ) =
    B.sequenceValue (e ‘ b) (B.nameSequence_of_mem_function (B.lowRankNameSet_names ε) (L.image_assignment hn hb)) := by
  let hs := A.nameSequence_of_mem_function (A.lowRankNameSet_names δ) hb
  let hsB : IsNameSequence B.P b := fun i hi ↦ (hs i hi).mono hπ.inclusion
  let ht := B.nameSequence_of_mem_function (B.lowRankNameSet_names ε) (L.image_assignment hn hb)
  let := L.graph_isFunction hπ hG
  have hsrc := L.source_sequence_mem_graph_domain hπ hb
  have hf := compose_function hsrc (IsFunction.mem_function (L.graph hπ))
  let := IsFunction.of_mem hf
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hf, B.sequenceValue_domain,
      domain_eq_of_mem_function (L.image_assignment hn hb)]
  · intro a ha
    rw [domain_eq_of_mem_function hf] at ha
    obtain ⟨i, hi, rfl⟩ := (B.mem_check_iff n a).mp ha
    change (compose (B.sequenceValue b hsB) (L.graph hπ)) ‘ (B.check i) =
      (B.sequenceValue (e ‘ b) ht) ‘ (B.check i)
    rw [value_compose_of_mem_function hsrc (IsFunction.mem_function (L.graph hπ)) ((B.check_mem_iff _ _).mpr hi),
      B.sequenceValue_value b hsB (domain_eq_of_mem_function hb ▸ hi),
      B.sequenceValue_value (e ‘ b) ht (domain_eq_of_mem_function (L.image_assignment hn hb) ▸ hi)]
    have hiv := function_value_mem hb hi
    have hr := (mem_lowRankNameSet A.P δ _).mp hiv |>.1
    rw [L.graph_value hπ hG ⟨b ‘ i, A.lowRankNameSet_names δ _ hiv⟩ hr]
    apply congrArg B.ofName
    apply Subtype.ext
    exact ((successorRankEmbedding_nameAssignment L.source_correct L.target_correct L.embedding L.poset_mem hn hb).2 i hi).symm

end SuccessorRankLiftData
end ZFVP
