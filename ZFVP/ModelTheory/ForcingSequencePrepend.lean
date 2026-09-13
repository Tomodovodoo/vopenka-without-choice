import ZFVP.ModelTheory.ForcingSequenceEvaluationGraph

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem sequenceValue_prepend (S : ForcingContext V) {C n b x : V}
    (hC : ∀ σ ∈ C, IsForcingName S.P σ) (hn : n ∈ (ω : V)) (hb : b ∈ C ^ n) (hx : x ∈ C) :
    S.sequenceValue (assignmentPrepend n b x) (S.nameSequence_of_mem_function hC (assignmentPrepend_mem_function hn hb hx)) =
      assignmentPrepend (S.check n) (S.sequenceValue b (S.nameSequence_of_mem_function hC hb)) (S.ofName ⟨x, hC x hx⟩) := by
  let hsN := S.nameSequence_of_mem_function hC hb
  let htN := S.nameSequence_of_mem_function hC (assignmentPrepend_mem_function hn hb hx)
  have hn' : S.check n ∈ (ω : S.Model) := by
    rw [← S.checkEmbedding.map_omega]
    exact (S.check_mem_iff n ω).mpr hn
  apply functions_eq_of_domain_values
  · rw [S.sequenceValue_domain, domain_assignmentPrepend, domain_assignmentPrepend, S.check_succ]
  · intro a ha
    rw [S.sequenceValue_domain, domain_assignmentPrepend] at ha
    obtain ⟨i, hi, rfl⟩ := (S.mem_check_iff (succ n) a).mp ha
    change (S.sequenceValue (assignmentPrepend n b x) htN) ‘ (S.check i) =
      (assignmentPrepend (S.check n) (S.sequenceValue b hsN) (S.ofName ⟨x, hC x hx⟩)) ‘ (S.check i)
    rw [S.sequenceValue_value _ _ (by rwa [domain_assignmentPrepend])]
    by_cases hi0 : i = 0
    · subst i
      rw [show S.check (0 : V) = (0 : S.Model) from S.checkEmbedding.map_numeral 0,
        assignmentPrepend_zero hn']
      apply congrArg S.ofName
      exact Subtype.ext (assignmentPrepend_zero hn b x)
    · have hip : ⋃ˢ i ∈ n := natural_predecessor_mem hn hi hi0
      have hipd : ⋃ˢ i ∈ domain b := (domain_eq_of_mem_function hb).symm ▸ hip
      have hi0' : S.check i ≠ (0 : S.Model) := by
        intro h
        apply hi0
        exact (S.check_eq_iff i 0).mp (h.trans (S.checkEmbedding.map_numeral 0).symm)
      have hi' : S.check i ∈ succ (S.check n) := by
        rw [← S.check_succ]
        exact (S.check_mem_iff i (succ n)).mpr hi
      have hval : (assignmentPrepend n b x) ‘ i = b ‘ (⋃ˢ i) := by
        simpa only [assignmentPrepend, prependValue, ite_eq_right hi0] using
          value_definableGraph (succ n) (prependValue b x) (by definability) hi
      have hval' : (assignmentPrepend (S.check n) (S.sequenceValue b hsN) (S.ofName ⟨x, hC x hx⟩)) ‘ (S.check i) =
          (S.sequenceValue b hsN) ‘ (S.check (⋃ˢ i)) := by
        rw [show S.check (⋃ˢ i) = ⋃ˢ (S.check i) from S.checkEmbedding.map_sUnion i]
        simpa only [assignmentPrepend, prependValue, ite_eq_right hi0'] using
          value_definableGraph (succ (S.check n)) (prependValue (S.sequenceValue b hsN) (S.ofName ⟨x, hC x hx⟩))
            (by definability) hi'
      rw [hval', S.sequenceValue_value b hsN hipd]
      apply congrArg S.ofName
      exact Subtype.ext hval

end ForcingContext
end ZFVP
