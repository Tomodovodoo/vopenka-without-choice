import ZFVP.SetTheory.OrdinalDependentChoice

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A finite tuple of values of a function has a tuple of preimages in its domain. -/
theorem finite_function_lift {E X Y n b : V} (hE : E ∈ Y ^ X)
    (hn : n ∈ (ω : V)) (hb : b ∈ range E ^ n) :
    ∃ s ∈ X ^ n, ∀ i ∈ n, E ‘ (s ‘ i) = b ‘ i := by
  let := IsFunction.of_mem hE
  have hall : ∀ n ∈ (ω : V), ∀ b ∈ range E ^ n,
      ∃ s ∈ X ^ n, ∀ i ∈ n, E ‘ (s ‘ i) = b ‘ i := by
    apply naturalNumber_induction (fun n ↦ ∀ b ∈ range E ^ n,
      ∃ s ∈ X ^ n, ∀ i ∈ n, E ‘ (s ‘ i) = b ‘ i) (by definability) ?_ ?_
    · intro b _
      refine ⟨∅, by simp [zero_def, mem_function_iff], ?_⟩
      intro i hi
      simp [zero_def] at hi
    · intro n _ ih b hb
      obtain ⟨t, y, ht, hy, rfl⟩ := function_succ_decompose hb
      obtain ⟨s, hs, hvalues⟩ := ih t ht
      obtain ⟨x, hxy⟩ := mem_range_iff.mp hy
      have hx : x ∈ X := (mem_of_mem_functions hE hxy).1
      have hEx : E ‘ x = y := value_eq_of_kpair_mem hxy
      refine ⟨insert ⟨n, x⟩ₖ s, function_append_mem hs hx, fun i hi ↦ ?_⟩
      rcases mem_succ_iff.mp hi with rfl | hi
      · rw [function_append_value_new hs hx, function_append_value_new ht hy]
        exact hEx
      · rw [function_append_value_old hs hx hi, function_append_value_old ht hy hi]
        exact hvalues i hi
  exact hall n hn b hb

end ZFVP
