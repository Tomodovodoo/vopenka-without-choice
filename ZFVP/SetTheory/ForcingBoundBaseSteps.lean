import ZFVP.SetTheory.ForcingBoundFixedExtension
import ZFVP.SetTheory.ForcingIterationTables

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingBound_step_before_base {θ P R π E B i I : V}
    (hθ : succ θ ⊆ i) (hB : IsIterationTable θ B) :
    IsIterationTable (succ θ) (forcingFamilyNext θ B ∅) ∧
    IsCoherentForcingBound (succ θ) P R π (forcingFamilyNext θ B ∅) i I ∧
    IsSectionCompatibleForcingBound (succ θ) P R π E (forcingFamilyNext θ B ∅) i I ∧
    B ⊆ forcingFamilyNext θ B ∅ :=
  ⟨forcingFamilyNext_table _ _ _, coherentForcingBound_before_base hθ,
    sectionCompatibleForcingBound_before_base hθ, forcingFamilyNext_extends hB _⟩

theorem forcingBound_step_at_base {P R π E B i I : V}
    (hB : IsIterationTable i B)
    (hπ : π ‘ ⟨i, i⟩ₖ = identity (P ‘ i))
    (hE : E ‘ ⟨i, i⟩ₖ = identity (P ‘ i)) :
    let C := forcingFamilyNext i B (forcingIdentityBound (P ‘ i) I)
    IsIterationTable (succ i) C ∧ IsCoherentForcingBound (succ i) P R π C i I ∧
    IsSectionCompatibleForcingBound (succ i) P R π E C i I ∧ B ⊆ C := by
  dsimp only
  have last (j : V) (hj : j ∈ succ i) (hij : i ⊆ j) : j = i := by
    rcases mem_succ_iff.mp hj with he | hji
    · exact he
    · exact (mem_irrefl j (hij j hji)).elim
  refine ⟨forcingFamilyNext_table _ _ _, ?_, ?_, forcingFamilyNext_extends hB _⟩
  · constructor
    · intro j hj hij f hf p hp hb
      obtain rfl := last j hj hij
      rw [forcingFamilyNext_new, forcingIdentityBound_value hf.1 hp, hπ, identity_value hp]
      refine ⟨hp, ?_, rfl⟩
      intro a ha
      simpa only [hπ, identity_value (function_value_mem hf.1 ha)] using hb a ha
    · intro j hj k hk hij hjk f hf p hp hb
      obtain rfl := last j hj hij
      obtain rfl := last k hk hjk
      rw [forcingFamilyNext_new, forcingIdentityBound_value hf.1 hp, hπ,
        identity_value hp, graph_compose_identity hf.1, forcingIdentityBound_value hf.1 hp]
  · constructor
    intro j hj k hk hij hjk f hf p hp hb
    obtain rfl := last j hj hij
    obtain rfl := last k hk hjk
    rw [forcingFamilyNext_new, hE, graph_compose_identity hf.1,
      forcingIdentityBound_value hf.1 hp, identity_value hp]

end ZFVP
