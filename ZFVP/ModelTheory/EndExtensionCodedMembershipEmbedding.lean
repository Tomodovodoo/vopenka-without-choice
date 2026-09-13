import ZFVP.Syntax.EndExtensionMembershipSatisfaction
import ZFVP.ModelTheory.SigmaOneMembershipEmbedding

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
namespace MembershipEndExtension
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem codedMembershipEmbedding_map (j : MembershipEndExtension V W) {A B f : V}
    (hf : IsCodedMembershipEmbedding A B f) : IsCodedMembershipEmbedding (j A) (j B) (j f) := by
  apply codedMembershipEmbedding_iff_valid_satisfaction.mpr
  refine ⟨(j.nonempty_iff A).mpr hf.source_nonempty, (j.nonempty_iff B).mpr hf.target_nonempty,
    (j.function_iff f A B).mpr hf.function, ?_⟩
  intro n φ b hφ hb
  obtain ⟨m, ψ, rfl, rfl, hψ⟩ := j.membershipFormulaCode_preimages hφ
  rw [← j.map_finiteFunctionSet A hψ.context] at hb
  obtain ⟨a, ha, rfl⟩ := j.endExtension _ b hb
  rw [← j.map_compose, j.membershipSatisfies_iff, j.membershipSatisfies_iff]
  exact (codedMembershipEmbedding_iff_valid_satisfaction.mp hf).2.2.2 m ψ a hψ ha

end MembershipEndExtension
end ZFVP
