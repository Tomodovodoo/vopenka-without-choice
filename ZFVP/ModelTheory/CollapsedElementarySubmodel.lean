import ZFVP.ModelTheory.ElementaryRange
import ZFVP.SetTheory.TransitiveCollapseFixation

/-! The inverse collapse of an elementary submodel is an internal elementary
embedding from a transitive set. No correctness assumption on the ambient rank. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem transitiveCollapse_codedEmbedding {X C f : V}
    (hf : IsTransitiveCollapse (membershipRelation X) X C f) (hX : IsNonempty X) :
    IsCodedMembershipEmbedding X C f := by
  let := IsFunction.of_mem hf.2.1
  refine codedMembershipEmbedding_of_isomorphism hX hf.2.1 ?_ hf.2.2.1 ?_
  · intro x y z hx hy
    have hxX := (mem_of_mem_functions hf.2.1 hx).1
    have hyX := (mem_of_mem_functions hf.2.1 hy).1
    exact hf.2.2.2.1 x hxX y hyX ((value_eq_of_kpair_mem hx).trans (value_eq_of_kpair_mem hy).symm)
  · intro x hx y hy
    rw [hf.2.2.2.2 x hx y hy, pair_mem_membershipRelation]
    simp [hx, hy]

theorem transitiveCollapse_inverse_elementary {X B C f : V}
    (hX : IsElementaryInclusion X B)
    (hf : IsTransitiveCollapse (membershipRelation X) X C f) :
    IsCodedMembershipEmbedding C B (converseGraph f) := by
  have he := transitiveCollapse_codedEmbedding hf hX.source_nonempty
  have hi := he.inverse_elementary
  rw [hf.2.2.1] at hi
  have hc := hi.comp hX
  rw [graph_compose_identity hi.function] at hc
  exact hc

theorem transitiveCollapse_inverse_value {X C f x : V}
    (hf : IsTransitiveCollapse (membershipRelation X) X C f) (hx : x ∈ X) :
    (converseGraph f) ‘ (f ‘ x) = x := by
  have hi : Injective f := by
    let := IsFunction.of_mem hf.2.1
    intro u v z hu hv
    exact hf.2.2.2.1 u (mem_of_mem_functions hf.2.1 hu).1
      v (mem_of_mem_functions hf.2.1 hv).1
      ((value_eq_of_kpair_mem hu).trans (value_eq_of_kpair_mem hv).symm)
  exact converseGraph_value_value hf.2.1 hi hx

theorem transitiveCollapse_inverse_fixes {X C f D x : V}
    (hf : IsTransitiveCollapse (membershipRelation X) X C f)
    [IsTransitive D] (hDX : D ⊆ X) (hx : x ∈ D) :
    x ∈ C ∧ (converseGraph f) ‘ x = x := by
  have hfix := transitiveCollapse_fixes_transitive_subset hf hDX x hx
  refine ⟨hfix ▸ function_value_mem hf.2.1 (hDX x hx), ?_⟩
  rw [← hfix]
  rw [transitiveCollapse_inverse_value hf (hDX x hx), hfix]

end ZFVP

