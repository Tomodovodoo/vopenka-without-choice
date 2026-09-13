import ZFVP.ModelTheory.SuccessorRankGenericGraph

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SuccessorRankLiftData
variable {A B : ForcingContext V} {δ ε e : V} (L : SuccessorRankLiftData A B δ ε e)
  (hP : A.P ⊆ B.P) (hG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P)

theorem genericGraph_function_closed {γ : V} (hγ : γ ∈ hierarchy δ)
    (hpre : ∀ (X : A.Model) (f : B.Model),
      f ∈ A.genericInclusion B hG X ^ B.check γ →
      ∃ g ∈ X ^ A.check γ, A.genericInclusion B hG g = f)
    {X f : B.Model} (hX : X ∈ domain (L.genericGraph hP)) (hf : f ∈ X ^ B.check γ) :
    f ∈ domain (L.genericGraph hP) := by
  let := L.source_correct.ordinal
  let j := A.genericInclusion B hG
  rw [L.genericGraph_domain_eq_rank_image hP hG] at hX ⊢
  obtain ⟨Y, hY, rfl⟩ := j.endExtension (hierarchy (A.check δ)) X hX
  obtain ⟨g, hg, rfl⟩ := hpre Y f hf
  apply (j.mem_iff _ _).mpr
  have hc : ∀ β ∈ A.check δ, succ β ∈ A.check δ := by
    intro β hβ
    obtain ⟨b, hb, rfl⟩ := (A.mem_check_iff δ β).mp hβ
    rw [← A.check_succ]
    exact (A.check_mem_iff _ _).mpr (L.source_correct.successor_closed b hb)
  have hγ' : A.check γ ∈ hierarchy (A.check δ) :=
    A.ofName_mem_checked_hierarchy ⟨checkName A.one γ, checkName_isName A.top.1 γ⟩
      (L.checkName_mem_source hγ)
  exact (hierarchy_transitive (A.check δ)).mem_trans hg
    (function_mem_hierarchy_limit hc hγ' hY)

end SuccessorRankLiftData
end ZFVP
