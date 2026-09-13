import ZFVP.ModelTheory.FiniteRankLiftGraph
import ZFVP.ModelTheory.FiniteRankCheckNameCovariance

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace FiniteRankLiftData

variable {A B : ForcingContext V} {δ ε e π : V} (L : FiniteRankLiftData A B δ ε e)
  (hπ : IsForcingRetraction A.P A.R B.P B.R π)
  (hG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P)

include L

theorem one_mem_source : A.one ∈ hierarchy δ := by
  exact L.poset_subset _ A.top.1

theorem checkName_mem_source {x : V} (hx : x ∈ hierarchy δ) : checkName A.one x ∈ hierarchy δ :=
  L.source_inaccessible.checkName_mem_hierarchy L.one_mem_source hx

theorem check_mem_graph_domain (hone : A.one = B.one) {x : V} (hx : x ∈ hierarchy δ) :
    B.check x ∈ domain (L.graph hπ) := by
  apply (L.graph_domain hπ _).mpr
  refine ⟨⟨checkName A.one x, checkName_isName A.top.1 x⟩, L.checkName_mem_source hx, ?_⟩
  change B.ofName ⟨checkName B.one x, _⟩ = B.ofName ⟨checkName A.one x, _⟩
  congr 1
  exact Subtype.ext (congrArg (fun one ↦ checkName one x) hone.symm)

include hG in
theorem graph_check (hone : A.one = B.one) (heone : e ‘ A.one = B.one)
    {x : V} (hx : x ∈ hierarchy δ) : (L.graph hπ) ‘ (B.check x) = B.check (e ‘ x) := by
  let := L.target_inaccessible.1
  let := hierarchy_transitive (ordinalAdd ε (ω : V))
  let τ : ForcingName A.P := ⟨checkName A.one x, checkName_isName A.top.1 x⟩
  have ht : B.ofName ⟨τ.val, τ.property.mono hπ.inclusion⟩ = B.check x := by
    change B.ofName ⟨checkName A.one x, _⟩ = B.ofName ⟨checkName B.one x, _⟩
    congr 1
    exact Subtype.ext (congrArg (fun one ↦ checkName one x) hone)
  rw [← ht, L.graph_value hπ hG τ (L.checkName_mem_source hx)]
  change B.ofName ⟨e ‘ (checkName A.one x), _⟩ = B.ofName ⟨checkName B.one (e ‘ x), _⟩
  congr 1
  apply Subtype.ext
  change e ‘ (checkName A.one x) = checkName B.one (e ‘ x)
  rw [finiteRankEmbedding_value_checkName L.source_inaccessible L.embedding
    L.one_mem_source hx, heone]

end FiniteRankLiftData
end ZFVP

