import ZFVP.ModelTheory.EmbeddingCofinality
import ZFVP.SetTheory.Cofinality
import ZFVP.SetTheory.CofinalityDictionary

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankEmbedding_criticalPoint_regular {k l : ℕ} {δ ε f κ : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ) : IsRegularCardinal κ := by
  let := hδ.ordinal
  let := hε.ordinal
  let := hierarchy_transitive ε
  let := hκ.ordinal
  let : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff k δ).mp hδ).2.support
  refine ⟨rankEmbedding_criticalPoint_initial hδ hε h hκ,
    IsOrdinal.toIsTransitive.transitive _ (hκ.omega_lt h), ?_⟩
  rcases IsOrdinal.subset_iff.mp (internalCofinality_subset κ) with he | hlt
  · exact he
  · obtain ⟨g, hg⟩ := cofinalMap_exists κ
    exact False.elim (rankEmbedding_criticalPoint_no_cofinalMap hδ hε h hκ
      (ordinal_subset_hierarchy κ _ hlt) hg)

end ZFVP
