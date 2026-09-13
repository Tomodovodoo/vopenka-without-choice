import ZFVP.ModelTheory.ReflectedPairWitnessTable
import ZFVP.SetTheory.ForcingPairNames
import ZFVP.SetTheory.RankBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace IsElementaryInclusion

 theorem bounded_doubleton_mem {Y B a b : V} (hY : IsElementaryInclusion Y B) [IsTransitive B]
    (ha : a ∈ Y) (hb : b ∈ Y) (hab : ({a, b} : V) ∈ B) : ({a, b} : V) ∈ Y := by
  obtain ⟨z, hz, he⟩ := hY.bounded_witness boundedDoubletonFormula_bounded ![a, b]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, ha, hb])
    ⟨{a, b}, hab, by simpa [pair_eq_doubleton]⟩
  have heq : z = ({a, b} : V) := by simpa [pair_eq_doubleton] using he
  exact heq ▸ hz

theorem pairName_mem_of_rank {Y α β p σ τ : V} [IsOrdinal α] [IsOrdinal β]
    (hY : IsElementaryInclusion Y (hierarchy β)) (hαβ : α ⊆ β)
    (hα : ∀ ξ ∈ α, succ ξ ∈ α)
    (hp : p ∈ Y ∩ hierarchy α) (hσ : σ ∈ Y ∩ hierarchy α) (hτ : τ ∈ Y ∩ hierarchy α) :
    pairName p σ τ ∈ Y ∩ hierarchy α := by
  let := hierarchy_transitive β
  have hsp := kpair_mem_hierarchy_limit hα (mem_inter_iff.mp hσ).2 (mem_inter_iff.mp hp).2
  have htp := kpair_mem_hierarchy_limit hα (mem_inter_iff.mp hτ).2 (mem_inter_iff.mp hp).2
  have hspY := hY.kpair_mem (mem_inter_iff.mp hσ).1 (mem_inter_iff.mp hp).1 (hierarchy_mono hαβ _ hsp)
  have htpY := hY.kpair_mem (mem_inter_iff.mp hτ).1 (mem_inter_iff.mp hp).1 (hierarchy_mono hαβ _ htp)
  have hr := pair_mem_hierarchy_limit hα hsp htp
  exact mem_inter_iff.mpr ⟨hY.bounded_doubleton_mem hspY htpY (hierarchy_mono hαβ _ hr), hr⟩

theorem orderedPairName_mem_of_rank {Y α β p σ τ : V} [IsOrdinal α] [IsOrdinal β]
    (hY : IsElementaryInclusion Y (hierarchy β)) (hαβ : α ⊆ β)
    (hα : ∀ ξ ∈ α, succ ξ ∈ α)
    (hp : p ∈ Y ∩ hierarchy α) (hσ : σ ∈ Y ∩ hierarchy α) (hτ : τ ∈ Y ∩ hierarchy α) :
    orderedPairName p σ τ ∈ Y ∩ hierarchy α :=
  hY.pairName_mem_of_rank hαβ hα hp (hY.pairName_mem_of_rank hαβ hα hp hσ hσ)
    (hY.pairName_mem_of_rank hαβ hα hp hσ hτ)

end IsElementaryInclusion
end ZFVP
