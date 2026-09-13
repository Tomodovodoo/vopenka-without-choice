import ZFVP.ModelTheory.FiniteRankLiftChecks
import ZFVP.ModelTheory.CriticalPoint

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace FiniteRankLiftData
variable {A B : ForcingContext V} {δ ε e π κ : V} (L : FiniteRankLiftData A B δ ε e)
  (hπ : IsForcingRetraction A.P A.R B.P B.R π)
  (hG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P)

include hG

theorem graph_criticalPoint
    (hκ : IsCriticalPoint (hierarchy (ordinalAdd δ (ω : V))) e κ) (hκδ : κ ∈ δ)
    (hone : A.one = B.one) (heone : e ‘ A.one = B.one) :
    IsCriticalPoint (domain (L.graph hπ)) (L.graph hπ) (B.check κ) := by
  let := L.source_inaccessible.1
  let := hκ.ordinal
  let := hierarchy_transitive (ordinalAdd δ (ω : V))
  have hκV : κ ∈ hierarchy δ := ordinal_mem_hierarchy_iff.mpr hκδ
  have hmove : (L.graph hπ) ‘ (B.check κ) ≠ B.check κ := by
    rw [L.graph_check hπ hG hone heone hκV]
    exact fun h ↦ hκ.moved ((B.check_eq_iff _ _).mp h)
  refine ⟨inferInstance, ⟨L.check_mem_graph_domain hπ hone hκV, hmove⟩, ?_⟩
  intro α hα hαmove
  let := hα
  rcases IsOrdinal.mem_trichotomy (B.check κ) α with hlt | heq | hgt
  · exact IsOrdinal.toIsTransitive.transitive _ hlt
  · rw [heq]
  · obtain ⟨a, ha, rfl⟩ := (B.mem_check_iff κ α).mp hgt
    have haV := (hierarchy_transitive δ).mem_trans ha hκV
    exact False.elim (hαmove.2 (by rw [L.graph_check hπ hG hone heone haV, hκ.fixed_below ha]))

theorem graph_criticalPoint_image
    (hκ : IsCriticalPoint (hierarchy (ordinalAdd δ (ω : V))) e κ) (hκδ : κ ∈ δ)
    (hone : A.one = B.one) (heone : e ‘ A.one = B.one) :
    IsCriticalPoint (domain (L.graph hπ)) (L.graph hπ) (B.check κ) ∧
      (L.graph hπ) ‘ (B.check κ) = B.check (e ‘ κ) := by
  let := L.source_inaccessible.1
  let := hκ.ordinal
  exact ⟨L.graph_criticalPoint hπ hG hκ hκδ hone heone,
    L.graph_check hπ hG hone heone (ordinal_mem_hierarchy_iff.mpr hκδ)⟩

end FiniteRankLiftData
end ZFVP
