import ZFVP.SetTheory.UniquePiWitnessCodes
import ZFVP.SetTheory.CodingUniverse

/-! A least-witness code stays in any limit rank containing one witness. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem LeastWitnessBody.rank_subset_of_witness {n : ℕ} {ψ : SetTheorySemisentence (n + 1)}
    {v : Fin n → V} {α A B C u : V} (h : LeastWitnessBody ψ v α A B C)
    (hu : ψ.Evalb (u :> v)) : α ⊆ rank u := by
  let := h.1
  rcases IsOrdinal.mem_trichotomy α (rank u) with hl | he | hg
  · exact IsOrdinal.toIsTransitive.transitive _ hl
  · exact subset_of_eq he
  · have hua : u ∈ A := by
      rw [h.2.1, mem_hierarchy_iff_rank_mem]
      exact hg
    exact False.elim (h.2.2.2.2.2.1 u hua hu)

theorem IsLeastWitnessCode.mem_hierarchy_limit {n : ℕ} {ψ : SetTheorySemisentence (n + 1)}
    {v : Fin n → V} {c κ u : V} [IsOrdinal κ]
    (hκ : ∀ β ∈ κ, succ β ∈ κ) (hc : IsLeastWitnessCode ψ v c)
    (hu : u ∈ hierarchy κ) (hψ : ψ.Evalb (u :> v)) : c ∈ hierarchy κ := by
  obtain ⟨α, A, B, C, rfl, h⟩ := hc
  let := h.1
  have hαr := h.rank_subset_of_witness hψ
  have hrκ := (mem_hierarchy_iff_rank_mem u κ).mp hu
  have hακ : α ∈ κ := by
    rcases IsOrdinal.subset_iff.mp hαr with he | hl
    · exact he ▸ hrκ
    · exact IsOrdinal.toIsTransitive.mem_trans hl hrκ
  have hα : α ∈ hierarchy κ := ordinal_subset_hierarchy κ α hακ
  have hA : A ∈ hierarchy κ := h.2.1 ▸ hierarchy_mem hακ
  have hB : B ∈ hierarchy κ := h.2.2.1 ▸ hierarchy_mem (hκ α hακ)
  have hC : C ∈ hierarchy κ := subset_mem_hierarchy_limit hκ hB h.2.2.2.2.1
  exact kpair_mem_hierarchy_limit hκ hα
    (kpair_mem_hierarchy_limit hκ hA (kpair_mem_hierarchy_limit hκ hB hC))

end ZFVP
