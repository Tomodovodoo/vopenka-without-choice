import ZFVP.ModelTheory.ForcingModelEvaluation
import ZFVP.SetTheory.OrdinalMeasureInduction

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem rank_ofName_subset (S : ForcingContext V) (τ : ForcingName S.P) :
    rank (S.ofName τ) ⊆ S.check (rank τ.val) := by
  let C := nameClosure τ.val
  have hC (σ : V) (hσ : σ ∈ C) : IsForcingName S.P σ := forcingName_mem_closure τ.property hσ
  let F := S.evaluationGraph C hC
  let r := definableGraph C rank (by definability)
  let μ : S.Model → S.Model := fun x ↦ (S.check r) ‘ x
  have hμ (σ : V) (hσ : σ ∈ C) : μ (S.check σ) = S.check (rank σ) := by
    change (S.check r) ‘ (S.check σ) = _
    rw [S.check_value (by simpa only [r, domain_definableGraph] using hσ)]
    rw [show r ‘ σ = rank σ from value_definableGraph C rank (by definability) hσ]
  have hF (σ : V) (hσ : σ ∈ C) : F ‘ (S.check σ) = S.ofName ⟨σ, hC σ hσ⟩ :=
    S.evaluationGraph_value C hC σ hσ
  have hord (x : S.Model) (hx : x ∈ S.check C) : IsOrdinal (μ x) := by
    obtain ⟨σ, hσ, rfl⟩ := (S.mem_check_iff C x).mp hx
    rw [hμ σ hσ]
    infer_instance
  have hall := ordinalMeasure_induction (S.check C) μ (by unfold μ; definability) hord
    (fun x ↦ rank (F ‘ x) ⊆ μ x) (by unfold μ; definability) ?_
  · have ht := hall (S.check τ.val) ((S.check_mem_iff _ _).mpr (mem_nameClosure_self τ.val))
    simpa only [hF τ.val (mem_nameClosure_self τ.val), hμ τ.val (mem_nameClosure_self τ.val)] using ht
  intro x hx ih
  obtain ⟨σ, hσ, rfl⟩ := (S.mem_check_iff C x).mp hx
  rw [hF σ hσ, hμ σ hσ]
  apply rank_minimal _ _ inferInstance
  intro z hz
  obtain ⟨ν, p, _, hνp, rfl⟩ := (S.mem_ofName_iff ⟨σ, hC σ hσ⟩ z).mp hz
  have hνC : ν.val ∈ C := nameClosure_closed τ.val σ hσ ν.val (mem_domain_of_kpair_mem hνp)
  have hlt : S.check (rank ν.val) ∈ S.check (rank σ) := (S.check_mem_iff _ _).mpr (rank_subname_lt hνp)
  have hbound := ih (S.check ν.val) ((S.check_mem_iff _ _).mpr hνC) (by rwa [hμ ν.val hνC, hμ σ hσ])
  rw [hF ν.val hνC, hμ ν.val hνC] at hbound
  apply (mem_hierarchy_iff_rank_mem _ _).mpr
  rcases IsOrdinal.subset_iff.mp hbound with he | hm
  · exact he.symm ▸ hlt
  · exact IsOrdinal.toIsTransitive.mem_trans hm hlt

theorem ordinal_eq_check (S : ForcingContext V) (α : S.Model) [IsOrdinal α] :
    ∃ β : V, IsOrdinal β ∧ α = S.check β := by
  obtain ⟨τ, rfl⟩ := S.ofName_surjective α
  have hb := S.rank_ofName_subset τ
  rw [rank_of_ordinal] at hb
  rcases IsOrdinal.subset_iff.mp hb with he | hm
  · exact ⟨rank τ.val, inferInstance, he⟩
  · obtain ⟨β, hβ, he⟩ := (S.mem_check_iff (rank τ.val) _).mp hm
    exact ⟨β, IsOrdinal.of_mem hβ, he⟩

end ForcingContext
end ZFVP
