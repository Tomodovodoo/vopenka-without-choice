import ZFVP.SetTheory.ForcingNameHierarchy
import ZFVP.SetTheory.CnSigmaClosure
import ZFVP.SetTheory.WitnessClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private theorem ordinal_succ_subset_of_mem {a b : V} [IsOrdinal b] (h : a ∈ b) : succ a ⊆ b := by
  intro z hz
  rcases mem_succ_iff.mp hz with rfl | hz
  · exact h
  · exact IsOrdinal.toIsTransitive.mem_trans hz h

private theorem pair_rank_lower (a b : V) :
    succ (succ (rank a ∪ rank b)) ⊆ rank ⟨a, b⟩ₖ := by
  let := ordinal_union_ordinal (rank a) (rank b)
  have ha : rank a ∈ rank ({a, b} : V) := rank_mem (by simp)
  have hb : rank b ∈ rank ({a, b} : V) := rank_mem (by simp)
  have hu : rank a ∪ rank b ∈ rank ({a, b} : V) := by
    rcases IsOrdinal.subset_or_supset (rank a) (rank b) with h | h
    · have he : rank a ∪ rank b = rank b := subset_antisymm
        (fun z hz ↦ (mem_union_iff.mp hz).elim (h z) id)
        (fun z hz ↦ mem_union_iff.mpr (.inr hz))
      rwa [he]
    · have he : rank a ∪ rank b = rank a := subset_antisymm
        (fun z hz ↦ (mem_union_iff.mp hz).elim id (h z))
        (fun z hz ↦ mem_union_iff.mpr (.inl hz))
      rwa [he]
  have hd : rank ({a, b} : V) ∈ rank ⟨a, b⟩ₖ := rank_mem (by simp [kpair])
  have hs := ordinal_succ_subset_of_mem hu
  have hsm : succ (rank a ∪ rank b) ∈ rank ⟨a, b⟩ₖ := by
    rcases IsOrdinal.subset_iff.mp hs with he | hm
    · exact he.symm ▸ hd
    · exact IsOrdinal.toIsTransitive.mem_trans hm hd
  exact ordinal_succ_subset_of_mem hsm

theorem forcingNameHierarchy_subset_check_rank (P α : V) [IsOrdinal α] :
    forcingNameHierarchy P α ⊆ hierarchy (rank (checkName P α)) := by
  have hall := transfinite_induction
    (fun α ↦ forcingNameHierarchy P α ⊆ hierarchy (rank (checkName P α))) (by definability) ?_
  · exact hall (IsOrdinal.toOrdinal α)
  intro β ih ν hν
  obtain ⟨γ, hγ, hν⟩ := (mem_forcingNameHierarchy P (β : V) ν).mp hν
  let := IsOrdinal.of_mem hγ
  let a := checkName P γ
  let r := rank a ∪ rank P
  have hr : IsOrdinal r := ordinal_union_ordinal _ _
  have hn : ν ⊆ hierarchy (rank ⟨a, P⟩ₖ) := by
    intro z hz
    obtain ⟨x, hx, p, hp, rfl⟩ := mem_prod_iff.mp (hν z hz)
    have hxV := ih (IsOrdinal.toOrdinal γ) hγ x hx
    have hxR : x ∈ hierarchy r := hierarchy_mono
      (fun z hz ↦ mem_union_iff.mpr (.inl hz)) x hxV
    have hpR : p ∈ hierarchy r := hierarchy_mono
      (fun z hz ↦ mem_union_iff.mpr (.inr hz)) p (subset_hierarchy_rank P p hp)
    exact hierarchy_mono (pair_rank_lower a P) _ (kpair_mem_hierarchy_succ_succ hxR hpR)
  have hle := rank_minimal ν (rank ⟨a, P⟩ₖ) inferInstance hn
  have hlt : rank ⟨a, P⟩ₖ ∈ rank (checkName P (β : V)) :=
    rank_mem ((mem_checkName_iff P (β : V) _).mpr ⟨γ, hγ, rfl⟩)
  apply (mem_hierarchy_iff_rank_mem _ _).mpr
  rcases IsOrdinal.subset_iff.mp hle with he | hm
  · exact he.symm ▸ hlt
  · exact IsOrdinal.toIsTransitive.mem_trans hm hlt

theorem Cn.forcingNameHierarchy_closed {δ P α : V} (hδ : Cn 1 δ)
    (hP : P ∈ hierarchy δ) (hα : α ∈ δ) : forcingNameHierarchy P α ∈ hierarchy δ := by
  let := hδ.ordinal
  let := IsOrdinal.of_mem hα
  have hc := hδ.checkName_closed hP (ordinal_mem_hierarchy_iff.mpr hα)
  have hr := (mem_hierarchy_iff_rank_mem _ _).mp hc
  apply mem_hierarchy_of_mem_stage (hδ.successor_closed _ hr)
  rw [hierarchy_succ, mem_power_iff]
  exact forcingNameHierarchy_subset_check_rank P α

end ZFVP
