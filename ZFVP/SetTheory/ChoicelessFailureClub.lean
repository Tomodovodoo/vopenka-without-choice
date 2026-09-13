import ZFVP.SetTheory.ChoicelessExtendible
import ZFVP.SetTheory.WitnessClosure

/-! The closed unbounded class of failure-witness ranks in Mohammd's
Theorem 3.1. The class is unbounded under the stated failure of
alpha-relative choiceless extendibility. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def ChoicelessFailureWitness (n : ℕ) (α γ μ : V) : Prop :=
  Cn n μ ∧ γ ∈ μ ∧ ¬∃ ν e κ,
    Cn n ν ∧ IsCodedMembershipEmbedding (hierarchy μ) (hierarchy ν) e ∧
      IsCriticalPoint (hierarchy μ) e κ ∧ α ∈ κ ∧ μ ∈ e ‘ γ

instance choicelessFailureWitness_definable (n : ℕ) :
    ℒₛₑₜ-relation₃[V] (ChoicelessFailureWitness n) := by
  unfold ChoicelessFailureWitness
  definability

theorem choicelessFailureWitness_exists {n : ℕ} {α γ : V} [IsOrdinal γ]
    (hαγ : α ∈ γ) (h : ¬IsAlphaChoicelessExtendible n α γ) :
    ∃ μ, ChoicelessFailureWitness n α γ μ := by
  classical
  by_contra hn
  apply h
  refine ⟨inferInstance, hαγ, ?_⟩
  intro μ hμ hγμ
  by_contra he
  exact hn ⟨μ, hμ, hγμ, he⟩

def IsChoicelessFailureLimit (n : ℕ) (α β : V) : Prop :=
  IsOrdinal β ∧ α ∈ β ∧ (∀ ξ ∈ β, succ ξ ∈ β) ∧
    ∀ γ ∈ β, α ∈ γ → ∃ μ ∈ β, ChoicelessFailureWitness n α γ μ

instance isChoicelessFailureLimit_definable (n : ℕ) :
    ℒₛₑₜ-relation[V] (IsChoicelessFailureLimit n) := by
  unfold IsChoicelessFailureLimit
  definability

theorem choicelessFailureLimit_unbounded (n : ℕ) (α ξ : V)
    [IsOrdinal α] [IsOrdinal ξ]
    (h : ∀ γ, ¬IsAlphaChoicelessExtendible n α γ) :
    ∃ β, ξ ∈ β ∧ IsChoicelessFailureLimit n α β := by
  let := ordinal_union_ordinal α ξ
  obtain ⟨β, hβ, hb, hlim, hw⟩ := witnessClosed_above
    (ChoicelessFailureWitness n α) (by definability) (α ∪ ξ)
  let := hβ
  have haβ : α ∈ β := ordinal_mem_of_subset_mem
    (fun x hx ↦ mem_union_iff.mpr (Or.inl hx)) hb
  have hξβ : ξ ∈ β := ordinal_mem_of_subset_mem
    (fun x hx ↦ mem_union_iff.mpr (Or.inr hx)) hb
  refine ⟨β, hξβ, hβ, haβ, hlim, ?_⟩
  intro γ hγ hαγ
  let : IsOrdinal γ := IsOrdinal.of_mem hγ
  obtain ⟨μ, hμ, hwμ⟩ := hw γ (ordinal_subset_hierarchy β γ hγ)
    (choicelessFailureWitness_exists hαγ (h γ))
  let := hwμ.1.ordinal
  have hμβ : μ ∈ β := by
    simpa only [rank_of_ordinal] using (mem_hierarchy_iff_rank_mem μ β).mp hμ
  exact ⟨μ, hμβ, hwμ⟩

theorem choicelessFailureLimit_closed {n : ℕ} {α β : V} [IsOrdinal β]
    (hβ : IsNonempty β)
    (hc : ∀ ξ ∈ β, ∃ δ ∈ β, ξ ∈ δ ∧ IsChoicelessFailureLimit n α δ) :
    IsChoicelessFailureLimit n α β := by
  obtain ⟨ξ, hξ⟩ := hβ
  obtain ⟨δ, hδ, _, hD⟩ := hc ξ hξ
  refine ⟨inferInstance, IsOrdinal.toIsTransitive.mem_trans hD.2.1 hδ, ?_, ?_⟩
  · intro η hη
    obtain ⟨δ, hδ, hηδ, hD⟩ := hc η hη
    exact IsOrdinal.toIsTransitive.mem_trans (hD.2.2.1 η hηδ) hδ
  · intro γ hγ hαγ
    obtain ⟨δ, hδ, hγδ, hD⟩ := hc γ hγ
    obtain ⟨μ, hμ, hw⟩ := hD.2.2.2 γ hγδ hαγ
    exact ⟨μ, IsOrdinal.toIsTransitive.mem_trans hμ hδ, hw⟩

theorem IsChoicelessFailureLimit.cn_cofinal {n : ℕ} {α β : V}
    (h : IsChoicelessFailureLimit n α β) :
    ∀ ξ ∈ β, ∃ μ ∈ β, ξ ∈ μ ∧ Cn n μ := by
  let := h.1
  let : IsOrdinal α := IsOrdinal.of_mem h.2.1
  intro ξ hξ
  let : IsOrdinal ξ := IsOrdinal.of_mem hξ
  have hmax : α ∪ ξ ∈ β := by
    rcases IsOrdinal.mem_trichotomy α ξ with ha | he | hx
    · have heq : α ∪ ξ = ξ := by
        apply mem_ext_iff.mpr
        intro x
        simp only [mem_union_iff]
        exact ⟨fun hh ↦ hh.elim (fun hx ↦ IsOrdinal.toIsTransitive.mem_trans hx ha) id, Or.inr⟩
      rwa [heq]
    · subst ξ
      simpa using hξ
    · have heq : α ∪ ξ = α := by
        apply mem_ext_iff.mpr
        intro x
        simp only [mem_union_iff]
        exact ⟨fun hh ↦ hh.elim id (fun hξ ↦ IsOrdinal.toIsTransitive.mem_trans hξ hx), Or.inl⟩
      rw [heq]
      exact h.2.1
  let := ordinal_union_ordinal α ξ
  have hαγ : α ∈ succ (α ∪ ξ) := mem_succ_iff.mpr
    (IsOrdinal.subset_iff.mp (fun x hx ↦ mem_union_iff.mpr (Or.inl hx)))
  have hξγ : ξ ∈ succ (α ∪ ξ) := mem_succ_iff.mpr
    (IsOrdinal.subset_iff.mp (fun x hx ↦ mem_union_iff.mpr (Or.inr hx)))
  obtain ⟨μ, hμβ, hw⟩ := h.2.2.2 _ (h.2.2.1 _ hmax) hαγ
  let := hw.1.ordinal
  exact ⟨μ, hμβ, IsOrdinal.toIsTransitive.mem_trans hξγ hw.2.1, hw.1⟩

theorem IsChoicelessFailureLimit.cn {n : ℕ} {α β : V}
    (h : IsChoicelessFailureLimit n α β) : Cn n β := by
  let := h.1
  exact cn_closed n ⟨α, h.2.1⟩ h.cn_cofinal

end ZFVP
