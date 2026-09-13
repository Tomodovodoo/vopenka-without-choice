import ZFVP.SetTheory.NameClosure
import ZFVP.SetTheory.NaturalIteration
import ZFVP.SetTheory.FunctionUnion

/-! Iterating the subname operation through all internal naturals computes name closure. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def subnameStep (X : V) : V := X ∪ ⋃ˢ repl domain (by definability) X

instance subnameStep_definable : ℒₛₑₜ-function₁[V] subnameStep := by
  have h : ℒₛₑₜ-relation[V] (fun Y X ↦ ∀ u, u ∈ Y ↔ u ∈ X ∨ ∃ τ ∈ X, u ∈ domain τ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = subnameStep (v 1) ↔ _
  rw [mem_ext_iff]
  simp [subnameStep, mem_sUnion_iff, repl_spec]

theorem mem_subnameStep_iff (u X : V) : u ∈ subnameStep X ↔ u ∈ X ∨ ∃ τ ∈ X, u ∈ domain τ := by
  simp [subnameStep, mem_sUnion_iff, repl_spec]

theorem subset_subnameStep (X : V) : X ⊆ subnameStep X :=
  fun u hu ↦ (mem_subnameStep_iff u X).mpr (Or.inl hu)

theorem subnameStep_subset {X C : V} (hXC : X ⊆ C) (hC : IsSubnameClosed C) : subnameStep X ⊆ C := by
  intro u hu
  rcases (mem_subnameStep_iff u X).mp hu with hu | ⟨τ, hτ, hu⟩
  · exact hXC u hu
  · exact hC τ (hXC τ hτ) u hu

noncomputable def subnameIteration (τ n : V) : V :=
  naturalIteration subnameStep subnameStep_definable {τ} n

instance subnameIteration_definable (τ : V) : ℒₛₑₜ-function₁[V] (subnameIteration τ) := by
  unfold subnameIteration
  definability

noncomputable def subnameIterationGraph (τ : V) : V :=
  naturalIterationGraph subnameStep subnameStep_definable {τ}

instance subnameIterationGraph_isFunction (τ : V) : IsFunction (subnameIterationGraph τ) :=
  naturalIterationGraph_isFunction _ _ _

theorem domain_subnameIterationGraph (τ : V) : domain (subnameIterationGraph τ) = ω :=
  domain_naturalIterationGraph _ _ _

theorem subnameIterationGraph_value (τ : V) {n : V} (hn : n ∈ (ω : V)) :
    (subnameIterationGraph τ) ‘ n = subnameIteration τ n :=
  naturalIterationGraph_value _ _ _ hn

theorem subnameIteration_zero (τ : V) : subnameIteration τ 0 = {τ} := naturalIteration_zero _ _ _

theorem subnameIteration_succ (τ : V) {n : V} (hn : n ∈ (ω : V)) :
    subnameIteration τ (succ n) = subnameStep (subnameIteration τ n) := naturalIteration_succ _ _ _ hn

theorem subnameIteration_subset {τ C : V} (hτ : τ ∈ C) (hC : IsSubnameClosed C) :
    ∀ n ∈ (ω : V), subnameIteration τ n ⊆ C := by
  apply naturalNumber_induction (fun n ↦ subnameIteration τ n ⊆ C) (by definability)
  · rw [subnameIteration_zero]
    intro x hx
    exact (mem_singleton_iff.mp hx).symm ▸ hτ
  · intro n hn ih
    rw [subnameIteration_succ τ hn]
    exact subnameStep_subset ih hC

theorem mem_sUnion_range_subnameIterationGraph (τ u : V) :
    u ∈ ⋃ˢ range (subnameIterationGraph τ) ↔ ∃ n ∈ (ω : V), u ∈ subnameIteration τ n := by
  simp only [mem_sUnion_iff, mem_range_iff]
  constructor
  · rintro ⟨X, ⟨n, hnX⟩, hu⟩
    have hn : n ∈ (ω : V) := domain_subnameIterationGraph τ ▸ mem_domain_of_kpair_mem hnX
    have hX := value_eq_of_kpair_mem hnX
    rw [subnameIterationGraph_value τ hn] at hX
    exact ⟨n, hn, hX.symm ▸ hu⟩
  · rintro ⟨n, hn, hu⟩
    refine ⟨subnameIteration τ n, ⟨n, ?_⟩, hu⟩
    rw [← subnameIterationGraph_value τ hn]
    exact kpair_value_mem (by simpa only [domain_subnameIterationGraph] using hn)

theorem nameClosure_eq_iteration (τ : V) : nameClosure τ = ⋃ˢ range (subnameIterationGraph τ) := by
  apply SetTheory.subset_antisymm
  · apply nameClosure_minimal
    · intro σ hσ u hu
      obtain ⟨n, hn, hσn⟩ := (mem_sUnion_range_subnameIterationGraph τ σ).mp hσ
      apply (mem_sUnion_range_subnameIterationGraph τ u).mpr
      refine ⟨succ n, ω_succ_closed hn, ?_⟩
      rw [subnameIteration_succ τ hn]
      exact (mem_subnameStep_iff u _).mpr (Or.inr ⟨σ, hσn, hu⟩)
    · apply (mem_sUnion_range_subnameIterationGraph τ τ).mpr
      exact ⟨0, by simp, by rw [subnameIteration_zero]; simp⟩
  · intro u hu
    obtain ⟨n, hn, hun⟩ := (mem_sUnion_range_subnameIterationGraph τ u).mp hu
    exact subnameIteration_subset (mem_nameClosure_self τ) (nameClosure_closed τ) n hn u hun

theorem subnameIterationGraph_eq_of_recursion {τ f : V} [IsFunction f]
    (hf : domain f = ω) (hz : f ‘ (0 : V) = {τ})
    (hs : ∀ n ∈ (ω : V), f ‘ (succ n) = subnameStep (f ‘ n)) : f = subnameIterationGraph τ := by
  have hv : ∀ n ∈ (ω : V), f ‘ n = subnameIteration τ n := by
    apply naturalNumber_induction (fun n ↦ f ‘ n = subnameIteration τ n) (by definability)
    · rw [subnameIteration_zero]
      exact hz
    · intro n hn ih
      rw [hs n hn, subnameIteration_succ τ hn, ih]
  apply functions_eq_of_domain_values
  · exact hf.trans (domain_subnameIterationGraph τ).symm
  · intro n hn
    rw [hf] at hn
    exact (hv n hn).trans (subnameIterationGraph_value τ hn).symm

end ZFVP
