import ZFVP.SetTheory.InternalChoice
import ZFVP.SetTheory.NaturalIteration

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def InternalPointedDependentChoice (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : Prop :=
  ∀ A R a : V, a ∈ A → (∀ x ∈ A, ∃ y ∈ A, ⟨x, y⟩ₖ ∈ R) →
    ∃ f ∈ A ^ (ω : V), f ‘ 0 = a ∧ ∀ n ∈ (ω : V), ⟨f ‘ n, f ‘ (succ n)⟩ₖ ∈ R

def InternalDependentChoice (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : Prop :=
  ∀ A R : V, IsNonempty A → (∀ x ∈ A, ∃ y ∈ A, ⟨x, y⟩ₖ ∈ R) →
    ∃ f ∈ A ^ (ω : V), ∀ n ∈ (ω : V), ⟨f ‘ n, f ‘ (succ n)⟩ₖ ∈ R

theorem pointedDependentChoice_of_internalChoice (hAC : InternalChoice V) : InternalPointedDependentChoice V := by
  intro A R a ha hR
  let F : V → V := fun x ↦ {y ∈ A ; ⟨x, y⟩ₖ ∈ R}
  have hF : ℒₛₑₜ-function₁ F := by
    have h : ℒₛₑₜ-relation[V] (fun B x ↦ ∀ y, y ∈ B ↔ y ∈ A ∧ ⟨x, y⟩ₖ ∈ R) := by definability
    apply Language.Definable.of_iff h
    intro v
    change v 0 = F (v 1) ↔ _
    rw [mem_ext_iff]
    simp [F]
  have hn (x : V) (hx : x ∈ A) : IsNonempty (F x) := by
    obtain ⟨y, hy, hxy⟩ := hR x hx
    exact ⟨y, mem_sep_iff.mpr ⟨hy, hxy⟩⟩
  obtain ⟨g, _, _, hchoice⟩ := choice_for_definable_family hAC A F hF hn
  let G : V → V := fun x ↦ g ‘ x
  have hG : ℒₛₑₜ-function₁ G := by unfold G; definability
  have hnext (x : V) (hx : x ∈ A) : G x ∈ A ∧ ⟨x, G x⟩ₖ ∈ R := mem_sep_iff.mp (hchoice x hx)
  have hiter (n : V) (hn : n ∈ (ω : V)) : naturalIteration G hG a n ∈ A :=
    naturalIteration_invariant G hG a (fun x ↦ x ∈ A) (by definability) ha
      (fun x hx ↦ (hnext x hx).1) n hn
  let f := naturalIterationGraph G hG a
  have hf : f ∈ A ^ (ω : V) := definableGraph_mem_function_of_mapsTo _ _ _ _ hiter
  refine ⟨f, hf, ?_, ?_⟩
  · rw [naturalIterationGraph_value G hG a (by simp), naturalIteration_zero]
  · intro n hnω
    rw [naturalIterationGraph_value G hG a hnω,
      naturalIterationGraph_value G hG a (ω_succ_closed hnω), naturalIteration_succ G hG a hnω]
    exact (hnext _ (hiter n hnω)).2

theorem dependentChoice_of_pointed (hDC : InternalPointedDependentChoice V) : InternalDependentChoice V := by
  intro A R hA hR
  obtain ⟨a, ha⟩ := hA.nonempty
  obtain ⟨f, hf, _, hsteps⟩ := hDC A R a ha hR
  exact ⟨f, hf, hsteps⟩

theorem dependentChoice_of_internalChoice (hAC : InternalChoice V) : InternalDependentChoice V :=
  dependentChoice_of_pointed (pointedDependentChoice_of_internalChoice hAC)

theorem dependentChoice_of_models_ac [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] : InternalDependentChoice V :=
  dependentChoice_of_internalChoice internalChoice_of_models_ac

end ZFVP
