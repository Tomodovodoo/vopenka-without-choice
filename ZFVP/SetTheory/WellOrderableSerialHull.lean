import ZFVP.SetTheory.DependentChoice
import ZFVP.SetTheory.WellOrderingChoice

/-! The last step of Usuba, Proposition 3.6: a serial relation on a
well-orderable set admits a path, without internal Choice. Constructing the
small elementary hull and its generic interpretation is a separate obligation. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem pointedDependentChoice_of_wellOrderable {A R a : V}
    (hA : IsWellOrderable A) (ha : a ∈ A)
    (hR : ∀ x ∈ A, ∃ y ∈ A, ⟨x, y⟩ₖ ∈ R) :
    ∃ f ∈ A ^ (ω : V), f ‘ 0 = a ∧
      ∀ n ∈ (ω : V), ⟨f ‘ n, f ‘ (succ n)⟩ₖ ∈ R := by
  obtain ⟨α, hα, w, hw, hinj⟩ := (wellOrderable_iff_cardLE_ordinal A).mp hA
  let := hα
  let C : V → V := fun x ↦ {y ∈ A ; ⟨x, y⟩ₖ ∈ R}
  have hC : ℒₛₑₜ-function₁ C := by
    have h : ℒₛₑₜ-relation (fun B x : V ↦ ∀ y, y ∈ B ↔ y ∈ A ∧ ⟨x, y⟩ₖ ∈ R) := by
      definability
    apply Language.Definable.of_iff h
    intro v
    rw [mem_ext_iff]
    simp only [C, mem_sep_iff]
    rfl
  let F : V → V := fun x ↦ wellOrderSelection w (C x)
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  have hnext (x : V) (hx : x ∈ A) : F x ∈ A ∧ ⟨x, F x⟩ₖ ∈ R := by
    obtain ⟨y, hy, hxy⟩ := hR x hx
    exact mem_sep_iff.mp (wellOrderSelection_mem hw hinj
      (fun _ h ↦ (mem_sep_iff.mp h).1) ⟨y, mem_sep_iff.mpr ⟨hy, hxy⟩⟩)
  have hiter (n : V) (hn : n ∈ (ω : V)) : naturalIteration F hF a n ∈ A :=
    naturalIteration_invariant F hF a (fun x ↦ x ∈ A) (by definability) ha
      (fun x hx ↦ (hnext x hx).1) n hn
  let f := naturalIterationGraph F hF a
  have hf : f ∈ A ^ (ω : V) := definableGraph_mem_function_of_mapsTo _ _ _ _ hiter
  refine ⟨f, hf, ?_, ?_⟩
  · rw [naturalIterationGraph_value F hF a (by simp), naturalIteration_zero]
  · intro n hn
    rw [naturalIterationGraph_value F hF a hn,
      naturalIterationGraph_value F hF a (ω_succ_closed hn), naturalIteration_succ F hF a hn]
    exact (hnext _ (hiter n hn)).2

/-- A well-orderable serial subset suffices; the whole set need not be
well-orderable. This is the use of the countable hull in Usuba's proof. -/
theorem dependentChoice_of_wellOrderable_serial_subset {A R B : V}
    (hBA : B ⊆ A) (hB : IsWellOrderable B) (hne : IsNonempty B)
    (hR : ∀ x ∈ B, ∃ y ∈ B, ⟨x, y⟩ₖ ∈ R) :
    ∃ f ∈ A ^ (ω : V), ∀ n ∈ (ω : V), ⟨f ‘ n, f ‘ (succ n)⟩ₖ ∈ R := by
  obtain ⟨a, ha⟩ := hne.nonempty
  obtain ⟨f, hf, _, hstep⟩ := pointedDependentChoice_of_wellOrderable hB ha hR
  exact ⟨f, mem_function_of_mem_function_of_subset hf hBA, hstep⟩

theorem dependentChoice_of_wellOrderable_serial_hulls
    (hHull : ∀ A R : V, IsNonempty A →
      (∀ x ∈ A, ∃ y ∈ A, ⟨x, y⟩ₖ ∈ R) →
      ∃ B : V, B ⊆ A ∧ IsWellOrderable B ∧ IsNonempty B ∧
        ∀ x ∈ B, ∃ y ∈ B, ⟨x, y⟩ₖ ∈ R) : InternalDependentChoice V := by
  intro A R hA hR
  obtain ⟨B, hBA, hB, hne, hs⟩ := hHull A R hA hR
  exact dependentChoice_of_wellOrderable_serial_subset hBA hB hne hs

end ZFVP
