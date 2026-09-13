import ZFVP.Syntax.TermInduction
import ZFVP.SetTheory.InternalWellFounded

/-! Immediate subterms form an internally well-founded set relation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def subtermRelation (T : V) : V :=
  {p ∈ T ×ˢ T ; ∃ f args, kpair.π₂ p = functionTermCode f args ∧ kpair.π₁ p ∈ range args}

instance subtermRelation_definable : ℒₛₑₜ-function₁[V] subtermRelation := by
  have h : ℒₛₑₜ-relation (fun R T : V ↦ ∀ p,
      p ∈ R ↔ p ∈ T ×ˢ T ∧
        ∃ f args, kpair.π₂ p = functionTermCode f args ∧ kpair.π₁ p ∈ range args) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = subtermRelation (v 1) ↔ _
  rw [mem_ext_iff]
  simp [subtermRelation]

theorem kpair_mem_subtermRelation_iff (T s t : V) :
    ⟨s, t⟩ₖ ∈ subtermRelation T ↔ s ∈ T ∧ t ∈ T ∧
      ∃ f args, t = functionTermCode f args ∧ s ∈ range args := by
  simp [subtermRelation, and_assoc]

theorem rank_lt_functionTermCode {f args s : V} (hs : s ∈ range args) :
    rank s ∈ rank (functionTermCode f args) :=
  IsOrdinal.toIsTransitive.mem_trans (rank_lt_of_mem_range hs)
    (IsOrdinal.toIsTransitive.mem_trans (rank_kpair_right_lt f args)
      (rank_kpair_right_lt (2 : V) ⟨f, args⟩ₖ))

theorem subtermRelation_wellFounded (T : V) : IsInternallyWellFounded (subtermRelation T) T := by
  apply rank_decreasing_internallyWellFounded
  intro s _ t _ hst
  obtain ⟨_, _, f, args, rfl, hs⟩ := (kpair_mem_subtermRelation_iff T s t).mp hst
  exact rank_lt_functionTermCode hs

theorem immediate_subterm_mem {L n f args s : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V))
    (Γ : V) (ht : functionTermCode f args ∈ termSet L Γ n) (hs : s ∈ range args) :
    s ∈ termSet L Γ n :=
  range_subset_of_mem_function ((functionTermCode_mem_iff hL hn Γ f args).mp ht).2 s hs

theorem immediate_subterm_relation {L n f args s : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (Γ : V) (ht : functionTermCode f args ∈ termSet L Γ n)
    (hs : s ∈ range args) : ⟨s, functionTermCode f args⟩ₖ ∈ subtermRelation (termSet L Γ n) :=
  (kpair_mem_subtermRelation_iff _ _ _).mpr
    ⟨immediate_subterm_mem hL hn Γ ht hs, ht, f, args, rfl, hs⟩

end ZFVP
