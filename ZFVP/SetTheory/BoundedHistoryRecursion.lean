import ZFVP.SetTheory.DependentChoice
import ZFVP.SetTheory.UniformRecursion
import ZFVP.SetTheory.FunctionUnion
import ZFVP.SetTheory.FiniteSequences

/-! Actual bounded choice over histories and transfinite recursion with a
fallback value. Admissibility is required only at the histories where it is
used; no totality assumption on the successor relation is imposed. -/

set_option autoImplicit false

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem exists_boundedHistoryChoice (hAC : InternalChoice V) {κ B b₀ : V} (hb₀ : b₀ ∈ B)
    (Next : V → V → Prop) (hNext : ℒₛₑₜ-relation[V] Next) :
    ∃ q ∈ B ^ power (κ ×ˢ B), ∀ s ∈ power (κ ×ˢ B),
      ((∃ b ∈ B, Next s b) → Next s (q ‘ s)) ∧
      ((¬∃ b ∈ B, Next s b) → q ‘ s = b₀) := by
  classical
  let : ℒₛₑₜ-relation[V] Next := hNext
  let G : V → V := fun s ↦ {b ∈ B ; Next s b ∨ (¬∃ c ∈ B, Next s c) ∧ b = b₀}
  have hG : ℒₛₑₜ-function₁ G := by
    have hh : ℒₛₑₜ-relation[V] (fun X s ↦ ∀ b,
        b ∈ X ↔ b ∈ B ∧ (Next s b ∨ (¬∃ c ∈ B, Next s c) ∧ b = b₀)) := by definability
    apply Language.Definable.of_iff hh
    intro v
    rw [mem_ext_iff]
    simp only [G, mem_sep_iff]
    rfl
  have hne : ∀ s ∈ power (κ ×ˢ B), IsNonempty (G s) := by
    intro s _
    by_cases he : ∃ b ∈ B, Next s b
    · obtain ⟨b, hb, hsb⟩ := he
      exact ⟨b, mem_sep_iff.mpr ⟨hb, Or.inl hsb⟩⟩
    · exact ⟨b₀, mem_sep_iff.mpr ⟨hb₀, Or.inr ⟨he, rfl⟩⟩⟩
  obtain ⟨q, hq, hdq, hval⟩ := choice_for_definable_family hAC (power (κ ×ˢ B)) G hG hne
  let : IsFunction q := hq
  have hqb : q ∈ B ^ power (κ ×ˢ B) := by
    have hr : range q ⊆ B := by
      intro b hb
      obtain ⟨s, hsb⟩ := mem_range_iff.mp hb
      have hs : s ∈ power (κ ×ˢ B) := hdq ▸ mem_domain_of_kpair_mem hsb
      have hh := (mem_sep_iff.mp (hval s hs)).1
      rwa [value_eq_of_kpair_mem hsb] at hh
    simpa only [hdq] using mem_function_of_mem_function_of_subset (IsFunction.mem_function q) hr
  refine ⟨q, hqb, ?_⟩
  intro s hs
  have hv := (mem_sep_iff.mp (hval s hs)).2
  constructor
  · intro he
    exact hv.elim id (fun hh ↦ False.elim (hh.1 he))
  · intro he
    exact hv.elim (fun hh ↦ False.elim (he ⟨q ‘ s, function_value_mem hqb hs, hh⟩)) And.right

noncomputable def boundedTransfiniteHistory (F : V → V) (hF : ℒₛₑₜ-function₁ F) (κ : V) : V :=
  definableGraph κ (Replacement.transfiniteRec F hF) (Replacement.transfiniteRec_definable hF)

instance boundedTransfiniteHistory_isFunction (F : V → V) (hF : ℒₛₑₜ-function₁ F) (κ : V) :
    IsFunction (boundedTransfiniteHistory F hF κ) := by
  unfold boundedTransfiniteHistory
  infer_instance

theorem boundedTransfiniteHistory_restrict (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    {κ α : V} (hακ : α ⊆ κ) :
    (boundedTransfiniteHistory F hF κ) ↾ α = boundedTransfiniteHistory F hF α := by
  apply functions_eq_of_domain_values
  · simp only [boundedTransfiniteHistory, domain_restrict_eq, domain_definableGraph,
      inter_eq_right_of_subset hακ]
  · intro x hx
    have hxα : x ∈ α := by
      simpa only [boundedTransfiniteHistory, domain_restrict_eq, domain_definableGraph,
        inter_eq_right_of_subset hακ] using hx
    rw [value_restrict (by simpa only [boundedTransfiniteHistory, domain_definableGraph] using hακ x hxα) hxα]
    exact (value_definableGraph _ _ _ (hακ x hxα)).trans (value_definableGraph _ _ _ hxα).symm

theorem boundedTransfiniteHistory_value (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    {κ α : V} [IsOrdinal κ] (hα : α ∈ κ) :
    (boundedTransfiniteHistory F hF κ) ‘ α = F ((boundedTransfiniteHistory F hF κ) ↾ α) := by
  let : IsOrdinal α := IsOrdinal.of_mem hα
  rw [boundedTransfiniteHistory_restrict F hF (IsOrdinal.toIsTransitive.transitive _ hα)]
  rw [show (boundedTransfiniteHistory F hF κ) ‘ α = Replacement.transfiniteRec F hF α from
    value_definableGraph _ _ _ hα]
  exact Replacement.transfiniteRec_spec F hF (IsOrdinal.toOrdinal α)

theorem boundedTransfiniteHistory_mem (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    {κ B : V} [IsOrdinal κ] (hFB : ∀ s, F s ∈ B) : boundedTransfiniteHistory F hF κ ∈ B ^ κ := by
  apply definableGraph_mem_function_of_mapsTo
  intro α hα
  let : IsOrdinal α := IsOrdinal.of_mem hα
  have he : Replacement.transfiniteRec F hF α = F (boundedTransfiniteHistory F hF α) :=
    Replacement.transfiniteRec_spec F hF (IsOrdinal.toOrdinal α)
  rw [he]
  exact hFB _

/-- Produce a bounded actual history. Every prefix has its expected domain,
and whenever a row is admissible, the chosen row satisfies `Next`. -/
theorem exists_boundedHistoryRecursion (hAC : InternalChoice V) {κ B b₀ : V}
    (hκ : IsOrdinal κ) (hb₀ : b₀ ∈ B) (Next : V → V → Prop) (hNext : ℒₛₑₜ-relation[V] Next) :
    ∃ C ∈ B ^ κ, ∀ α ∈ κ, C ↾ α ∈ B ^ α ∧ domain (C ↾ α) = α ∧
      ((∃ b ∈ B, Next (C ↾ α) b) → Next (C ↾ α) (C ‘ α)) ∧
      ((¬∃ b ∈ B, Next (C ↾ α) b) → C ‘ α = b₀) := by
  classical
  let : IsOrdinal κ := hκ
  obtain ⟨q, hq, hchoose⟩ := exists_boundedHistoryChoice (κ := κ) hAC hb₀ Next hNext
  let F : V → V := fun s ↦ if s ∈ power (κ ×ˢ B) then q ‘ s else b₀
  have hF : ℒₛₑₜ-function₁ F := by
    have hh : ℒₛₑₜ-relation[V] (fun y s ↦
        (s ∈ power (κ ×ˢ B) ∧ y = q ‘ s) ∨ (s ∉ power (κ ×ˢ B) ∧ y = b₀)) := by definability
    apply Language.Definable.of_iff hh
    intro v
    change v 0 = F (v 1) ↔ _
    dsimp only [F]
    split <;> simp_all
  have hFB : ∀ s, F s ∈ B := by
    intro s
    dsimp only [F]
    split
    · exact function_value_mem hq ‹s ∈ power (κ ×ˢ B)›
    · exact hb₀
  let C := boundedTransfiniteHistory F hF κ
  have hC : C ∈ B ^ κ := boundedTransfiniteHistory_mem F hF hFB
  let : IsFunction C := IsFunction.of_mem hC
  refine ⟨C, hC, ?_⟩
  intro α hα
  have hακ : α ⊆ κ := IsOrdinal.toIsTransitive.transitive _ hα
  have hprefix : C ↾ α ∈ B ^ α := function_restrict_mem hC hακ
  have hbounded : C ↾ α ∈ power (κ ×ˢ B) := mem_power_iff.mpr (by
    intro p hp
    obtain ⟨x, hx, b, hb, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hprefix _ hp)
    exact kpair_mem_iff.mpr ⟨hακ x hx, hb⟩)
  have he : C ‘ α = q ‘ (C ↾ α) := by
    rw [boundedTransfiniteHistory_value F hF hα]
    change (if C ↾ α ∈ power (κ ×ˢ B) then q ‘ (C ↾ α) else b₀) = q ‘ (C ↾ α)
    simp only [hbounded, ite_true]
  refine ⟨hprefix, domain_eq_of_mem_function hprefix, ?_, ?_⟩
  · intro hex
    rw [he]
    exact (hchoose _ hbounded).1 hex
  · intro hnone
    rw [he]
    exact (hchoose _ hbounded).2 hnone

end ZFVP
