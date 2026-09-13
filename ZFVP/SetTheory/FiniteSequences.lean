import ZFVP.SetTheory.DefinableGraph
import Foundation.FirstOrder.SetTheory.Ordinal

/-! Internally finite sequences, including nonstandard finite lengths in
nonstandard ZF models. Sequences are internal function graphs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def finiteSequences (A : V) : V :=
  {s ∈ ℘ ((ω : V) ×ˢ A) ; ∃ n ∈ (ω : V), s ∈ A ^ n}

theorem mem_finiteSequences_iff (A s : V) :
    s ∈ finiteSequences A ↔ ∃ n ∈ (ω : V), s ∈ A ^ n := by
  constructor
  · intro hs
    exact (show s ∈ ℘ ((ω : V) ×ˢ A) ∧ ∃ n ∈ (ω : V), s ∈ A ^ n from by
      simpa [finiteSequences] using hs).2
  · intro h
    obtain ⟨n, hn, hs⟩ := h
    have hb : s ⊆ (ω : V) ×ˢ A :=
      subset_trans (subset_prod_of_mem_function hs)
        (prod_subset_prod_of_subset (IsTransitive.transitive n hn) (subset_refl A))
    simpa [finiteSequences, mem_power_iff, hb] using (show ∃ n ∈ (ω : V), s ∈ A ^ n from ⟨n, hn, hs⟩)

def finiteSequencesFormula : SetTheorySemisentence 2 :=
  f“S A. ∀ s, s ∈ S ↔ ∃ n, n ∈ !isω ∧ s ∈ !function.dfn A n”

instance finiteSequencesFormula_defined :
    ℒₛₑₜ-function₁[V] finiteSequences via finiteSequencesFormula :=
  ⟨fun v ↦ by simp [finiteSequencesFormula, mem_ext_iff (y := finiteSequences _),
    mem_finiteSequences_iff]⟩

instance finiteSequences_definable : ℒₛₑₜ-function₁[V] finiteSequences :=
  finiteSequencesFormula_defined.to_definable

theorem empty_mem_finiteSequences (A : V) : (∅ : V) ∈ finiteSequences A :=
  (mem_finiteSequences_iff A ∅).mpr ⟨∅, empty_mem_ω, by simp [mem_function_iff]⟩

theorem finiteSequence_length_unique {A s n m : V}
    (hn : s ∈ A ^ n) (hm : s ∈ A ^ m) : n = m :=
  (domain_eq_of_mem_function hn).symm.trans (domain_eq_of_mem_function hm)

theorem mem_finiteSequences_iff_domain (A s : V) :
    s ∈ finiteSequences A ↔ domain s ∈ (ω : V) ∧ s ∈ A ^ domain s := by
  rw [mem_finiteSequences_iff]
  constructor
  · rintro ⟨n, hn, hs⟩
    simpa only [domain_eq_of_mem_function hs] using And.intro hn hs
  · rintro ⟨hn, hs⟩
    exact ⟨domain s, hn, hs⟩

theorem function_append_mem {A s n x : V} (hs : s ∈ A ^ n) (hx : x ∈ A) :
    insert ⟨n, x⟩ₖ s ∈ A ^ succ n := by
  have : IsFunction s := IsFunction.of_mem hs
  have hd := domain_eq_of_mem_function hs
  have : IsFunction (insert ⟨n, x⟩ₖ s) := IsFunction.insert s n x (by simp [hd])
  have hd' : domain (insert ⟨n, x⟩ₖ s) = succ n := by simp [hd, succ]
  have hr : range (insert ⟨n, x⟩ₖ s) ⊆ A := by
    intro y hy
    rcases show y = x ∨ y ∈ range s from by simpa using hy with rfl | hy
    · exact hx
    · exact range_subset_of_mem_function hs y hy
  have hh := IsFunction.mem_function (insert ⟨n, x⟩ₖ s)
  rw [hd'] at hh
  exact mem_function_of_mem_function_of_subset hh hr

theorem finiteSequence_append {A s x : V} (hs : s ∈ finiteSequences A) (hx : x ∈ A) :
    insert ⟨domain s, x⟩ₖ s ∈ finiteSequences A := by
  obtain ⟨hn, hf⟩ := (mem_finiteSequences_iff_domain A s).mp hs
  exact (mem_finiteSequences_iff A _).mpr
    ⟨succ (domain s), ω_succ_closed hn, function_append_mem hf hx⟩

theorem function_append_restrict {A s n x : V} (hs : s ∈ A ^ n) :
    (insert ⟨n, x⟩ₖ s) ↾ n = s := by
  have : IsFunction s := IsFunction.of_mem hs
  rw [restrict_insert_kpair_eq_restrict_of_not_mem (mem_irrefl n)]
  exact IsFunction.restrict_eq_self s n (by rw [domain_eq_of_mem_function hs])

theorem function_restrict_mem {A s n m : V} (hs : s ∈ A ^ n) (hm : m ⊆ n) :
    s ↾ m ∈ A ^ m := by
  have : IsFunction s := IsFunction.of_mem hs
  have hd : domain (s ↾ m) = m := by
    rw [domain_restrict_eq, domain_eq_of_mem_function hs, inter_eq_right_of_subset hm]
  have hr : range (s ↾ m) ⊆ A := by
    intro y hy
    obtain ⟨x, hxy⟩ := mem_range_iff.mp hy
    exact range_subset_of_mem_function hs y
      (mem_range_of_kpair_mem (kpair_mem_restrict_iff.mp hxy).1)
  have hh := IsFunction.mem_function (s ↾ m)
  rw [hd] at hh
  exact mem_function_of_mem_function_of_subset hh hr

theorem function_succ_decompose {A s n : V} (hs : s ∈ A ^ succ n) :
    ∃ t x, t ∈ A ^ n ∧ x ∈ A ∧ s = insert ⟨n, x⟩ₖ t := by
  have : IsFunction s := IsFunction.of_mem hs
  obtain ⟨x, hx, hnx⟩ := exists_of_mem_function hs n (by simp)
  refine ⟨s ↾ n, x, function_restrict_mem hs (mem_subset_refl n), hx, ?_⟩
  apply mem_ext
  intro p
  constructor
  · intro hp
    obtain ⟨i, hi, y, _, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hs p hp)
    rcases mem_succ_iff.mp hi with rfl | hi
    · have hy : y = x := IsFunction.unique hp hnx
      simp [hy]
    · exact mem_insert.mpr (Or.inr (kpair_mem_restrict_iff.mpr ⟨hp, hi⟩))
  · intro hp
    rcases mem_insert.mp hp with rfl | hp
    · exact hnx
    · exact restrict_subset s n p hp

/-- Induction on internal finite sequences requires definability, just as
induction on internal natural numbers does in a possibly nonstandard model. -/
theorem finiteSequence_induction (A : V) (P : V → Prop) (hP : ℒₛₑₜ-predicate P)
    (hzero : P ∅)
    (hstep : ∀ n ∈ (ω : V), ∀ s ∈ A ^ n, ∀ x ∈ A, P s → P (insert ⟨n, x⟩ₖ s)) :
    ∀ s ∈ finiteSequences A, P s := by
  have hn : ∀ n ∈ (ω : V), ∀ s ∈ A ^ n, P s := by
    apply naturalNumber_induction (fun n ↦ ∀ s ∈ A ^ n, P s) (by definability)
    · intro s hs
      have he : s = ∅ := subset_empty_iff_eq_empty.mp (by
        simpa [zero_def] using subset_prod_of_mem_function hs)
      exact he ▸ hzero
    · intro n hn ih s hs
      obtain ⟨t, x, ht, hx, rfl⟩ := function_succ_decompose hs
      exact hstep n hn t ht x hx (ih t ht)
  intro s hs
  obtain ⟨n, hnω, hs⟩ := (mem_finiteSequences_iff A s).mp hs
  exact hn n hnω s hs

end ZFVP
