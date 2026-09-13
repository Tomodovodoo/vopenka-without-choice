import ZFVP.SetTheory.NaturalParity
import ZFVP.SetTheory.RealCoverApproximation

/-! Interleaving two internal sequences without external enumeration. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def sequenceInterleaveEntry (f g n : V) : V :=
  ⋃ˢ {y ∈ range f ∪ range g ; ∃ k ∈ (ω : V),
    (n = ordinalAdd k k ∧ y = f ‘ k) ∨ (n = succ (ordinalAdd k k) ∧ y = g ‘ k)}

instance sequenceInterleaveEntry_definable : ℒₛₑₜ-function₃[V] sequenceInterleaveEntry := by
  have h : ℒₛₑₜ-relation₄ (fun w f g n : V ↦ ∀ z, z ∈ w ↔
      ∃ y, y ∈ range f ∪ range g ∧
        (∃ k ∈ (ω : V), (n = ordinalAdd k k ∧ y = f ‘ k) ∨
          (n = succ (ordinalAdd k k) ∧ y = g ‘ k)) ∧ z ∈ y) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [sequenceInterleaveEntry, mem_sUnion_iff, mem_sep_iff, and_assoc]
  rfl

theorem sequenceInterleaveEntry_even {f g B C k : V}
    (hf : f ∈ B ^ (ω : V)) (_hg : g ∈ C ^ (ω : V)) (hk : k ∈ (ω : V)) :
    sequenceInterleaveEntry f g (ordinalAdd k k) = f ‘ k := by
  have : IsFunction f := IsFunction.of_mem hf
  have hs : {y ∈ range f ∪ range g ; ∃ i ∈ (ω : V),
      (ordinalAdd k k = ordinalAdd i i ∧ y = f ‘ i) ∨
      (ordinalAdd k k = succ (ordinalAdd i i) ∧ y = g ‘ i)} = ({f ‘ k} : V) := by
    apply mem_ext
    intro y
    simp only [mem_sep_iff, mem_singleton_iff]
    constructor
    · rintro ⟨_, i, hi, ⟨he, hy⟩ | ⟨he, _⟩⟩
      · rw [← natural_double_injective hk hi he] at hy
        exact hy
      · exact (natural_double_ne_succ_double hk hi he).elim
    · rintro rfl
      refine ⟨mem_union_iff.mpr (Or.inl ?_), k, hk, Or.inl ⟨rfl, rfl⟩⟩
      exact value_mem_range hf hk
  simp only [sequenceInterleaveEntry, hs, sUnion_singleton_eq]

theorem sequenceInterleaveEntry_odd {f g B C k : V}
    (_hf : f ∈ B ^ (ω : V)) (hg : g ∈ C ^ (ω : V)) (hk : k ∈ (ω : V)) :
    sequenceInterleaveEntry f g (succ (ordinalAdd k k)) = g ‘ k := by
  have : IsFunction g := IsFunction.of_mem hg
  have hs : {y ∈ range f ∪ range g ; ∃ i ∈ (ω : V),
      (succ (ordinalAdd k k) = ordinalAdd i i ∧ y = f ‘ i) ∨
      (succ (ordinalAdd k k) = succ (ordinalAdd i i) ∧ y = g ‘ i)} = ({g ‘ k} : V) := by
    apply mem_ext
    intro y
    simp only [mem_sep_iff, mem_singleton_iff]
    constructor
    · rintro ⟨_, i, hi, ⟨he, _⟩ | ⟨he, hy⟩⟩
      · exact (natural_double_ne_succ_double hi hk he.symm).elim
      · let := IsOrdinal.of_mem (ordinalAdd_natural hk hk)
        let := IsOrdinal.of_mem (ordinalAdd_natural hi hi)
        have he' := succ_injective_ordinal he
        rw [← natural_double_injective hk hi he'] at hy
        exact hy
    · rintro rfl
      refine ⟨mem_union_iff.mpr (Or.inr ?_), k, hk, Or.inr ⟨rfl, rfl⟩⟩
      exact value_mem_range hg hk
  simp only [sequenceInterleaveEntry, hs, sUnion_singleton_eq]

noncomputable def sequenceInterleave (f g : V) : V :=
  definableGraph (ω : V) (sequenceInterleaveEntry f g) (by definability)

theorem sequenceInterleave_even {f g B C k : V}
    (hf : f ∈ B ^ (ω : V)) (hg : g ∈ C ^ (ω : V)) (hk : k ∈ (ω : V)) :
    (sequenceInterleave f g) ‘ (ordinalAdd k k) = f ‘ k := by
  rw [sequenceInterleave, value_definableGraph _ _ _ (ordinalAdd_natural hk hk)]
  exact sequenceInterleaveEntry_even hf hg hk

theorem sequenceInterleave_odd {f g B C k : V}
    (hf : f ∈ B ^ (ω : V)) (hg : g ∈ C ^ (ω : V)) (hk : k ∈ (ω : V)) :
    (sequenceInterleave f g) ‘ (succ (ordinalAdd k k)) = g ‘ k := by
  rw [sequenceInterleave, value_definableGraph _ _ _ (ω_succ_closed (ordinalAdd_natural hk hk))]
  exact sequenceInterleaveEntry_odd hf hg hk

theorem sequenceInterleave_mem {f g B : V}
    (hf : f ∈ B ^ (ω : V)) (hg : g ∈ B ^ (ω : V)) :
    sequenceInterleave f g ∈ B ^ (ω : V) := by
  apply definableGraph_mem_function_of_mapsTo
  intro n hn
  obtain ⟨k, hk, rfl | rfl⟩ := natural_even_or_odd n hn
  · rw [sequenceInterleaveEntry_even hf hg hk]
    exact function_value_mem hf hk
  · rw [sequenceInterleaveEntry_odd hf hg hk]
    exact function_value_mem hg hk

end ZFVP
