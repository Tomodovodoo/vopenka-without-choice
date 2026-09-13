import ZFVP.SetTheory.CountableSets
import ZFVP.SetTheory.InverseFunction

/-! Actual injections into the first uncountable ordinal, extending a fixed
countable set of labels and including a prescribed new label. -/

set_option autoImplicit false

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A countable family can be assigned distinct labels avoiding any given
countable set of forbidden labels. -/
theorem exists_hartogsOmega_fresh_injection (hAC : InternalChoice V) {A B : V}
    (hA : IsInternallyCountable A) (hB : IsInternallyCountable B) :
    ∃ f ∈ (hartogsNumber (ω : V) \ B) ^ A, Injective f := by
  have hinf : IsInternallyInfinite (hartogsNumber (ω : V) \ B) := by
    intro hfin
    have hcover : hartogsNumber (ω : V) ⊆ B ∪ (hartogsNumber (ω : V) \ B) := by
      intro x hx
      by_cases hb : x ∈ B
      · exact mem_union_iff.mpr (Or.inl hb)
      · exact mem_union_iff.mpr (Or.inr (mem_sdiff_iff.mpr ⟨hx, hb⟩))
    exact hartogs_omega_not_countable (internallyCountable_subset
      (internallyCountable_union hB (internallyCountable_of_finite hfin)) hcover)
  exact hA.trans (omega_cardLE_of_infinite_dependentChoice (dependentChoice_of_internalChoice hAC) hinf)

/-- Extend an actual countable partial labeling without changing any of its
values. The resulting total labeling still has countable range. -/
theorem exists_hartogsOmega_injection_extending (hAC : InternalChoice V) {A S g : V}
    (hA : IsInternallyCountable A) (hSA : S ⊆ A)
    (hg : g ∈ hartogsNumber (ω : V) ^ S) (hgi : Injective g)
    (hsmall : IsInternallyCountable (range g)) :
    ∃ h ∈ hartogsNumber (ω : V) ^ A, Injective h ∧
      (∀ x ∈ S, h ‘ x = g ‘ x) ∧ IsInternallyCountable (range h) := by
  classical
  obtain ⟨q, hq, hqi⟩ := exists_hartogsOmega_fresh_injection hAC hA hsmall
  let F : V → V := fun x ↦ if x ∈ S then g ‘ x else q ‘ x
  have hF : ℒₛₑₜ-function₁ F := by
    have hh : ℒₛₑₜ-relation[V] (fun y x ↦
        (x ∈ S ∧ y = g ‘ x) ∨ (x ∉ S ∧ y = q ‘ x)) := by definability
    apply Language.Definable.of_iff hh
    intro v
    change v 0 = F (v 1) ↔ _
    dsimp only [F]
    split <;> simp_all
  let h := definableGraph A F hF
  have hh : h ∈ hartogsNumber (ω : V) ^ A := definableGraph_mem_function_of_mapsTo _ _ _ _ (by
    intro x hx
    dsimp only [F]
    split
    · exact function_value_mem hg ‹x ∈ S›
    · exact (mem_sdiff_iff.mp (function_value_mem hq hx)).1)
  have hhi : Injective h := by
    intro x y z hx hy
    obtain ⟨hxA, rfl⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hx
    obtain ⟨hyA, he⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hy
    dsimp only [F] at he
    split_ifs at he with hxS hyS hyS
    · exact injective_value_eq hg hgi hxS hyS he
    · exact False.elim ((mem_sdiff_iff.mp (function_value_mem hq hyA)).2
        (he ▸ value_mem_range hg hxS))
    · exact False.elim ((mem_sdiff_iff.mp (function_value_mem hq hxA)).2
        (he.symm ▸ value_mem_range hg hyS))
    · exact injective_value_eq hq hqi hxA hyA he
  refine ⟨h, hh, hhi, ?_, ?_⟩
  · intro x hx
    rw [value_definableGraph _ _ _ (hSA x hx)]
    simp only [F, hx, ite_true]
  · let : IsFunction h := IsFunction.of_mem hh
    exact internallyCountable_range (internallyCountable_function (by
      simpa only [domain_eq_of_mem_function hh] using hA))

/-- Relabel a countable extension inside `hartogsNumber ω`, preserving every
old label and including `α`. A fresh domain point is needed only when `α` is
not already an old label. -/
theorem exists_hartogsOmega_relabeling (hAC : InternalChoice V) {D A f α : V}
    (hD : IsInternallyCountable D) (hDκ : D ⊆ hartogsNumber (ω : V))
    (hA : IsInternallyCountable A) (hf : f ∈ A ^ D) (hfi : Injective f)
    (hα : α ∈ hartogsNumber (ω : V))
    (hnew : α ∉ D → ∃ y ∈ A, y ∉ range f) :
    ∃ h ∈ hartogsNumber (ω : V) ^ A, Injective h ∧
      (∀ x ∈ D, h ‘ (f ‘ x) = x) ∧ α ∈ range h ∧ IsInternallyCountable (range h) := by
  classical
  let : IsFunction f := IsFunction.of_mem hf
  have hgf := converseGraph_mem_function hf hfi
  let : IsFunction (converseGraph f) := IsFunction.of_mem hgf
  have hgκ : converseGraph f ∈ hartogsNumber (ω : V) ^ range f :=
    mem_function_of_mem_function_of_subset hgf hDκ
  have hgr : range (converseGraph f) = D := by rw [range_converseGraph, domain_eq_of_mem_function hf]
  by_cases hαD : α ∈ D
  · obtain ⟨h, hh, hhi, hval, hsmall⟩ := exists_hartogsOmega_injection_extending hAC hA
      (range_subset_of_mem_function hf) hgκ (converseGraph_injective f) (hgr.symm ▸ hD)
    have hfix : ∀ x ∈ D, h ‘ (f ‘ x) = x := by
      intro x hx
      rw [hval _ (value_mem_range hf hx), converseGraph_value_value hf hfi hx]
    refine ⟨h, hh, hhi, hfix, ?_, hsmall⟩
    rw [← hfix α hαD]
    exact value_mem_range hh (function_value_mem hf hαD)
  · obtain ⟨y, hyA, hyf⟩ := hnew hαD
    let g := insert ⟨y, α⟩ₖ (converseGraph f)
    let S := insert y (range f)
    have hgd : domain g = S := by simp [g, S, domain_eq_of_mem_function hgf]
    have hgr' : range g = insert α D := by simp [g, hgr]
    let : IsFunction g := IsFunction.insert (converseGraph f) y α (by
      simpa only [domain_eq_of_mem_function hgf] using hyf)
    have hg : g ∈ hartogsNumber (ω : V) ^ S := by
      rw [← hgd]
      apply mem_function_of_mem_function_of_subset (IsFunction.mem_function g)
      rw [hgr']
      intro z hz
      rcases mem_insert.mp hz with rfl | hz
      · exact hα
      · exact hDκ z hz
    have hgi : Injective g := injective_append_fresh (converseGraph_injective f) (by rwa [hgr])
    have hSA : S ⊆ A := by
      intro z hz
      rcases mem_insert.mp hz with rfl | hz
      · exact hyA
      · exact range_subset_of_mem_function hf z hz
    obtain ⟨h, hh, hhi, hval, hsmall⟩ := exists_hartogsOmega_injection_extending hAC hA hSA hg hgi
      (by rw [hgr']; exact internallyCountable_insert hD α)
    refine ⟨h, hh, hhi, ?_, ?_, hsmall⟩
    · intro x hx
      rw [hval _ (mem_insert.mpr (Or.inr (value_mem_range hf hx)))]
      apply value_eq_of_kpair_mem
      exact mem_insert.mpr (Or.inr ((pair_mem_converseGraph _ _ _).mpr
        (kpair_value_mem (by rwa [domain_eq_of_mem_function hf]))))
    · have hgy : g ‘ y = α := value_eq_of_kpair_mem (mem_insert.mpr (Or.inl rfl))
      have hhy : h ‘ y = α := (hval y (mem_insert.mpr (Or.inl rfl))).trans hgy
      rw [← hhy]
      exact value_mem_range hh hyA

end ZFVP
