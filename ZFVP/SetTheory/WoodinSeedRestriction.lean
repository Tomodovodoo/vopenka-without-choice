import ZFVP.SetTheory.WoodinSeedInsertion
import ZFVP.SetTheory.ForcingSystemExtension

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinInsertSeed_restrict {θ α f a : V} [IsOrdinal θ] [IsOrdinal α]
    [IsFunction f] (hf : domain f = θ) (hα : α ⊆ θ) :
    woodinInsertSeed α (f ↾ α) a = (woodinInsertSeed θ f a) ↾ (woodinSourceIndex α) := by
  have hs : woodinSourceIndex α ⊆ woodinSourceIndex θ := ordinalAdd_mono_right 1 hα
  apply functions_eq_of_domain_values
  · rw [woodinInsertSeed_domain, domain_restrict_eq, woodinInsertSeed_domain]
    apply mem_ext
    intro x
    simp only [mem_inter_iff]
    exact ⟨fun h ↦ ⟨hs x h, h⟩, fun h ↦ h.2⟩
  · intro β hβ
    rw [woodinInsertSeed_domain] at hβ
    rw [value_restrict (by rw [woodinInsertSeed_domain]; exact hs β hβ) hβ]
    by_cases hz : β = ∅
    · subst β
      rw [woodinInsertSeed_zero, woodinInsertSeed_zero]
    · let := IsOrdinal.of_mem hβ
      have hr : woodinRecursiveIndex β ∈ α := (woodinRecursiveIndex_mem_iff hz).mpr hβ
      rw [woodinInsertSeed_nonzero hβ hz, woodinInsertSeed_nonzero (hs β hβ) hz,
        value_restrict (by rw [hf]; exact hα _ hr) hr]

theorem woodinRemoveSeed_restrict {θ α g : V} [IsOrdinal θ] [IsOrdinal α]
    [IsFunction g] (hg : domain g = woodinSourceIndex θ) (hα : α ⊆ θ) :
    woodinRemoveSeed α (g ↾ (woodinSourceIndex α)) = (woodinRemoveSeed θ g) ↾ α := by
  apply functions_eq_of_domain_values
  · rw [woodinRemoveSeed_domain, domain_restrict_eq, woodinRemoveSeed_domain]
    apply mem_ext
    intro x
    simp only [mem_inter_iff]
    exact ⟨fun h ↦ ⟨hα x h, h⟩, fun h ↦ h.2⟩
  · intro β hβ
    rw [woodinRemoveSeed_domain] at hβ
    let := IsOrdinal.of_mem hβ
    rw [woodinRemoveSeed_value hβ,
      value_restrict (by rw [woodinRemoveSeed_domain]; exact hα β hβ) hβ,
      woodinRemoveSeed_value (hα β hβ),
      value_restrict (by rw [hg]; exact woodinSourceIndex_mem_iff.mpr (hα β hβ))
        (woodinSourceIndex_mem_iff.mpr hβ)]

theorem woodinInsertSeed_familyNext {θ P Q a : V} [IsOrdinal θ] :
    woodinInsertSeed (succ θ) (forcingFamilyNext θ P Q) a =
      forcingFamilyNext (woodinSourceIndex θ) (woodinInsertSeed θ P a) Q := by
  have hfun : IsFunction (forcingFamilyNext (woodinSourceIndex θ)
      (woodinInsertSeed θ P a) Q) := by unfold forcingFamilyNext; infer_instance
  let := hfun
  apply functions_eq_of_domain_values
  · rw [woodinInsertSeed_domain, woodinSourceIndex_successor]
    exact (domain_definableGraph _ _ _).symm
  · intro β hβ
    rw [woodinInsertSeed_domain] at hβ
    by_cases hz : β = ∅
    · subst β
      have hzero : (∅ : V) ∈ woodinSourceIndex θ :=
        subset_ordinalAdd 1 θ ∅ (by change (0 : V) ∈ succ 0; simp)
      rw [woodinInsertSeed_zero, forcingFamilyNext_old hzero, woodinInsertSeed_zero]
    · let := IsOrdinal.of_mem hβ
      have hr : woodinRecursiveIndex β ∈ succ θ := (woodinRecursiveIndex_mem_iff hz).mpr hβ
      have he := woodinSourceIndex_recursiveIndex β hz
      rw [← he, woodinInsertSeed_at_sourceIndex hr]
      rcases mem_succ_iff.mp hr with heq | hold
      · rw [heq, forcingFamilyNext_new, forcingFamilyNext_new]
      · rw [forcingFamilyNext_old hold,
          forcingFamilyNext_old (woodinSourceIndex_mem_iff.mpr hold),
          woodinInsertSeed_at_sourceIndex hold]

end ZFVP
