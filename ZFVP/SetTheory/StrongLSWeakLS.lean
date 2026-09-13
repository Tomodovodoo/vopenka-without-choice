import ZFVP.ModelTheory.ElementaryIntersectionTruthTable
import ZFVP.ModelTheory.ElementaryParameterClosure
import ZFVP.SetTheory.LowenheimSkolemCardinals
import ZFVP.SetTheory.PulledWellOrder

/-! Strong LS implies weak LS. The hull is intersected with the requested rank;
a truth table among its parameters ensures elementarity for every internal code. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsLSCardinal.weaklyLSCardinal {κ : V} (hκ : IsLSCardinal κ) :
    IsWeaklyLSCardinal κ := by
  let := hκ.1.1
  refine ⟨hκ.1, hκ.2.1, ?_⟩
  intro δ hδ α hα hκα x hx
  let := hα
  let := IsOrdinal.of_mem hδ
  have hωκ : (ω : V) ⊆ κ := IsOrdinal.toIsTransitive.transitive _ hκ.2.1
  have hsω : succ (ω : V) ∈ κ := initial_succ_mem hκ.1 hωκ hκ.2.1
  obtain ⟨γ, hγκ, hδγ, hlowγ⟩ :
      ∃ γ : V, γ ∈ κ ∧ δ ⊆ γ ∧ succ (ω : V) ⊆ γ := by
    rcases IsOrdinal.subset_or_supset (α := δ) (β := succ (ω : V)) with h | h
    · exact ⟨succ (ω : V), hsω, h, subset_refl _⟩
    · exact ⟨δ, hδ, subset_refl _, h⟩
  let := IsOrdinal.of_mem hγκ
  let a := hierarchy α
  let U := codingUniverse a
  let T := membershipModelTruthTable a
  let p := ⟨⟨U, T⟩ₖ, ⟨a, x⟩ₖ⟩ₖ
  let η := rank ({p, κ} : V)
  have hpη : p ∈ hierarchy η := (mem_hierarchy_iff_rank_mem _ _).mpr
    (rank_mem (show p ∈ ({p, κ} : V) by simp))
  have hκη : κ ∈ η := by
    simpa only [rank_of_ordinal] using rank_mem (show κ ∈ ({p, κ} : V) by simp)
  obtain ⟨β, X, hβ, _, hX, hγX, hpX, hsmall, _⟩ :=
    hκ.2.2 γ hγκ η inferInstance (IsOrdinal.toIsTransitive.transitive _ hκη) p hpη
  let := hβ
  let := hierarchy_transitive β
  have hparts := hX.kpair_components_mem hpX
  have hUT := hX.kpair_components_mem hparts.1
  have hax := hX.kpair_components_mem hparts.2
  have hlow : hierarchy (succ (ω : V)) ⊆ X := subset_trans (hierarchy_mono hlowγ) hγX
  obtain ⟨C, hC, f, hf⟩ := hsmall
  let : IsTransitive a := hierarchy_transitive α
  let : IsSequenceSupport U := codingUniverse_isSequenceSupport a
  have haU : a ⊆ U := (codingUniverse_transitive a).transitive a (self_mem_codingUniverse a)
  have he : IsElementaryInclusion (X ∩ a) a :=
    elementaryIntersection_of_truthTable hX hf hlow hax.1 ⟨x, hx⟩ hUT.1 haU hUT.2
      (membershipModelTruthTable_correct a)
  refine ⟨X ∩ a, he, ?_, mem_inter_iff.mpr ⟨hax.2, hx⟩, ?_⟩
  · intro u hu
    exact mem_inter_iff.mpr ⟨hγX u (hierarchy_mono hδγ u hu),
      hierarchy_mono (subset_trans (IsOrdinal.toIsTransitive.transitive _ hδ) hκα) u hu⟩
  · exact ⟨f ‘ a, (hierarchy_transitive κ).mem_trans (function_value_mem hf.2.1 hax.1) hC,
      f ↾ (X ∩ a), transitiveCollapse_restrict_member hf hax.1⟩

end ZFVP
