import ZFVP.SetTheory.RankEnumerationInaccessible
import ZFVP.SetTheory.InaccessibleFunctionClosure
import ZFVP.SetTheory.WellOrderingChoice
import ZFVP.ModelTheory.TransitiveZFValues

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rank_internalChoice_of_shortEnumerations {κ : V}
    (hκ : IsChoicelessInaccessible κ) (hr : HasShortRankEnumerations κ κ)
    [Nonempty (SetDomain (hierarchy κ))] [(SetDomain (hierarchy κ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙] :
    InternalChoice (SetDomain (hierarchy κ)) := by
  let := hκ.1
  let U := hierarchy κ
  let := hierarchy_transitive κ
  intro A hn
  have hA : A.val ∈ hierarchy κ := A.property
  have hu : ⋃ˢ A.val ∈ hierarchy κ := sUnion_mem_hierarchy_limit hκ.rankCriterion.2.2.1 hA
  have hnonempty : ∀ X ∈ A.val, IsNonempty X := by
    intro X hX
    let X' : SetDomain U := ⟨X, (hierarchy_transitive κ).mem_trans hX hA⟩
    obtain ⟨x, hx⟩ := hn X' hX
    exact ⟨x.val, hx⟩
  obtain ⟨f, hf, hsel⟩ := choiceFunction_of_wellOrderable_union (hr.member_wellOrderable hu) hnonempty
  have hfU : f ∈ hierarchy κ := hκ.function_mem hA
    (mem_function_of_mem_function_of_subset hf (IsTransitive.transitive _ hu))
  let f' : SetDomain U := ⟨f, hfU⟩
  refine ⟨f', ?_, ?_⟩
  · apply (TransitiveZF.function_iff U f' A (⋃ˢ A)).mpr
    simpa only [TransitiveZF.sUnion_val] using hf
  · intro X hX
    change (f' ‘ X).val ∈ X.val
    rw [TransitiveZF.value_val_total]
    exact hsel X.val hX

theorem rank_models_zfc_of_shortEnumerations {κ : V}
    (hr : HasShortRankEnumerations κ κ) (hκ : IsRegularCardinal κ) (hω : (ω : V) ∈ κ)
    [Nonempty (SetDomain (hierarchy κ))] : (SetDomain (hierarchy κ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖 := by
  have hi := hr.inaccessible hκ hω
  let := hi.rankCriterion.models_zf
  let := models_ac_of_internalChoice (rank_internalChoice_of_shortEnumerations hi hr)
  refine ⟨?_⟩
  intro φ hφ
  rcases hφ with hφ | hφ
  · exact Theory.models (SetDomain (hierarchy κ)) 𝗭𝗙 hφ
  · exact Theory.models (SetDomain (hierarchy κ)) 𝗔𝗖 hφ

end ZFVP
