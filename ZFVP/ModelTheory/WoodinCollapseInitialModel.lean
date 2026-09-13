import ZFVP.ModelTheory.WoodinCollapseInitialGeneric
import ZFVP.SetTheory.WoodinCollapseRetraction
import ZFVP.ModelTheory.WoodinCollapsePreservation
import ZFVP.ModelTheory.ForcingRetractionSequences

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace WoodinCollapseModel

variable {κ β δ : V} (hκ : IsRegularCardinal κ) (hβ : IsRegularCardinal β)
  [IsOrdinal δ] (hβδ : β ⊆ δ) {G : Set V}
  (hG : IsExternalForcingGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) G)

noncomputable def initialContext : ForcingContext V :=
  woodinCollapseContext hκ β (woodinCollapseInitialGeneric κ β G)
    (woodinCollapse_initial_generic hκ hβ hβδ hG)

noncomputable def initialEmbedding : MembershipEndExtension
    (initialContext hκ hβ hβδ hG).Model (woodinCollapseContext hκ δ G hG).Model :=
  ForcingContext.retractionEmbedding (initialContext hκ hβ hβδ hG)
    (woodinCollapseContext hκ δ G hG) (woodinCollapse_retraction hκ hβ hβδ) (fun _ ↦ Iff.rfl)

theorem initialEmbedding_check (x : V) :
    initialEmbedding hκ hβ hβδ hG ((initialContext hκ hβ hβδ hG).check x) =
      (woodinCollapseContext hκ δ G hG).check x :=
  ForcingContext.retractionInclusion_check (initialContext hκ hβ hβδ hG)
    (woodinCollapseContext hκ δ G hG) (woodinCollapse_retraction hκ hβ hβδ)
    (fun _ ↦ Iff.rfl) rfl x

set_option maxHeartbeats 800000 in
theorem initial_function_eq {γ : V} (hγ : γ ∈ κ)
    (hDC : ∀ α ∈ κ, InternalDependentChoiceAt α)
    {X : (initialContext hκ hβ hβδ hG).Model} {f : (woodinCollapseContext hκ δ G hG).Model}
    (hf : f ∈ initialEmbedding hκ hβ hβδ hG X ^ (woodinCollapseContext hκ δ G hG).check γ) :
    ∃ g ∈ X ^ (initialContext hκ hβ hβδ hG).check γ,
      initialEmbedding hκ hβ hβδ hG g = f := by
  let := hκ.1.1
  let := IsOrdinal.of_mem hγ
  apply ForcingContext.retractionInclusion_function_of_closed (initialContext hκ hβ hβδ hG)
    (woodinCollapseContext hκ δ G hG)
    (woodinCollapse_retraction hκ hβ hβδ) (fun _ ↦ Iff.rfl) rfl (hDC γ hγ) ?_ hf
  intro α hα hαγ
  let := hα
  exact woodinCollapse_closedBelow hκ hDC δ α (ordinal_mem_of_subset_mem hαγ hγ)

theorem initial_functionSet {γ : V} (hγ : γ ∈ κ)
    (hDC : ∀ α ∈ κ, InternalDependentChoiceAt α) (X : (initialContext hκ hβ hβδ hG).Model) :
    initialEmbedding hκ hβ hβδ hG (X ^ (initialContext hκ hβ hβδ hG).check γ) =
      initialEmbedding hκ hβ hβδ hG X ^ (woodinCollapseContext hκ δ G hG).check γ := by
  let j := initialEmbedding hκ hβ hβδ hG
  apply mem_ext
  intro f
  constructor
  · intro hf
    obtain ⟨g, hg, rfl⟩ := j.endExtension _ f hf
    have ht := (j.function_iff _ _ _).mpr hg
    dsimp only [j] at ht
    rwa [initialEmbedding_check] at ht
  · intro hf
    obtain ⟨g, hg, he⟩ := initial_function_eq hκ hβ hβδ hG hγ hDC hf
    exact he ▸ (j.mem_iff _ _).mpr hg

end WoodinCollapseModel
end ZFVP
