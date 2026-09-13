import ZFVP.ModelTheory.SaturatedWoodinPrefix
import ZFVP.ModelTheory.SaturatedCollapseBounds
import ZFVP.ModelTheory.ForcingHartogsName
import ZFVP.SetTheory.InaccessibleHartogs

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

noncomputable def saturatedHartogsCollapseName (A : ForcingContext V) (γ δ : V) : ForcingName A.P :=
  ⟨saturatedWoodinCollapseName A.P A.R δ
    (hartogsNumberName A.P A.R (checkName A.one γ)) (checkName A.one δ),
    forcingSaturatedName_isName _ _ _ _⟩

theorem hartogs_checked_mem (A : ForcingContext V) {γ δ : V}
    (hδ : IsChoicelessInaccessible δ) (hP : A.P ∈ hierarchy δ) (hγ : γ ∈ δ) :
    hartogsNumber (A.check γ) ∈ A.check δ := by
  let := hδ.1
  let := IsOrdinal.of_mem hγ
  exact (A.check_inaccessible_of_small hδ hP).hartogsNumber_mem
    (ordinal_mem_hierarchy_iff.mpr ((A.check_mem_iff _ _).mpr hγ))

theorem saturatedHartogsCollapseName_value (A : ForcingContext V) {γ δ : V}
    (hδ : IsChoicelessInaccessible δ) (hP : A.P ∈ hierarchy δ) (hγ : γ ∈ δ) :
    A.ofName (A.saturatedHartogsCollapseName γ δ) =
      woodinCollapse (hartogsNumber (A.check γ)) (A.check δ) := by
  let := hδ.1
  let τ : ForcingName A.P := ⟨checkName A.one γ, checkName_isName A.top.1 _⟩
  let κ := A.hartogsName τ
  let ν : ForcingName A.P := ⟨checkName A.one δ, checkName_isName A.top.1 _⟩
  let : IsOrdinal (A.ofName ν) := by change IsOrdinal (A.check δ); infer_instance
  have hv : A.ofName κ = hartogsNumber (A.check γ) := A.hartogsName_value τ
  have hc : A.ofName (A.collapseName κ ν) =
      woodinCollapse (hartogsNumber (A.check γ)) (A.check δ) := by
    rw [A.collapseName_value_of_ordinal, hv]
    rfl
  have hcover : A.ofName (A.collapseName κ ν) ⊆ hierarchy (A.check δ) := by
    rw [hc]
    exact fun _ hp ↦ woodinCollapse_condition_mem_hierarchy
      (A.check_inaccessible_of_small hδ hP).regular
      (IsOrdinal.toIsTransitive.transitive _ (A.hartogs_checked_mem hδ hP hγ)) hp
  exact (A.saturatedName_value_of_hierarchy δ (A.collapseName κ ν) hcover).trans hc

theorem saturatedHartogsCollapseOrderName_value (A : ForcingContext V) {γ δ : V}
    (hδ : IsChoicelessInaccessible δ) (hP : A.P ∈ hierarchy δ) (hγ : γ ∈ δ) :
    A.ofName (A.reverseOrderName (A.saturatedHartogsCollapseName γ δ)) =
      woodinCollapseOrder (hartogsNumber (A.check γ)) (A.check δ) := by
  rw [A.reverseOrderName_value, A.saturatedHartogsCollapseName_value hδ hP hγ]
  rfl

end ForcingContext
end ZFVP
