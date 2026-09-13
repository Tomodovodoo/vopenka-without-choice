import ZFVP.SetTheory.UniformRank
import ZFVP.SetTheory.BoundedFunctionDomain

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def shortRankEnumerationsFormula : SetTheorySemisentence 2 :=
  f“θ κ. ∀ α ∈ θ, ∃ γ ∈ κ, ∃ e,
    !boundedFunctionFormula e γ (!hierarchyFormula α) ∧ !range.dfn e = !hierarchyFormula α”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- All ranks below the first ordinal have enumerations shorter than the second. -/
def HasShortRankEnumerations (θ κ : V) : Prop :=
  ∀ α ∈ θ, ∃ γ ∈ κ, ∃ e ∈ (hierarchy α) ^ γ, range e = hierarchy α

instance shortRankEnumerationsFormula_defined : ℒₛₑₜ-relation[V] HasShortRankEnumerations
    via shortRankEnumerationsFormula :=
  ⟨fun v ↦ by simp [shortRankEnumerationsFormula, HasShortRankEnumerations]⟩

theorem shortRankEnumerations_empty (κ : V) : HasShortRankEnumerations ∅ κ := by
  intro α hα
  exact False.elim (not_mem_empty hα)

theorem HasShortRankEnumerations.mono {θ θ' κ κ' : V}
    (h : HasShortRankEnumerations θ κ) (hθ : θ' ⊆ θ) (hκ : κ ⊆ κ') :
    HasShortRankEnumerations θ' κ' := by
  intro α hα
  obtain ⟨γ, hγ, e, he, hr⟩ := h α (hθ α hα)
  exact ⟨γ, hκ γ hγ, e, he, hr⟩

theorem ElementaryMap.shortRankEnumerations_iff {W : Type*} [SetStructure W]
    [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (j : ElementaryMap V W) (θ κ : V) :
    HasShortRankEnumerations θ κ ↔ HasShortRankEnumerations (j θ) (j κ) :=
  j.map_defined shortRankEnumerationsFormula
    (fun v ↦ HasShortRankEnumerations (v 0) (v 1))
    (fun v ↦ HasShortRankEnumerations (v 0) (v 1)) ![θ, κ]

end ZFVP
