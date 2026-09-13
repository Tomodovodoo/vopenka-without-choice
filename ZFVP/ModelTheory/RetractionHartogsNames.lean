import ZFVP.ModelTheory.SaturatedHartogsSpecification
import ZFVP.ModelTheory.RetractionCanonicalNames

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u
variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsForcingRetraction.hartogs_name_equality {P R N T m one p : V}
    (hr : IsForcingRetraction N T P R m)
    (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (he : ∀ q ∈ P, ⟨m ‘ q, q⟩ₖ ∈ R ∧ ⟨q, m ‘ q⟩ₖ ∈ R)
    (ht : IsForcingTop P R one) (ho : one ∈ N) (hp : p ∈ P)
    (τ : ForcingName P) (υ : ForcingName N)
    (hτυ : m ‘ p ∈ atomicEquality N T (nameAction m τ.val) υ.val) :
    m ‘ p ∈ atomicEquality N T (nameAction m (hartogsNumberName P R τ.val))
      (hartogsNumberName N T υ.val) := by
  refine hr.unique_relation_equality hartogsNumberFormula ?_ hR hT he (hr.top_of_mem ht ho) hp ![τ] ![υ]
    ⟨_, hartogsNumberName_isName _ _ _⟩ ⟨_, hartogsNumberName_isName _ _ _⟩ ?_ ?_ ?_
  · intro W _ _ _ v x y hx hy
    exact ((hartogsNumberFormula_defined.iff _).mp hx).trans ((hartogsNumberFormula_defined.iff _).mp hy).symm
  · intro i
    exact Fin.cases hτυ (fun j ↦ Fin.elim0 j) i
  · exact hartogsNumberName_forces hR ht hp τ
  · exact hartogsNumberName_forces hT (hr.top_of_mem ht ho) (function_value_mem hr.maps hp) υ

theorem IsForcingRetraction.saturated_hartogs_equality {P R N T m one γ δ p : V}
    (hr : IsForcingRetraction N T P R m)
    (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (he : ∀ q ∈ P, ⟨m ‘ q, q⟩ₖ ∈ R ∧ ⟨q, m ‘ q⟩ₖ ∈ R)
    (ht : IsForcingTop P R one) (ho : one ∈ N)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hγ : γ ∈ δ) (hp : p ∈ P) :
    m ‘ p ∈ atomicEquality N T (nameAction m (saturatedHartogsPosetName P R one γ δ))
      (saturatedHartogsPosetName N T one γ δ) := by
  let := hδ.1
  have hN := subset_mem_hierarchy_limit hδ.rankCriterion.2.2.1 hP hr.inclusion
  have hc (a : V) : m ‘ p ∈ atomicEquality N T (nameAction m (checkName one a)) (checkName one a) := by
    rw [nameAction_checkName ht.1 (hr.fixes one ho), atomicEquality_refl hT]
    exact function_value_mem hr.maps hp
  have hH := hr.hartogs_name_equality hR hT he ht ho hp
    ⟨checkName one γ, checkName_isName ht.1 γ⟩ ⟨checkName one γ, checkName_isName ho γ⟩ (hc γ)
  refine hr.unique_relation_equality totalWoodinCollapseFormula ?_ hR hT he (hr.top_of_mem ht ho) hp
    ![⟨hartogsNumberName P R (checkName one γ), hartogsNumberName_isName _ _ _⟩,
      ⟨checkName one δ, checkName_isName ht.1 δ⟩]
    ![⟨hartogsNumberName N T (checkName one γ), hartogsNumberName_isName _ _ _⟩,
      ⟨checkName one δ, checkName_isName ho δ⟩]
    ⟨_, saturatedHartogsPosetName_isName P R one γ δ⟩
    ⟨_, saturatedHartogsPosetName_isName N T one γ δ⟩ ?_ ?_ ?_
  · intro W _ _ _ v x y hx hy
    exact ((totalWoodinCollapseFormula_defined.iff _).mp hx).trans
      ((totalWoodinCollapseFormula_defined.iff _).mp hy).symm
  · intro i
    exact Fin.cases hH (fun j ↦ Fin.cases (hc δ) (fun k ↦ Fin.elim0 k) j) i
  · exact saturatedHartogsPosetName_forces hR ht hδ hP hγ hp
  · exact saturatedHartogsPosetName_forces hT (hr.top_of_mem ht ho) hδ hN hγ (function_value_mem hr.maps hp)

end ZFVP
