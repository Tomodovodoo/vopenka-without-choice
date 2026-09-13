import ZFVP.ModelTheory.WoodinSparseInverseBase

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ Q T m : V} [IsOrdinal θ]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
variable (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP (woodinNormalizedPrefixCode θ)) ‘ i)
  ((forcingCodeR (woodinNormalizedPrefixCode θ)) ‘ i) (Q ‘ i) (T ‘ i) (m ‘ i))
variable (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i))
variable (hQt : IsIterationTable θ Q) (hTt : IsIterationTable θ T)
variable (h0 : ∅ ∈ θ) (hlim : ∀ i ∈ θ, succ i ∈ θ)
variable (hsp : ∀ i ∈ θ, ∀ p ∈ Q ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p)
variable (hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ Q ‘ j,
  ((forcingRecodedProjections θ (woodinNormalizedPrefixCode θ) m) ‘ ⟨i, j⟩ₖ) ‘ p =
    p ↾ (succ (woodinSourceIndex i)))

local notation "c" => forcingRecodedCode θ (woodinNormalizedPrefixCode θ) Q T m

include hΩ hAC hθ hm hT hQt hTt h0 hlim hsp hπ

theorem woodinSparseInverseFlatten_recoded_isomorphism :
    IsForcingIsomorphism (forcingInverseCodePoset θ c) (forcingInverseCodeOrder θ c)
      (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c) (woodinSparseInverseFlatten θ c) := by
  apply woodinSparseInverseFlatten_isomorphism
    (forcingRecoded_code (woodinNormalizedPrefixCode_valid hΩ hAC hθ) hm hT hQt hTt) h0 hlim
  · simpa only [forcingRecodedCode, forcingCodeP_code] using hsp
  · simpa only [forcingRecodedCode, forcingCodeP_code, forcingCodeπ_code] using hπ

theorem woodinSparseInverseBaseMap_isomorphism :
    IsForcingIsomorphism (woodinNormalizedInverseBase θ) (woodinNormalizedInverseOrder θ)
      (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c) (woodinSparseInverseBaseMap θ c m) := by
  have hf := woodinRecodedInverseBaseMap_isomorphism (Q := Q) (T := T) (m := m) hΩ hAC hθ hm hT hQt hTt
  exact hf.comp (woodinSparseInverseFlatten_recoded_isomorphism hΩ hAC hθ hm hT hQt hTt h0 hlim hsp hπ)

theorem woodinSparseInverseBaseMap_value {p : V} (hp : p ∈ woodinNormalizedInverseBase θ) :
    (woodinSparseInverseBaseMap θ c m) ‘ p = ⋃ˢ range (forcingThreadAction θ m p) := by
  have hf := woodinRecodedInverseBaseMap_isomorphism (Q := Q) (T := T) (m := m) hΩ hAC hθ hm hT hQt hTt
  have he := woodinSparseInverseFlatten_recoded_isomorphism hΩ hAC hθ hm hT hQt hTt h0 hlim hsp hπ
  have hsp' : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p := by
    simpa only [forcingRecodedCode, forcingCodeP_code] using hsp
  have hπ' : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ (forcingCodeP c) ‘ j,
      ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i)) := by
    simpa only [forcingRecodedCode, forcingCodeP_code, forcingCodeπ_code] using hπ
  rw [woodinSparseInverseBaseMap, value_compose_of_mem_function hf.1 he.1 hp,
    woodinSparseInverseFlatten_value hsp' hπ' (function_value_mem hf.1 hp),
    woodinRecodedInverseBaseMap, forcingThreadActionMap_value hp]

theorem woodinSparseInverseBaseMap_restrict {p i : V} (hp : p ∈ woodinNormalizedInverseBase θ) (hi : i ∈ θ) :
    ((woodinSparseInverseBaseMap θ c m) ‘ p) ↾ (succ (woodinSourceIndex i)) = (m ‘ i) ‘ (p ‘ i) := by
  have hf := woodinRecodedInverseBaseMap_isomorphism (Q := Q) (T := T) (m := m) hΩ hAC hθ hm hT hQt hTt
  have he := woodinSparseInverseFlatten_recoded_isomorphism hΩ hAC hθ hm hT hQt hTt h0 hlim hsp hπ
  have hsp' : ∀ i ∈ θ, ∀ p ∈ (forcingCodeP c) ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p := by
    simpa only [forcingRecodedCode, forcingCodeP_code] using hsp
  have hπ' : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ (forcingCodeP c) ‘ j,
      ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i)) := by
    simpa only [forcingRecodedCode, forcingCodeP_code, forcingCodeπ_code] using hπ
  rw [woodinSparseInverseBaseMap, value_compose_of_mem_function hf.1 he.1 hp,
    woodinSparseInverseFlatten_restrict hsp' hπ' (function_value_mem hf.1 hp) hi,
    woodinRecodedInverseBaseMap_coordinate hp hi]

end ZFVP
