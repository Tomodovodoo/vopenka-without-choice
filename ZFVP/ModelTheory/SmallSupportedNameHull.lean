import ZFVP.ModelTheory.ElementarySmallSubsetClosure
import ZFVP.ModelTheory.ForcingSaturatedName

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsElementaryInclusion
variable {Y B : V} (hY : IsElementaryInclusion Y B) [IsTransitive B]
include hY

theorem subset_of_rank_surjective_support_mem {δ η A F C e : V}
    [IsOrdinal δ] [IsOrdinal η]
    (hclosure : (Y ∩ A) ^ (hierarchy δ) ⊆ Y) (hzero : (∅ : V) ∈ Y)
    (hC : C ⊆ Y ∩ A) (hη : η ∈ δ)
    (he : e ∈ C ^ (hierarchy η)) (hre : range e = C)
    (hFC : F ⊆ C) (hFB : F ∈ B) : F ∈ Y := by
  rcases eq_empty_or_isNonempty F with hF | hF
  · exact hF.symm ▸ hzero
  have hrid : range (identity F) = F := by
    apply mem_ext
    intro z
    simp [mem_range_iff]
  obtain ⟨q, hq, hrq⟩ := surjection_extension hFC (identity_mem_function F) hrid hF
  exact hY.rank_surjective_subset_mem hclosure (subset_trans hFC hC) hFB
    (compose_function he hq) (range_compose_surjective he hq hre hrq) hη hF

theorem small_supported_saturatedName_mem {δ η A P R U τ e : V}
    [IsOrdinal δ] [IsOrdinal η]
    (hclosure : (Y ∩ A) ^ (hierarchy δ) ⊆ Y) (hzero : (∅ : V) ∈ Y)
    (hsupport : U ×ˢ P ⊆ Y ∩ A) (hη : η ∈ δ)
    (he : e ∈ (U ×ˢ P) ^ (hierarchy η)) (hre : range e = U ×ˢ P)
    (hνB : forcingSaturatedName P R U τ ∈ B) :
    forcingSaturatedName P R U τ ∈ Y :=
  hY.subset_of_rank_surjective_support_mem hclosure hzero hsupport hη he hre
    (forcingSaturatedName_subset _ _ _ _) hνB

end IsElementaryInclusion

theorem ForcingContext.small_supported_name_in_hull (M : ForcingContext V)
    {Y B δ η A U e : V} [IsTransitive B] [IsOrdinal δ] [IsOrdinal η]
    (hY : IsElementaryInclusion Y B)
    (hclosure : (Y ∩ A) ^ (hierarchy δ) ⊆ Y) (hzero : (∅ : V) ∈ Y)
    (hsupport : U ×ˢ M.P ⊆ Y ∩ A) (hη : η ∈ δ)
    (he : e ∈ (U ×ˢ M.P) ^ (hierarchy η)) (hre : range e = U ×ˢ M.P)
    (τ : ForcingName M.P) (hνB : forcingSaturatedName M.P M.R U τ.val ∈ B)
    (hcover : ∀ x ∈ M.ofName τ, ∃ σ : ForcingName M.P, σ.val ∈ U ∧ x = M.ofName σ) :
    ∃ ν : ForcingName M.P, ν.val ∈ Y ∧ M.ofName ν = M.ofName τ :=
  ⟨⟨forcingSaturatedName M.P M.R U τ.val, forcingSaturatedName_isName _ _ _ _⟩,
    hY.small_supported_saturatedName_mem hclosure hzero hsupport hη he hre hνB,
    M.saturatedName_value U τ hcover⟩

end ZFVP
