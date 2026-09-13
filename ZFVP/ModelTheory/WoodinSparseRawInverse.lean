import ZFVP.ModelTheory.WoodinSparseSourceQuotientClosure
import ZFVP.ModelTheory.RetractionIsomorphismHartogs

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal θ]
local notation "s" => woodinIterationPrefix θ
local notation "c" => woodinSparsePrefixCode θ
local notation "m" => woodinRecodingMaps (woodinSparseRecodingHistory θ)
local notation "r" => forcingNormalizationInverseMap θ s (woodinNormalizationHistory θ)
local notation "P" => forcingInverseCodePoset θ s
local notation "R" => forcingInverseCodeOrder θ s
local notation "N" => woodinNormalizedInverseBase θ
local notation "T" => woodinNormalizedInverseOrder θ

theorem woodinNormalizationInverse_retraction
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (h0 : ∅ ∈ θ) :
    IsForcingRetraction N T P R r := by
  have hs := woodinIterationPrefix_of_stages
    (fun i hi ↦ ((woodinIterationExit hΩ hAC).2.1 i (hθ i hi)).1)
  have hr := (forcingNormalizationInverse_base hs.code
    (woodinNormalizationHistory_actual_prefix hΩ hAC hθ) h0).1
  obtain ⟨hb, he⟩ := woodinNormalized_inverse_base_dictionary hΩ hAC hθ
  rwa [hb, he] at hr

theorem woodinNormalizationInverse_equivalent
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (h0 : ∅ ∈ θ)
    {p : V} (hp : p ∈ P) : ⟨r ‘ p, p⟩ₖ ∈ R ∧ ⟨p, r ‘ p⟩ₖ ∈ R := by
  have hs := woodinIterationPrefix_of_stages
    (fun i hi ↦ ((woodinIterationExit hΩ hAC).2.1 i (hθ i hi)).1)
  exact (forcingNormalizationInverse_base hs.code
    (woodinNormalizationHistory_actual_prefix hΩ hAC hθ) h0).2.2 p hp

theorem woodinSparseRawInverse_isomorphism
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : ∅ ∈ θ) (hlim : ∀ i ∈ θ, succ i ∈ θ) :
    IsForcingIsomorphism N T (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c)
      (woodinSparseInverseBaseMap θ c m) := by
  apply woodinSparseInverseBaseMap_isomorphism hΩ hAC hθ
    (woodinSparsePrefix_family hΩ hAC hθ) (woodinSparsePrefix_preorders hΩ hAC hθ)
    (woodinSparseRecodingHistory_tables θ).1 (woodinSparseRecodingHistory_tables θ).2.1 h0 hlim
  · intro i hi p hp
    exact woodinSparseHistory_sparse (fun j hj ↦ woodinSparseRecodingRec_correct hΩ hAC j (hθ j hj)) hi hp
  · intro i hi j hj hij p hp
    let := IsOrdinal.of_mem hj
    exact woodinSparseHistory_projection hΩ hAC hθ
      (fun k hk ↦ woodinSparseRecodingRec_correct hΩ hAC k (hθ k hk)) hi hj (IsOrdinal.toIsTransitive.transitive _ hij) hp

theorem woodinSparseRawInverse_laws
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : ∅ ∈ θ) (hlim : ∀ i ∈ θ, succ i ∈ θ) :
    IsForcingPreorder (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c) ∧
      IsForcingTop (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c) ∅ := by
  apply woodinSparseInverseBase_recoded_laws hΩ hAC hθ
    (woodinSparsePrefix_family hΩ hAC hθ) (woodinSparsePrefix_preorders hΩ hAC hθ)
    (woodinSparseRecodingHistory_tables θ).1 (woodinSparseRecodingHistory_tables θ).2.1 h0 hlim
  · intro i hi p hp
    exact woodinSparseHistory_sparse (fun j hj ↦ woodinSparseRecodingRec_correct hΩ hAC j (hθ j hj)) hi hp
  · intro i hi j hj hij p hp
    let := IsOrdinal.of_mem hj
    exact woodinSparseHistory_projection hΩ hAC hθ
      (fun k hk ↦ woodinSparseRecodingRec_correct hΩ hAC k (hθ k hk)) hi hj (IsOrdinal.toIsTransitive.transitive _ hij) hp
  · intro i hi
    exact woodinSparseHistory_top hΩ hAC hθ (fun j hj ↦ woodinSparseRecodingRec_correct hΩ hAC j (hθ j hj)) hi

theorem woodinSparseRawInverse_top
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : ∅ ∈ θ) (hlim : ∀ i ∈ θ, succ i ∈ θ) :
    (woodinSparseInverseBaseMap θ c m) ‘ (forcingInverseCodeTop θ s) = ∅ := by
  apply woodinSparseInverseBaseMap_top hΩ hAC hθ
    (woodinSparsePrefix_family hΩ hAC hθ) (woodinSparsePrefix_preorders hΩ hAC hθ)
    (woodinSparseRecodingHistory_tables θ).1 (woodinSparseRecodingHistory_tables θ).2.1 h0 hlim
  · intro i hi p hp
    exact woodinSparseHistory_sparse (fun j hj ↦ woodinSparseRecodingRec_correct hΩ hAC j (hθ j hj)) hi hp
  · intro i hi j hj hij p hp
    let := IsOrdinal.of_mem hj
    exact woodinSparseHistory_projection hΩ hAC hθ
      (fun k hk ↦ woodinSparseRecodingRec_correct hΩ hAC k (hθ k hk)) hi hj (IsOrdinal.toIsTransitive.transitive _ hij) hp
  · intro i hi
    exact woodinSparseHistory_top hΩ hAC hθ (fun j hj ↦ woodinSparseRecodingRec_correct hΩ hAC j (hθ j hj)) hi

end ZFVP

