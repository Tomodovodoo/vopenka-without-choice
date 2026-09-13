import ZFVP.ModelTheory.TransitiveZFMinimalSupport
import ZFVP.ModelTheory.WoodinNormalizedCodeRankAgreement
import ZFVP.ModelTheory.RankSparseLimits
import ZFVP.ModelTheory.WoodinSparseDirectTransport

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rank_forcingRecodedSparseMap_val {ξ : V} [IsOrdinal ξ]
    [Nonempty (SetDomain (hierarchy ξ))] [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hs : ∀ β ∈ ξ, succ β ∈ ξ) (θ s z m A : SetDomain (hierarchy ξ)) :
    (forcingRecodedSparseMap θ s z m A).val = forcingRecodedSparseMap θ.val s.val z.val m.val A.val := by
  let := hierarchy_transitive ξ
  unfold forcingRecodedSparseMap
  rw [TransitiveZF.compose_val, TransitiveZF.forcingThreadActionMap_val,
    rank_forcingDirectLimit_val hs, TransitiveZF.forcingSparseEncode_val,
    TransitiveZF.forcingCodeP_val, TransitiveZF.forcingCodeπ_val,
    TransitiveZF.forcingCodeE_val, TransitiveZF.forcingCodeUniverse_val]

theorem IsWoodinSupercompact.rank_woodinSparseDirectMap_val {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    letI := hΩ.inaccessible.1
    letI := rankDomain_nonempty hΩ.inaccessible.2.1
    letI := hΩ.inaccessible.rankCriterion.models_zf
    ∀ θ c m : SetDomain (hierarchy Ω), IsOrdinal θ →
      (woodinSparseDirectMap θ c m).val = woodinSparseDirectMap θ.val c.val m.val := by
  let := hΩ.inaccessible.1
  let := rankDomain_nonempty hΩ.inaccessible.2.1
  let := hΩ.inaccessible.rankCriterion.models_zf
  let := hierarchy_transitive Ω
  intro θ c m hθ
  let := hθ
  have hs := hΩ.inaccessible.rankCriterion.2.2.1
  have hp := TransitiveZF.woodinIterationPrefixes_val_of_previous (hierarchy Ω) θ
    (fun i hi ↦ hΩ.rank_woodinIterationRec_val hAC i (IsOrdinal.of_mem hi))
  unfold woodinSparseDirectMap woodinRecodedDirectMap
  rw [TransitiveZF.compose_val, TransitiveZF.compose_val,
    rank_forcingRecodedSparseMap_val hs, TransitiveZF.forcingSparseDecode_val,
    TransitiveZF.woodinSparseDirectFlatten_val_rank Ω hs,
    TransitiveZF.forcingCodeUniverse_val, TransitiveZF.forcingCodeUniverse_val,
    hp.1, (hΩ.rank_woodinNormalizedCode_val hAC θ hθ).1]
end ZFVP

