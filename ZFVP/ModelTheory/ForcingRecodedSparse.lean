import ZFVP.ModelTheory.ForcingSparseCode
import ZFVP.ModelTheory.ForcingRecodedLimits

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Apply the coordinate maps, then use the target's least-support code. -/
noncomputable def forcingRecodedSparseMap (θ s z m U : V) : V :=
  compose
    (forcingThreadActionMap θ m (forcingDirectLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s) U))
    (forcingSparseEncode θ z (forcingCodeUniverse z))

instance forcingRecodedSparseMap_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (forcingRecodedSparseMap (V := V)) := by
  unfold forcingRecodedSparseMap
  apply Language.DefinableFunction₂.comp
  · apply Language.DefinableFunction₃.comp
    · definability
    · definability
    · apply Language.DefinableFunction₅.comp <;> definability
  · apply Language.DefinableFunction₃.comp
    · definability
    · definability
    · unfold forcingCodeUniverse
      definability

variable {θ s Q T m U : V} [IsOrdinal θ]
variable (hs : IsForcingIterationCode θ s)
variable (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
  (Q ‘ i) (T ‘ i) (m ‘ i))
variable (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i))
variable (hQt : IsIterationTable θ Q) (hTt : IsIterationTable θ T)
variable (hU : ∀ i ∈ θ, (forcingCodeP s) ‘ i ⊆ U)
local notation "c" => forcingRecodedCode θ s Q T m
local notation "D" => forcingDirectLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s) U
local notation "R" => forcingThreadOrder θ (forcingCodeR s) D
local notation "Dc" => forcingDirectLimit θ (forcingCodeP c) (forcingCodeπ c) (forcingCodeE c) (forcingCodeUniverse c)
local notation "Rc" => forcingThreadOrder θ (forcingCodeR c) Dc
local notation "A" => forcingSparseCodes θ c (forcingCodeUniverse c)
local notation "B" => forcingSparseOrder θ c (forcingCodeUniverse c)

include hs hm hT hQt hTt hU

theorem forcingRecodedSparse_thread_isomorphism :
    IsForcingIsomorphism D R Dc Rc (forcingThreadActionMap θ m D) := by
  have hc := forcingRecoded_code hs hm hT hQt hTt
  have hQ : ∀ i ∈ θ, Q ‘ i ⊆ forcingCodeUniverse c := by
    simpa only [forcingRecodedCode, forcingCodeP_code] using hc.subset_universe
  simpa only [forcingRecodedCode, forcingCodeP_code, forcingCodeR_code, forcingCodeπ_code, forcingCodeE_code]
    using forcingRecoded_directLimit_isomorphism hs hm hU hQ

theorem forcingRecodedSparseMap_isomorphism :
    IsForcingIsomorphism D R A B (forcingRecodedSparseMap θ s c m U) := by
  have hc := forcingRecoded_code hs hm hT hQt hTt
  exact (forcingRecodedSparse_thread_isomorphism hs hm hT hQt hTt hU).comp
    (forcingSparseEncode_isomorphism hc hc.subset_universe)

theorem forcingRecodedSparseMap_value {f : V} (hf : f ∈ D) :
    (forcingRecodedSparseMap θ s c m U) ‘ f =
      (forcingSparseEncode θ c (forcingCodeUniverse c)) ‘ (forcingThreadAction θ m f) := by
  have hc := forcingRecoded_code hs hm hT hQt hTt
  rw [forcingRecodedSparseMap,
    value_compose_of_mem_function (forcingRecodedSparse_thread_isomorphism hs hm hT hQt hTt hU).1
      (forcingSparseEncode_isomorphism hc hc.subset_universe).1 hf,
    forcingThreadActionMap_value hf]

theorem forcingRecodedSparseMap_decode {f : V} (hf : f ∈ D) :
    (forcingSparseDecode θ c (forcingCodeUniverse c)) ‘ ((forcingRecodedSparseMap θ s c m U) ‘ f) =
      forcingThreadAction θ m f := by
  have hc := forcingRecoded_code hs hm hT hQt hTt
  have hh := function_value_mem (forcingRecodedSparse_thread_isomorphism hs hm hT hQt hTt hU).1 hf
  rw [forcingThreadActionMap_value hf] at hh
  rw [forcingRecodedSparseMap_value hs hm hT hQt hTt hU hf,
    forcingSparseEncode_decode hc hc.subset_universe hh]

theorem forcingRecodedSparseMap_coordinate {f i : V} (hf : f ∈ D) (hi : i ∈ θ) :
    ((forcingSparseDecode θ c (forcingCodeUniverse c)) ‘ ((forcingRecodedSparseMap θ s c m U) ‘ f)) ‘ i =
      (m ‘ i) ‘ (f ‘ i) := by
  rw [forcingRecodedSparseMap_decode hs hm hT hQt hTt hU hf, forcingThreadAction_value hi]

theorem forcingRecodedSparseMap_rank (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hQ : ∀ i ∈ θ, Q ‘ i ∈ hierarchy θ) {f : V} (hf : f ∈ D) :
    (forcingRecodedSparseMap θ s c m U) ‘ f ∈ hierarchy θ := by
  have hQc : ∀ i ∈ θ, (forcingCodeP c) ‘ i ∈ hierarchy θ := by
    simpa only [forcingRecodedCode, forcingCodeP_code] using hQ
  exact forcingSparseCodes_subset_hierarchy hlim hQc _
    (function_value_mem (forcingRecodedSparseMap_isomorphism hs hm hT hQt hTt hU).1 hf)

theorem forcingRecodedSparseMap_least_support {f k : V} (hf : f ∈ D)
    (hk : IsLeastOrdinal (IsThreadSupport θ (forcingCodeE s) f) k) :
    (forcingRecodedSparseMap θ s c m U) ‘ f = ⟨k, (m ‘ k) ‘ (f ‘ k)⟩ₖ := by
  have hc := forcingRecoded_code hs hm hT hQt hTt
  have hfi := forcingDirectLimit_subset _ _ _ _ _ _ hf
  have hiff (j : V) : IsThreadSupport θ (forcingCodeE c) (forcingThreadAction θ m f) j ↔
      IsThreadSupport θ (forcingCodeE s) f j := by
    simpa only [forcingRecodedCode, forcingCodeE_code] using forcingRecodedThread_support_iff hs hm (k := j) hfi
  have hk' : IsLeastOrdinal (IsThreadSupport θ (forcingCodeE c) (forcingThreadAction θ m f)) k :=
    ⟨hk.1, (hiff k).mpr hk.2.1, fun j hj hjs ↦ hk.2.2 j hj ((hiff j).mp hjs)⟩
  have ht := function_value_mem (forcingRecodedSparse_thread_isomorphism hs hm hT hQt hTt hU).1 hf
  rw [forcingThreadActionMap_value hf] at ht
  rw [forcingRecodedSparseMap_value hs hm hT hQt hTt hU hf,
    forcingSparseEncode_least_support hc hc.subset_universe ht hk', forcingThreadAction_value hk.2.1.1]

end ZFVP
