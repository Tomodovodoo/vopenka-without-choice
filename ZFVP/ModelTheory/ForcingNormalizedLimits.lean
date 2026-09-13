import ZFVP.ModelTheory.ForcingNormalizedSystem
import ZFVP.ModelTheory.ForcingNormalizationLimits

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {θ s m U : V} [IsOrdinal θ]
  (h : IsForcingNormalizationFamily θ s m) (hs : IsForcingIterationCode θ s)
local notation "N" => forcingNormalizationCarriers θ s m
local notation "π" => forcingNormalizationProjections θ s m
local notation "E" => forcingNormalizationSections θ s m

include h hs

theorem forcingNormalized_inverseLimit_eq :
    forcingInverseLimit θ N π U = forcingInverseLimit θ N (forcingCodeπ s) U := by
  apply mem_ext
  intro f
  simp only [mem_forcingInverseLimit_iff]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro hv
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hij
  apply forall_congr'
  intro hi
  let := IsOrdinal.of_mem hj
  rw [forcingNormalizationProjections_apply h hs hi hj (IsOrdinal.toIsTransitive.transitive _ hij) (hv j hj)]

omit [IsOrdinal θ] in
theorem forcingNormalized_support_iff {f k : V}
    (hv : ∀ i ∈ θ, f ‘ i ∈ N ‘ i) :
    IsThreadSupport θ E f k ↔ IsThreadSupport θ (forcingCodeE s) f k := by
  unfold IsThreadSupport
  apply and_congr_right
  intro hk
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  apply forall_congr'
  intro hkj
  rw [forcingNormalizationSections_apply h hs hk hj hkj (hv k hk)]

theorem forcingNormalized_directLimit_eq :
    forcingDirectLimit θ N π E U = forcingDirectLimit θ N (forcingCodeπ s) (forcingCodeE s) U := by
  apply mem_ext
  intro f
  simp only [mem_forcingDirectLimit_iff, forcingNormalized_inverseLimit_eq h hs]
  apply and_congr_right
  intro hf
  apply exists_congr
  intro k
  exact forcingNormalized_support_iff h hs ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).2.1

theorem forcingNormalized_direct_fixedPoints :
    forcingMapFixedPoints ((forcingCodeP (forcingDirectCode θ s)) ‘ θ)
      (forcingNormalizationDirectMap θ s m) =
    forcingDirectLimit θ N π E (forcingCodeUniverse s) := by
  rw [forcingNormalized_directLimit_eq h hs]
  exact (forcingNormalizationDirect_retraction hs h).fixedPoints_eq

theorem forcingNormalized_inverse_fixedPoints :
    forcingMapFixedPoints ((forcingCodeP (forcingInverseCode θ s)) ‘ θ)
      (forcingNormalizationInverseMap θ s m) =
    forcingInverseLimit θ N π (forcingCodeUniverse s) := by
  rw [forcingNormalized_inverseLimit_eq h hs]
  exact (forcingNormalizationInverse_retraction hs h).fixedPoints_eq

end ZFVP
