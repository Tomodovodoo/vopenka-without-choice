import ZFVP.ModelTheory.ForcingNormalizedLimits

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {θ s m U : V} [IsOrdinal θ]
variable (hn : IsForcingNormalizationFamily θ s m) (hs : IsForcingIterationCode θ s)
local notation "N" => forcingNormalizationCarriers θ s m
local notation "π" => forcingNormalizationProjections θ s m
local notation "C" => forcingInverseLimit θ N π U
local notation "D" => forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) U

include hn hs in
theorem forcingNormalized_inverse_threadOrder :
    forcingOrderRestriction C (forcingThreadOrder θ (forcingCodeR s) D) =
      forcingThreadOrder θ (forcingNormalizationOrders θ s m) C := by
  have hC : C ⊆ D := by
    rw [forcingNormalized_inverseLimit_eq hn hs]
    exact forcingInverseLimit_mono_coordinates hn.inclusion
  have hv (f : V) (hf : f ∈ C) : ∀ i ∈ θ, f ‘ i ∈ N ‘ i :=
    ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).2.1
  apply mem_ext
  intro z
  simp only [forcingOrderRestriction, forcingThreadOrder, mem_sep_iff]
  apply and_congr_right
  intro hz
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hz
  simp only [kpair_mem_iff, hC a ha, hC b hb, true_and, kpair.π₁_kpair, kpair.π₂_kpair]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  rw [forcingNormalizationOrders_value hi, pair_mem_forcingOrderRestriction]
  simp only [hv a ha i hi, hv b hb i hi, true_and]

end ZFVP
