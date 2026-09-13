import ZFVP.ModelTheory.CoherentAutomorphismRecursion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem coherentAutomorphismRow_of_successor {Δ k c H f : V} [IsOrdinal Δ] [IsOrdinal k]
    (hc : IsForcingIterationCode Δ c) (hk : succ k ∈ Δ)
    (hm : IsCoherentForcingAutomorphismFamily (succ k) c H)
    (hf : IsForcingAutomorphism ((forcingCodeP c) ‘ (succ k)) ((forcingCodeR c) ‘ (succ k)) f)
    (ht : f ‘ ((forcingCodet c) ‘ (succ k)) = (forcingCodet c) ‘ (succ k))
    (hp : ∀ p ∈ (forcingCodeP c) ‘ (succ k),
      ((forcingCodeπ c) ‘ ⟨k,succ k⟩ₖ) ‘ (f ‘ p) =
        (H ‘ k) ‘ (((forcingCodeπ c) ‘ ⟨k,succ k⟩ₖ) ‘ p))
    (hs : ∀ p ∈ (forcingCodeP c) ‘ k,
      f ‘ (((forcingCodeE c) ‘ ⟨k,succ k⟩ₖ) ‘ p) =
        ((forcingCodeE c) ‘ ⟨k,succ k⟩ₖ) ‘ ((H ‘ k) ‘ p)) :
    IsCoherentAutomorphismRow (succ k) c H f := by
  have hkΔ := IsOrdinal.toIsTransitive.mem_trans (mem_succ_self k) hk
  have hiΔ : ∀ i ∈ succ k, i ∈ Δ := fun i hi ↦ IsOrdinal.toIsTransitive.mem_trans hi hk
  have hik : ∀ i ∈ succ k, i ⊆ k := by
    intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact subset_refl _
    · exact IsOrdinal.toIsTransitive.transitive _ hi
  refine ⟨hf, ht, ?_, ?_⟩
  · intro i hi p hpmem
    have hb := hc.system.split.projMaps k hkΔ (succ k) hk (mem_subset_refl k) p hpmem
    rw [← hc.system.split.projComp i (hiΔ i hi) k hkΔ (succ k) hk (hik i hi) (mem_subset_refl k)
      _ (function_value_mem hf.1 hpmem), hp p hpmem,
      hm.proj i hi k (mem_succ_self k) (hik i hi) _ hb,
      hc.system.split.projComp i (hiΔ i hi) k hkΔ (succ k) hk (hik i hi) (mem_subset_refl k) p hpmem]
  · intro i hi p hpmem
    have hb := hc.system.split.secMaps i (hiΔ i hi) k hkΔ (hik i hi) p hpmem
    rw [← hc.system.split.secComp i (hiΔ i hi) k hkΔ (succ k) hk (hik i hi) (mem_subset_refl k) p hpmem,
      hs _ hb, hm.sec i hi k (mem_succ_self k) (hik i hi) p hpmem,
      hc.system.split.secComp i (hiΔ i hi) k hkΔ (succ k) hk (hik i hi) (mem_subset_refl k)
        _ (function_value_mem (hm.iso i hi).1 hpmem)]

theorem coherentWitnessProjection_of_successor {Δ k c W w : V} [IsOrdinal Δ] [IsOrdinal k]
    (hc : IsForcingIterationCode Δ c) (hk : succ k ∈ Δ)
    (hw : w ∈ (forcingCodeP c) ‘ (succ k))
    (hproj : ∀ i ∈ succ k, ∀ j ∈ succ k, i ⊆ j →
      ((forcingCodeπ c) ‘ ⟨i,j⟩ₖ) ‘ (W ‘ j) = W ‘ i)
    (hp : ((forcingCodeπ c) ‘ ⟨k,succ k⟩ₖ) ‘ w = W ‘ k) :
    ∀ i ∈ succ k, ((forcingCodeπ c) ‘ ⟨i,succ k⟩ₖ) ‘ w = W ‘ i := by
  intro i hi
  have hkΔ := IsOrdinal.toIsTransitive.mem_trans (mem_succ_self k) hk
  have hiΔ := IsOrdinal.toIsTransitive.mem_trans hi hk
  have hik : i ⊆ k := by
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact subset_refl _
    · exact IsOrdinal.toIsTransitive.transitive _ hi
  rw [← hc.system.split.projComp i hiΔ k hkΔ (succ k) hk hik (mem_subset_refl k) w hw,
    hp, hproj i hi k (mem_succ_self k) hik]

end ZFVP
