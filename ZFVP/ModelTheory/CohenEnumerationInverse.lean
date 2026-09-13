import ZFVP.ModelTheory.CohenInfiniteSet

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace CohenModel

variable {I : V} {G : Set V} (hG : IsExternalForcingGeneric (cohenConditions I) (cohenOrder I) G)

theorem enumeration_value {i : V} (hi : i ∈ I) :
    (enumeration hG) ‘ ((cohenContext I G hG).toForcingContext.check i) =
      (cohenContext I G hG).toOrdinary (real hG i hi) := by
  have : IsFunction (enumeration hG) := IsFunction.of_mem (enumeration_function hG)
  exact value_eq_of_kpair_mem ((mem_enumeration_iff hG _).mpr ⟨i, hi, rfl⟩)

theorem enumeration_range : range (enumeration hG) = (cohenContext I G hG).toOrdinary (reals hG) := by
  let S := cohenContext I G hG
  apply SetTheory.subset_antisymm (range_subset_of_mem_function (enumeration_function hG))
  intro x hx
  obtain ⟨y, hy, rfl⟩ := S.inclusion.endExtension (reals hG) x hx
  obtain ⟨i, hi, rfl⟩ := (mem_reals_iff hG y).mp hy
  exact mem_range_iff.mpr ⟨S.toForcingContext.check i, (mem_enumeration_iff hG _).mpr ⟨i, hi, rfl⟩⟩

theorem enumeration_inverse_function : converseGraph (enumeration hG) ∈
    (cohenContext I G hG).toForcingContext.check I ^ (cohenContext I G hG).toOrdinary (reals hG) := by
  simpa only [enumeration_range hG] using converseGraph_mem_function (enumeration_function hG) (enumeration_injective hG)

theorem enumeration_inverse_value {i : V} (hi : i ∈ I) :
    (converseGraph (enumeration hG)) ‘ ((cohenContext I G hG).toOrdinary (real hG i hi)) =
      (cohenContext I G hG).toForcingContext.check i := by
  rw [← enumeration_value hG hi]
  exact converseGraph_value_value (enumeration_function hG) (enumeration_injective hG)
    (((cohenContext I G hG).toForcingContext.check_mem_iff i I).mpr hi)

/-- An injection into the Cohen reals cannot use only a finite ground set of indices. -/
theorem no_injection_with_finite_indices {E : V} (hEf : IsInternallyFinite E)
    {f : (cohenContext I G hG).Model}
    (hf : f ∈ reals hG ^ (ω : (cohenContext I G hG).Model)) (hfi : Injective f)
    (hs : ∀ n ∈ (ω : V), ∃ i : V, ∃ hi : i ∈ I,
      i ∈ E ∧ f ‘ ((cohenContext I G hG).check n) = real hG i hi) : False := by
  let S := cohenContext I G hG
  let O := S.toForcingContext
  have : IsFunction f := IsFunction.of_mem hf
  have hf' : S.toOrdinary f ∈ S.toOrdinary (reals hG) ^ (ω : O.Model) := by
    have hh := (S.inclusion.function_iff f ω (reals hG)).mpr hf
    rwa [S.inclusion.map_omega] at hh
  have hfi' : Injective (S.toOrdinary f) := (S.inclusion.injective_iff f).mpr hfi
  let g := compose (S.toOrdinary f) (converseGraph (enumeration hG))
  have hg : g ∈ O.check I ^ (ω : O.Model) := compose_function hf' (enumeration_inverse_function hG)
  have : IsFunction (enumeration hG) := IsFunction.of_mem (enumeration_function hG)
  have hgi : Injective g := compose_injective hfi' (converseGraph_injective _)
  have hrange : range g ⊆ O.check E := by
    intro y hy
    obtain ⟨x, hxy⟩ := mem_range_iff.mp hy
    have hx : x ∈ (ω : O.Model) := (mem_of_mem_functions hg hxy).1
    have hx' : x ∈ O.check (ω : V) := by
      change x ∈ O.checkEmbedding (ω : V)
      rwa [O.checkEmbedding.map_omega]
    obtain ⟨n, hn, rfl⟩ := (O.mem_check_iff ω x).mp hx'
    obtain ⟨i, hi, hiE, hval⟩ := hs n hn
    have hnc : S.check n ∈ domain f := by
      rw [domain_eq_of_mem_function hf, ← S.checkEmbedding.map_omega]
      exact (S.check_mem_iff n ω).mpr hn
    have hv : (S.toOrdinary f) ‘ (O.check n) = S.toOrdinary (real hG i hi) := by
      exact (S.inclusion.map_value f (S.check n) hnc).symm.trans (congrArg S.toOrdinary hval)
    have he : g ‘ (O.check n) = O.check i := by
      rw [show g = compose (S.toOrdinary f) (converseGraph (enumeration hG)) from rfl,
        value_compose_of_mem_function hf' (enumeration_inverse_function hG)
          (show O.check n ∈ (ω : O.Model) from by rw [← O.checkEmbedding.map_omega]; exact (O.check_mem_iff n ω).mpr hn),
        hv, enumeration_inverse_value hG hi]
    have : IsFunction g := IsFunction.of_mem hg
    have hye : y = O.check i := (value_eq_of_kpair_mem hxy).symm.trans he
    rw [hye]
    exact (O.check_mem_iff i E).mpr hiE
  have hgE : g ∈ O.check E ^ (ω : O.Model) :=
    mem_function_of_mem_function_of_subset (mem_function_range_of_mem_function hg) hrange
  have hE' : IsInternallyFinite (O.check E) := O.checkEmbedding.map_internallyFinite hEf
  exact omega_internallyInfinite (internallyFinite_of_cardLE hE' ⟨g, hgE, hgi⟩)

end CohenModel
end ZFVP
