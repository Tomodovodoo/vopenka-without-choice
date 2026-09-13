import ZFVP.SetTheory.RealTranslationPerfect
import ZFVP.SetTheory.CountableUnions
import ZFVP.SetTheory.InjectionRetraction

/-! Cantor PSP transfers to every actual internal real set under internal DC. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem allRealPerfectSetProperty_of_cantor (hDC : InternalDependentChoice V)
    (hPSP : AllPerfectSetProperty V) :
    ∀ A : V, A ⊆ dedekindReals V → RealPerfectSetProperty A := by
  intro A hA
  obtain ⟨e, he, her⟩ := surjection_of_injection (internalRationals_countable (V := V))
    (show IsNonempty (internalRationals V) from ⟨rationalZero V, rationalZero_mem⟩)
  have : IsFunction e := IsFunction.of_mem he
  let F : V → V := fun n ↦ A ∩ realTranslateImage (e ‘ n) (unitReals V)
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  let f := definableGraph (ω : V) F hF
  have : IsFunction f := definableGraph_isFunction _ _ _
  have hval : ∀ n ∈ (ω : V), f ‘ n = F n := fun n hn ↦ value_definableGraph _ _ _ hn
  by_cases hcount : ∀ n ∈ (ω : V), IsInternallyCountable (f ‘ n)
  · apply Or.inl
    apply (cardLE_of_subset (show A ⊆ ⋃ˢ range f from ?_)).trans
      (countable_union_of_dependentChoice hDC (domain_definableGraph _ _ _) hcount)
    intro x hx
    obtain ⟨a, ha, hxa⟩ := real_mem_translated_unit ((mem_dedekindReals_iff _).mp (hA x hx))
    have har : a ∈ range e := by rwa [her]
    obtain ⟨n, hna⟩ := mem_range_iff.mp har
    have hn : n ∈ (ω : V) := domain_eq_of_mem_function he ▸ mem_domain_of_kpair_mem hna
    refine mem_sUnion_iff.mpr ⟨f ‘ n, ?_, ?_⟩
    · exact mem_range_of_kpair_mem ((pair_mem_definableGraph_iff _ _ _ n (f ‘ n)).mpr ⟨hn, hval n hn⟩)
    · rw [hval n hn]
      exact mem_inter_iff.mpr ⟨hx, by simpa only [value_eq_of_kpair_mem hna] using hxa⟩
  · have hex : ∃ n ∈ (ω : V), ¬ IsInternallyCountable (f ‘ n) := by
      simpa only [not_forall, exists_prop] using hcount
    obtain ⟨n, hn, hnc⟩ := hex
    have hp : RealPerfectSetProperty (f ‘ n) := by
      rw [hval n hn]
      exact translated_unit_perfectSetProperty hPSP ⟨e ‘ n, function_value_mem he hn⟩
        (fun _ hx ↦ (mem_inter_iff.mp hx).2)
    rcases hp with hc | ⟨P, hP, hPf⟩
    · exact (hnc hc).elim
    · refine Or.inr ⟨P, hP, fun x hx ↦ ?_⟩
      have hxf := hPf x hx
      rw [hval n hn] at hxf
      exact (mem_inter_iff.mp hxf).1

end ZFVP
