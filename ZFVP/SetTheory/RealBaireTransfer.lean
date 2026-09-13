import ZFVP.SetTheory.RealUnitCover
import ZFVP.SetTheory.RealCategoryUnions

/-! Cantor BP implies BP for every actual internal real set under internal DC. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem allRealBaireProperty_of_cantor (hDC : InternalDependentChoice V)
    (hBP : AllBaireProperty V) : ∀ A : V, A ⊆ dedekindReals V → RealBaireProperty A := by
  intro A hA
  obtain ⟨e, he, her⟩ := surjection_of_injection (internalRationals_countable (V := V))
    (show IsNonempty (internalRationals V) from ⟨rationalZero V, rationalZero_mem⟩)
  have : IsFunction e := IsFunction.of_mem he
  let F : V → V := fun n ↦ A ∩ realTranslateImage (e ‘ n) (unitReals V)
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  let f := definableGraph (ω : V) F hF
  have hf : ∀ n ∈ (ω : V), RealBaireProperty (f ‘ n) := by
    intro n hn
    rw [value_definableGraph _ _ _ hn]
    exact translated_unit_baireProperty hBP ⟨e ‘ n, function_value_mem he hn⟩
      (fun _ hx ↦ (mem_inter_iff.mp hx).2)
  have hUnion : realSequenceUnion f = A := by
    apply mem_ext
    intro x
    constructor
    · intro hx
      obtain ⟨_, n, hn, hxn⟩ := (mem_realSequenceUnion_iff _ _).mp hx
      rw [value_definableGraph _ _ _ hn] at hxn
      exact (mem_inter_iff.mp hxn).1
    · intro hx
      have hxcut := (mem_dedekindReals_iff _).mp (hA x hx)
      obtain ⟨a, ha, hxa⟩ := real_mem_translated_unit hxcut
      have har : a ∈ range e := by rwa [her]
      obtain ⟨n, hna⟩ := mem_range_iff.mp har
      have hn : n ∈ (ω : V) := domain_eq_of_mem_function he ▸ mem_domain_of_kpair_mem hna
      refine (mem_realSequenceUnion_iff _ _).mpr ⟨hxcut, n, hn, ?_⟩
      rw [value_definableGraph _ _ _ hn]
      exact mem_inter_iff.mpr ⟨hx, by simpa only [value_eq_of_kpair_mem hna] using hxa⟩
  rw [← hUnion]
  exact realSequenceUnion_baireProperty (countableChoice_of_dependentChoice hDC) hf

end ZFVP
