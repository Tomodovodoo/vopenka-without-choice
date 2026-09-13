import ZFVP.SetTheory.ForcingNameOrdinalBound
import ZFVP.ModelTheory.ForcingModel

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingName_ordinal_bound_all_generics {δ P R one : V}
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (τ : ForcingName P) :
    ∃ β ∈ δ, ∀ G : Set V, ∀ hG : IsExternalForcingGeneric P R G,
      let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
      A.ofName τ ∈ A.check δ → A.ofName τ ∈ A.check β := by
  obtain ⟨β, hβ, hb⟩ := forcingName_checkedOrdinals_bounded hδ hP hR ht τ.val
  refine ⟨β, hβ, ?_⟩
  intro G hG
  let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
  change A.ofName τ ∈ A.check δ → A.ofName τ ∈ A.check β
  intro hτ
  obtain ⟨y, hy, he⟩ := (A.mem_check_iff δ (A.ofName τ)).mp hτ
  let cy : ForcingName P := ⟨checkName one y, checkName_isName ht.1 y⟩
  have he' : A.ofName τ = A.ofName cy := he
  obtain ⟨p, hpG, hp⟩ := (forcingQuotientMk_eq_iff P R G hR hG.1 τ cy).mp he'
  have hyβ := hb p (hG.1.1 p hpG) y hy hp
  exact he ▸ (A.check_mem_iff y β).mpr hyβ

end ZFVP
