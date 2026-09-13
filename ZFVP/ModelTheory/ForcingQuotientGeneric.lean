import ZFVP.ModelTheory.ForcingQuotientZF
import ZFVP.SetTheory.GenericName

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingGenericSet (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingFilter P R G) (one : V) (hone : IsForcingTop P R one) :
    ForcingQuotient P R G hR hG :=
  forcingQuotientMk P R G hR hG ⟨genericName P one, genericName_isName hone.1⟩

theorem forcingGenericSet_mem_iff (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (one : V) (hone : IsForcingTop P R one)
    (x : ForcingQuotient P R G hR hG.1) :
    x ∈ forcingGenericSet P R G hR hG.1 one hone ↔
      ∃ p ∈ G, x = forcingCheck P R G hR hG.1 one hone p := by
  unfold IsExternalForcingGeneric at hG
  obtain ⟨σ, rfl⟩ := forcingQuotientMk_surjective P R G hR hG.1 x
  constructor
  · intro hx
    obtain ⟨ν, s, hsG, hνs, he⟩ := (forcingQuotientMk_mem_subname_iff P R G hR hG _ _).mp hx
    obtain ⟨p, _, hpair⟩ := (mem_genericName_iff _ _ _).mp hνs
    obtain ⟨hν, hs⟩ := kpair_iff.mp hpair
    subst s
    have hν' : ν = (⟨checkName one p, checkName_isName hone.1 p⟩ : ForcingName P) := Subtype.ext hν
    exact ⟨p, hsG, he.trans (congrArg (forcingQuotientMk P R G hR hG.1) hν')⟩
  · rintro ⟨p, hpG, he⟩
    exact (forcingQuotientMk_mem_subname_iff P R G hR hG _ _).mpr
      ⟨⟨checkName one p, checkName_isName hone.1 p⟩, p, hpG,
        (mem_genericName_iff _ _ _).mpr ⟨p, hG.1.1 p hpG, rfl⟩, he⟩

theorem forcingCheck_mem_genericSet_iff (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (one : V) (hone : IsForcingTop P R one) (p : V) :
    forcingCheck P R G hR hG.1 one hone p ∈ forcingGenericSet P R G hR hG.1 one hone ↔ p ∈ G := by
  rw [forcingGenericSet_mem_iff P R G hR hG]
  constructor
  · rintro ⟨q, hqG, he⟩
    exact (forcingCheck_eq_iff P R G hR hG.1 one hone p q).mp he ▸ hqG
  · intro hpG
    exact ⟨p, hpG, rfl⟩

theorem forcingGenericSet_subset_check (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (one : V) (hone : IsForcingTop P R one) :
    ∀ x : ForcingQuotient P R G hR hG.1, x ∈ forcingGenericSet P R G hR hG.1 one hone →
      x ∈ forcingCheck P R G hR hG.1 one hone P := by
  unfold IsExternalForcingGeneric at hG
  intro x hx
  obtain ⟨p, hpG, rfl⟩ := (forcingGenericSet_mem_iff P R G hR hG one hone x).mp hx
  exact (forcingCheck_mem_iff P R G hR hG.1 one hone p P).mpr (hG.1.1 p hpG)

theorem exists_forcingQuotient_zf [Countable V] {P R p one : V}
    (hR : IsForcingPreorder P R) (hone : IsForcingTop P R one) (hp : p ∈ P) :
    ∃ G : Set V, ∃ hG : IsExternalForcingGeneric P R G,
      p ∈ G ∧ (ForcingQuotient P R G hR hG.1)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  obtain ⟨G, hG, hpG⟩ := exists_externalForcingGeneric hR hp
  exact ⟨G, hG, hpG, forcingQuotient_models_zf P R G hR hG one hone⟩

end ZFVP
