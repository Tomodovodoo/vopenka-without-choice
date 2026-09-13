import ZFVP.ModelTheory.ForcingQuotientNames
import ZFVP.SetTheory.ForcingUnionName

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingUnion {P : V} (R : V) (τ : ForcingName P) : ForcingName P :=
  ⟨forcingUnionName P R τ.val, forcingUnionName_isName τ.property⟩

theorem forcingQuotient_unionName (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (τ : ForcingName P)
    (x : ForcingQuotient P R G hR hG.1) :
    x ∈ forcingQuotientMk P R G hR hG.1 (forcingUnion R τ) ↔
      ∃ y : ForcingQuotient P R G hR hG.1,
        y ∈ forcingQuotientMk P R G hR hG.1 τ ∧ x ∈ y := by
  unfold IsExternalForcingGeneric at hG
  obtain ⟨ξ, rfl⟩ := forcingQuotientMk_surjective P R G hR hG.1 x
  constructor
  · intro hm
    obtain ⟨ν, q, hqG, hνq, he⟩ := (forcingQuotientMk_mem_subname_iff P R G hR hG _ _).mp hm
    obtain ⟨_, σ, s, t, hσ, hν, hqs, hqt⟩ := (mem_forcingUnionName_iff P R τ.val ν.val q).mp hνq
    let σ' : ForcingName P := ⟨σ, forcingName_subname τ.property hσ⟩
    have hsG := hG.1.2.2.1 q hqG s (forcingOrder_right_mem hR hqs) hqs
    have htG := hG.1.2.2.1 q hqG t (forcingOrder_right_mem hR hqt) hqt
    refine ⟨forcingQuotientMk P R G hR hG.1 σ', ?_, ?_⟩
    · exact (forcingQuotientMk_mem_subname_iff P R G hR hG _ _).mpr ⟨σ', s, hsG, hσ, rfl⟩
    · exact (forcingQuotientMk_mem_subname_iff P R G hR hG _ _).mpr ⟨ν, t, htG, hν, he⟩
  · rintro ⟨y, hy, hx⟩
    obtain ⟨η, rfl⟩ := forcingQuotientMk_surjective P R G hR hG.1 y
    obtain ⟨σ, s, hsG, hσ, heσ⟩ := (forcingQuotientMk_mem_subname_iff P R G hR hG _ _).mp hy
    rw [heσ] at hx
    obtain ⟨ν, t, htG, hν, heν⟩ := (forcingQuotientMk_mem_subname_iff P R G hR hG _ _).mp hx
    obtain ⟨q, hqG, hqs, hqt⟩ := hG.1.2.2.2 s hsG t htG
    apply (forcingQuotientMk_mem_subname_iff P R G hR hG _ _).mpr
    exact ⟨ν, q, hqG, (mem_forcingUnionName_iff _ _ _ _ _).mpr
      ⟨hG.1.1 q hqG, σ.val, s, t, hσ, hν, hqs, hqt⟩, heν⟩

theorem forcingQuotient_union (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (a : ForcingQuotient P R G hR hG.1) :
    ∃ b : ForcingQuotient P R G hR hG.1, ∀ x, x ∈ b ↔ ∃ y, y ∈ a ∧ x ∈ y := by
  unfold IsExternalForcingGeneric at hG
  obtain ⟨τ, rfl⟩ := forcingQuotientMk_surjective P R G hR hG.1 a
  exact ⟨forcingQuotientMk P R G hR hG.1 (forcingUnion R τ),
    forcingQuotient_unionName P R G hR hG τ⟩

end ZFVP
