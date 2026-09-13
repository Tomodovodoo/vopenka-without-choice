import ZFVP.ModelTheory.ForcingQuotientNames
import ZFVP.SetTheory.ForcingImageName

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingImage {P : V} (R : V) (τ : ForcingName P) (B : V)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) : ForcingName P :=
  ⟨forcingImageName P R τ.val B F hF, forcingImageName_isName P R τ.val B F hF⟩

theorem forcingQuotient_definableImage (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (τ : ForcingName P)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂ F)
    (hd : ∀ σ ν, IsForcingName P σ → IsForcingName P ν → IsForcingDownwardClosed P R (F σ ν))
    (Q : ForcingQuotient P R G hR hG.1 → ForcingQuotient P R G hR hG.1 → Prop)
    (htruth : ∀ σ ν : ForcingName P, GenericMeets G (F σ.val ν.val) ↔
      Q (forcingQuotientMk P R G hR hG.1 σ) (forcingQuotientMk P R G hR hG.1 ν))
    (huniq : ∀ a, a ∈ forcingQuotientMk P R G hR hG.1 τ → ∀ b c, Q a b → Q a c → b = c) :
    ∃ b : ForcingQuotient P R G hR hG.1, ∀ x, x ∈ b ↔
      ∃ a, a ∈ forcingQuotientMk P R G hR hG.1 τ ∧ Q a x := by
  unfold IsExternalForcingGeneric at hG
  obtain ⟨B, hB⟩ := forcingImageWitnessBound P τ.val F hF
  refine ⟨forcingQuotientMk P R G hR hG.1 (forcingImage R τ B F hF), ?_⟩
  intro x
  obtain ⟨ξ, rfl⟩ := forcingQuotientMk_surjective P R G hR hG.1 x
  constructor
  · intro hx
    obtain ⟨ν, p, hpG, hp, he⟩ := (forcingQuotientMk_mem_subname_iff P R G hR hG _ _).mp hx
    obtain ⟨_, _, _, σ, s, hσs, hps, hpF⟩ := (mem_forcingImageName_iff P R τ.val B F hF _ _).mp hp
    let σ' : ForcingName P := ⟨σ, forcingName_subname τ.property hσs⟩
    have hsG := hG.1.2.2.1 p hpG s (forcingOrder_right_mem hR hps) hps
    refine ⟨forcingQuotientMk P R G hR hG.1 σ',
      (forcingQuotientMk_mem_subname_iff P R G hR hG _ _).mpr ⟨σ', s, hsG, hσs, rfl⟩, ?_⟩
    rw [he]
    exact (htruth σ' ν).mp ⟨p, hpG, hpF⟩
  · rintro ⟨a, ha, hQ⟩
    obtain ⟨η, rfl⟩ := forcingQuotientMk_surjective P R G hR hG.1 a
    obtain ⟨σ, s, hsG, hσs, heσ⟩ := (forcingQuotientMk_mem_subname_iff P R G hR hG _ _).mp ha
    rw [heσ] at hQ ha
    obtain ⟨p, hpG, hpF⟩ := (htruth σ ξ).mpr hQ
    obtain ⟨q, hqG, hqs, hqp⟩ := hG.1.2.2.2 s hsG p hpG
    have hqF := hd σ.val ξ.val σ.property ξ.property p hpF q (hG.1.1 q hqG) hqp
    obtain ⟨ν, hνB, hνN, hνF⟩ := hB σ.val (mem_domain_of_kpair_mem hσs) q (hG.1.1 q hqG)
      ⟨ξ.val, ξ.property, hqF⟩
    let ν' : ForcingName P := ⟨ν, hνN⟩
    have heν : forcingQuotientMk P R G hR hG.1 ξ = forcingQuotientMk P R G hR hG.1 ν' :=
      huniq _ ha _ _ hQ ((htruth σ ν').mp ⟨q, hqG, hνF⟩)
    exact (forcingQuotientMk_mem_subname_iff P R G hR hG _ _).mpr
      ⟨ν', q, hqG, (mem_forcingImageName_iff P R τ.val B F hF _ _).mpr
        ⟨hνB, hG.1.1 q hqG, hνN, σ.val, s, hσs, hqs, hνF⟩, heν⟩

end ZFVP
