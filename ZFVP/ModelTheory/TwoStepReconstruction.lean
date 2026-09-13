import ZFVP.ModelTheory.TwoStepContexts

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TwoStepModel
variable (A : ForcingContext V) {Q S t : V} (h : IsForcingIterand A.P A.R Q S t) {G : Set V}
  (hG : IsExternalForcingGeneric (twoStepConditions A.P A.R Q t) (twoStepOrder A.P A.R Q S t) G)
  (hA : A.G = forcingProjectionGeneric A.P A.R (twoStepProjection A.P A.R Q t) G)
include h hG hA

theorem section_mem {p : V} (hp : p ∈ A.G) : ⟨p, t⟩ₖ ∈ G := by
  apply (twoStep_projected_generic_iff_section A.order A.top h hG.1).mp
  rw [← hA]
  exact hp

theorem mem_of_first_second {p : V} {τ : ForcingName A.P}
    (hc : ⟨p, τ.val⟩ₖ ∈ twoStepConditions A.P A.R Q t)
    (hp : p ∈ A.G)
    (hτ : A.ofName τ ∈ twoStepSecondFilter A ⟨Q, h.posetName⟩ ⟨S, h.orderName⟩ G) :
    ⟨p, τ.val⟩ₖ ∈ G := by
  obtain ⟨q, σ, hqG, hστ⟩ := hτ.2
  have he : boundedPairMemberFormula.Evalb (fun i ↦ A.ofName (![⟨S, h.orderName⟩, σ, τ] i)) :=
    (Defined.eval_iff _).mpr hστ
  obtain ⟨r, hrG, hr⟩ := (A.formula_truth boundedPairMemberFormula ![⟨S, h.orderName⟩, σ, τ]).mp he
  obtain ⟨a, haG, haq, hap⟩ := hG.1.2.2.2 _ hqG _ (section_mem A h hG hA hp)
  obtain ⟨b, hbG, hba, hbr⟩ := hG.1.2.2.2 _ haG _ (section_mem A h hG hA hrG)
  have ho := twoStep_preorder A.order A.top h
  have hbC := hG.1.1 b hbG
  have hbq := ho.2.2 b hbC a (hG.1.1 a haG) _ (hG.1.1 _ hqG) hba haq
  have hbp := ho.2.2 b hbC a (hG.1.1 a haG) _
    (hG.1.1 _ (section_mem A h hG hA hp)) hba hap
  obtain ⟨u, hu, ν, hν, rfl, hm⟩ := (mem_twoStepConditions _ _ _ _ _).mp hbC
  have hup := (twoStep_below_section A.order A.top h hbC (A.generic.1.1 p hp)).mp hbp
  have hur := (twoStep_below_section A.order A.top h hbC (A.generic.1.1 r hrG)).mp hbr
  simp only [kpair.π₁_kpair] at hup hur
  have huστ := (forcingFormula_regular A.order boundedPairMemberFormula _).2.1 r hr u hu hur
  have huνσ := ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp hbq).2.2.2
  simp only [kpair.π₁_kpair, kpair.π₂_kpair] at huνσ
  have huντ := forcedPreorder_trans A.order A.top hu ⟨Q, h.posetName⟩ ⟨S, h.orderName⟩
    ⟨ν, h.name hν⟩ σ τ (h.preorder u hu) huνσ huστ
  apply hG.1.2.2.1 _ hbG _ hc
  apply (kpair_mem_twoStepOrder _ _ _ _ _ _ _).mpr
  exact ⟨hbC, hc, by simpa using hup, by simpa using huντ⟩

theorem mem_iff_first_second {p : V} {τ : ForcingName A.P}
    (hc : ⟨p, τ.val⟩ₖ ∈ twoStepConditions A.P A.R Q t) :
    ⟨p, τ.val⟩ₖ ∈ G ↔ p ∈ A.G ∧
      A.ofName τ ∈ twoStepSecondFilter A ⟨Q, h.posetName⟩ ⟨S, h.orderName⟩ G :=
  ⟨fun hg ↦ ⟨first_mem A h hG hA (τ := τ) hg, value_in_second A h hG hA (τ := τ) hg⟩,
    fun hg ↦ mem_of_first_second A h hG hA hc hg.1 hg.2⟩

end TwoStepModel
end ZFVP
