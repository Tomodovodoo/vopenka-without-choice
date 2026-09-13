import ZFVP.ModelTheory.TwoStepReconstruction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Conditions whose two coordinates belong to the successive filters. -/
def twoStepCombinedFilter (A : ForcingContext V) (Q t : V) (H : Set A.Model) : Set V :=
  {a | ∃ p : V, ∃ τ : ForcingName A.P, a = ⟨p, τ.val⟩ₖ ∧
    a ∈ twoStepConditions A.P A.R Q t ∧ p ∈ A.G ∧ A.ofName τ ∈ H}

theorem kpair_mem_twoStepCombinedFilter (A : ForcingContext V) (Q t p : V)
    (τ : ForcingName A.P) (H : Set A.Model) :
    ⟨p, τ.val⟩ₖ ∈ twoStepCombinedFilter A Q t H ↔
      ⟨p, τ.val⟩ₖ ∈ twoStepConditions A.P A.R Q t ∧ p ∈ A.G ∧ A.ofName τ ∈ H := by
  constructor
  · rintro ⟨q, σ, he, hc, hq, hσ⟩
    have heq := kpair_iff.mp he
    have hτσ : τ = σ := Subtype.ext heq.2
    exact ⟨hc, heq.1.symm ▸ hq, hτσ.symm ▸ hσ⟩
  · rintro ⟨hc, hp, hτ⟩
    exact ⟨p, τ, rfl, hc, hp, hτ⟩

namespace TwoStepModel
variable (A : ForcingContext V) {Q S t : V} (h : IsForcingIterand A.P A.R Q S t)
include h

theorem realize_common_lower {p q : V} (τ σ : ForcingName A.P)
    (hpC : ⟨p, τ.val⟩ₖ ∈ twoStepConditions A.P A.R Q t)
    (hqC : ⟨q, σ.val⟩ₖ ∈ twoStepConditions A.P A.R Q t)
    (hp : p ∈ A.G) (hq : q ∈ A.G) {x : A.Model}
    (hx : x ∈ A.ofName ⟨Q, h.posetName⟩)
    (hxτ : ⟨x, A.ofName τ⟩ₖ ∈ A.ofName ⟨S, h.orderName⟩)
    (hxσ : ⟨x, A.ofName σ⟩ₖ ∈ A.ofName ⟨S, h.orderName⟩) :
    ∃ r : V, ∃ ν : ForcingName A.P,
      ⟨r, ν.val⟩ₖ ∈ twoStepConditions A.P A.R Q t ∧ r ∈ A.G ∧ A.ofName ν = x ∧
      ⟨⟨r, ν.val⟩ₖ, ⟨p, τ.val⟩ₖ⟩ₖ ∈ twoStepOrder A.P A.R Q S t ∧
      ⟨⟨r, ν.val⟩ₖ, ⟨q, σ.val⟩ₖ⟩ₖ ∈ twoStepOrder A.P A.R Q S t := by
  obtain ⟨ν, s, hs, hνs, rfl⟩ := (A.mem_ofName_iff ⟨Q, h.posetName⟩ x).mp hx
  have heτ : boundedPairMemberFormula.Evalb (fun i ↦ A.ofName (![⟨S, h.orderName⟩, ν, τ] i)) :=
    (Defined.eval_iff _).mpr hxτ
  have heσ : boundedPairMemberFormula.Evalb (fun i ↦ A.ofName (![⟨S, h.orderName⟩, ν, σ] i)) :=
    (Defined.eval_iff _).mpr hxσ
  obtain ⟨u, hu, huτ⟩ := (A.formula_truth boundedPairMemberFormula ![⟨S, h.orderName⟩, ν, τ]).mp heτ
  obtain ⟨v, hv, hvσ⟩ := (A.formula_truth boundedPairMemberFormula ![⟨S, h.orderName⟩, ν, σ]).mp heσ
  change u ∈ forcingFormula A.P A.R boundedPairMemberFormula (standardTuple ![S, ν.val, τ.val]) at huτ
  change v ∈ forcingFormula A.P A.R boundedPairMemberFormula (standardTuple ![S, ν.val, σ.val]) at hvσ
  obtain ⟨a, ha, hap, haq⟩ := A.generic.1.2.2.2 p hp q hq
  obtain ⟨b, hb, hba, hbs⟩ := A.generic.1.2.2.2 a ha s hs
  obtain ⟨c, hc, hcb, hcu⟩ := A.generic.1.2.2.2 b hb u hu
  obtain ⟨r, hr, hrc, hrv⟩ := A.generic.1.2.2.2 c hc v hv
  have hrP := A.generic.1.1 r hr
  have hrb := A.order.2.2 r hrP c (A.generic.1.1 c hc) b (A.generic.1.1 b hb) hrc hcb
  have hra := A.order.2.2 r hrP b (A.generic.1.1 b hb) a (A.generic.1.1 a ha) hrb hba
  have hrs := A.order.2.2 r hrP b (A.generic.1.1 b hb) s (A.generic.1.1 s hs) hrb hbs
  have hru := A.order.2.2 r hrP c (A.generic.1.1 c hc) u (A.generic.1.1 u hu) hrc hcu
  have hrQ := atomicMembership_mono A.order (atomicMembership_of_pair A.order (A.generic.1.1 s hs) hνs) hrP hrs
  have hνN : ν.val ∈ twoStepNames Q t := mem_union_iff.mpr (Or.inl (mem_domain_of_kpair_mem hνs))
  have hrC : ⟨r, ν.val⟩ₖ ∈ twoStepConditions A.P A.R Q t :=
    (kpair_mem_twoStepConditions _ _ _ _ _ _).mpr ⟨hrP, hνN, hrQ⟩
  refine ⟨r, ν, hrC, hr, rfl, ?_, ?_⟩
  · apply (kpair_mem_twoStepOrder _ _ _ _ _ _ _).mpr
    refine ⟨hrC, hpC, ?_, ?_⟩
    · simpa using A.order.2.2 r hrP a (A.generic.1.1 a ha) p (A.generic.1.1 p hp) hra hap
    · simpa using (forcingFormula_regular A.order boundedPairMemberFormula _).2.1 u huτ r hrP hru
  · apply (kpair_mem_twoStepOrder _ _ _ _ _ _ _).mpr
    refine ⟨hrC, hqC, ?_, ?_⟩
    · simpa using A.order.2.2 r hrP a (A.generic.1.1 a ha) q (A.generic.1.1 q hq) hra haq
    · simpa using (forcingFormula_regular A.order boundedPairMemberFormula _).2.1 v hvσ r hrP hrv


theorem combined_filter {H : Set A.Model}
    (hH : IsExternalForcingFilter (A.ofName ⟨Q, h.posetName⟩) (A.ofName ⟨S, h.orderName⟩) H) :
    IsExternalForcingFilter (twoStepConditions A.P A.R Q t) (twoStepOrder A.P A.R Q S t)
      (twoStepCombinedFilter A Q t H) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro a ⟨p, τ, he, hc, hp, hτ⟩
    exact hc
  · have htH := externalForcingFilter_top hH (top A h)
    exact ⟨⟨A.one, t⟩ₖ, A.one, ⟨t, h.topName⟩, rfl,
      twoStep_section_mem A.order A.top h A.top.1,
      externalForcingFilter_top A.generic.1 A.top, htH⟩
  · rintro a ⟨p, τ, rfl, hc, hp, hτ⟩ b hb hab
    obtain ⟨q, hq, σ, hσ, rfl, hqσ⟩ := (mem_twoStepConditions _ _ _ _ _).mp hb
    let ν : ForcingName A.P := ⟨σ, h.name hσ⟩
    have hpq := ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp hab).2.2.1
    simp only [kpair.π₁_kpair] at hpq
    have hqG := A.generic.1.2.2.1 p hp q hq hpq
    have hνQ := A.ofName_mem_of_forcedMember ν ⟨Q, h.posetName⟩ hqG hqσ
    have hτν := ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp hab).2.2.2
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hτν
    refine ⟨q, ν, rfl, hb, hqG, ?_⟩
    exact hH.2.2.1 _ hτ _ hνQ (A.ofName_pair_mem_of_forced ⟨S, h.orderName⟩ τ ν hp hτν)
  · rintro a ⟨p, τ, rfl, hpC, hp, hτ⟩ b ⟨q, σ, rfl, hqC, hq, hσ⟩
    obtain ⟨x, hx, hxτ, hxσ⟩ := hH.2.2.2 _ hτ _ hσ
    obtain ⟨r, ν, hrC, hr, hν, hrp, hrq⟩ := realize_common_lower A h τ σ hpC hqC hp hq
      (hH.1 x hx) hxτ hxσ
    exact ⟨⟨r, ν.val⟩ₖ, ⟨r, ν, rfl, hrC, hr, hν.symm ▸ hx⟩, hrp, hrq⟩

end TwoStepModel
end ZFVP
