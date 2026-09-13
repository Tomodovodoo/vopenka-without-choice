import ZFVP.ModelTheory.ForcingNormalizationFamily

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingRetraction_uniform_definable :
    Language.Definable ℒₛₑₜ (fun v : Fin 5 → V ↦ IsForcingRetraction (v 0) (v 1) (v 2) (v 3) (v 4)) := by
  have h : ℒₛₑₜ-relation₅[V] (fun P R Q S π ↦
      π ∈ P ^ Q ∧ P ⊆ Q ∧ (∀ p ∈ P, π ‘ p = p) ∧
      (∀ p ∈ Q, ∀ q ∈ Q, ⟨p, q⟩ₖ ∈ S → ⟨π ‘ p, π ‘ q⟩ₖ ∈ R) ∧
      (∀ q ∈ Q, ∀ p ∈ P, ⟨q, p⟩ₖ ∈ S ↔ ⟨π ‘ q, p⟩ₖ ∈ R) ∧
      (∀ q ∈ Q, ∀ p ∈ P, ⟨p, π ‘ q⟩ₖ ∈ R → ∃ r ∈ Q, ⟨r, q⟩ₖ ∈ S ∧ π ‘ r = p)) := by definability
  apply Language.Definable.of_iff h
  intro v
  constructor
  · intro h
    exact ⟨h.maps, h.inclusion, h.fixes, h.monotone, h.below, h.lift⟩
  · rintro ⟨a, b, c, d, e, f⟩
    exact ⟨a, b, c, d, e, f⟩

private theorem forcingRetraction_comp {n : ℕ} {a b c d e : (Fin n → V) → V}
    (ha : Language.DefinableFunction ℒₛₑₜ a) (hb : Language.DefinableFunction ℒₛₑₜ b)
    (hc : Language.DefinableFunction ℒₛₑₜ c) (hd : Language.DefinableFunction ℒₛₑₜ d)
    (he : Language.DefinableFunction ℒₛₑₜ e) :
    Language.Definable ℒₛₑₜ (fun v ↦ IsForcingRetraction (a v) (b v) (c v) (d v) (e v)) :=
  Language.Definable.substitution (f := ![a, b, c, d, e]) forcingRetraction_uniform_definable
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, ha, hb, hc, hd, he])

attribute [local aesop 5 (rule_sets := [Definability]) safe] forcingRetraction_comp

instance forcingNormalizationFamily_definable : ℒₛₑₜ-relation₃[V] IsForcingNormalizationFamily := by
  have h : ℒₛₑₜ-relation₃[V] (fun θ s m ↦
      (IsFunction m ∧ domain m = θ) ∧
      (∀ i ∈ θ, IsForcingRetraction (forcingMapFixedPoints ((forcingCodeP s) ‘ i) (m ‘ i))
        (forcingOrderRestriction (forcingMapFixedPoints ((forcingCodeP s) ‘ i) (m ‘ i)) ((forcingCodeR s) ‘ i))
        ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i) (m ‘ i)) ∧
      (∀ i ∈ θ, ∀ p ∈ (forcingCodeP s) ‘ i,
        ⟨(m ‘ i) ‘ p, p⟩ₖ ∈ (forcingCodeR s) ‘ i ∧ ⟨p, (m ‘ i) ‘ p⟩ₖ ∈ (forcingCodeR s) ‘ i) ∧
      (∀ i ∈ θ, (m ‘ i) ‘ ((forcingCodet s) ‘ i) = (forcingCodet s) ‘ i) ∧
      (∀ j ∈ θ, ∀ i ∈ j, i ∈ θ → ∀ p ∈ (forcingCodeP s) ‘ j,
        ((forcingCodeπ s) ‘ ⟨i, j⟩ₖ) ‘ ((m ‘ j) ‘ p) = (m ‘ i) ‘ (((forcingCodeπ s) ‘ ⟨i, j⟩ₖ) ‘ p)) ∧
      (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ (forcingCodeP s) ‘ i,
        (m ‘ j) ‘ (((forcingCodeE s) ‘ ⟨i, j⟩ₖ) ‘ p) = ((forcingCodeE s) ‘ ⟨i, j⟩ₖ) ‘ ((m ‘ i) ‘ p))) := by
    aesop (config := { terminal := true, maxRuleApplications := 1000 }) (rule_sets := [Definability])
  apply Language.Definable.of_iff h
  intro v
  change IsForcingNormalizationFamily (v 0) (v 1) (v 2) ↔ _
  constructor
  · intro h
    exact ⟨⟨h.table.function, h.table.domain_eq⟩, h.retraction, h.equivalent, h.fixesTop, h.projection,
      h.sectionCoherent⟩
  · rintro ⟨⟨a, b⟩, c, d, e, f, g⟩
    exact ⟨⟨a, b⟩, c, d, e, f, g⟩

end ZFVP
