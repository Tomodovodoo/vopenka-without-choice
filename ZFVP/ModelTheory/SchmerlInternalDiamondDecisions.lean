import ZFVP.ModelTheory.SchmerlInternalClosedPreservation
import ZFVP.ModelTheory.ForcingSemanticConsequence

/-! Simultaneous decisions over internal countable sets. Their construction
uses an internal enumeration and the internal omega-length dense intersection. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcing_countable_denseIntersection {P R one X D : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hDC : InternalDependentChoiceAt (ω : V)) (hclosed : IsForcingClosedAt P R (ω : V))
    (hX : IsInternallyCountable X)
    (hD : ∀ x ∈ X, ForcingDense P R (D ‘ x) ∧ IsForcingDownwardClosed P R (D ‘ x)) :
    ForcingDense P R {q ∈ P ; ∀ x ∈ X, q ∈ D ‘ x} := by
  refine ⟨sep_subset, fun p hp ↦ ?_⟩
  rcases eq_empty_or_isNonempty X with rfl | hne
  · exact ⟨p, mem_sep_iff.mpr ⟨hp, fun x hx ↦ False.elim (not_mem_empty hx)⟩, hR.2.1 p hp⟩
  obtain ⟨e, he, her⟩ := surjection_of_injection hX hne
  let : IsFunction e := IsFunction.of_mem he
  let E := definableGraph (ω : V) (fun n ↦ D ‘ (e ‘ n)) (by definability)
  have hE := forcingClosed_denseIntersection hR hDC (forcingClosedAt_through_omega hR htop hclosed)
    (D := E) (fun n hn ↦ by
      rw [show E ‘ n = D ‘ (e ‘ n) from value_definableGraph _ _ _ hn]
      exact hD (e ‘ n) (function_value_mem he hn))
  obtain ⟨q, hq, hqp⟩ := hE.2 p hp
  refine ⟨q, mem_sep_iff.mpr ⟨(mem_sep_iff.mp hq).1, ?_⟩, hqp⟩
  intro x hx
  obtain ⟨n, hnx⟩ := mem_range_iff.mp (her.symm ▸ hx)
  have hn := domain_eq_of_mem_function he ▸ mem_domain_of_kpair_mem hnx
  have hh := (mem_sep_iff.mp hq).2 n hn
  rwa [show E ‘ n = D ‘ (e ‘ n) from value_definableGraph _ _ _ hn,
    value_eq_of_kpair_mem hnx] at hh

noncomputable def checkedMembershipDecisions (P R one τ x : V) : V :=
  atomicMembership P R (checkName one x) τ ∪
    forcingNegation P R (atomicMembership P R (checkName one x) τ)

instance checkedMembershipDecisions_definable (P R one τ : V) :
    ℒₛₑₜ-function₁[V] (checkedMembershipDecisions P R one τ) := by
  unfold checkedMembershipDecisions
  definability

def DecidesMembershipOn (P R one τ q X : V) : Prop :=
  ∀ x ∈ X, q ∈ checkedMembershipDecisions P R one τ x

instance decidesMembershipOn_definable (P R one τ : V) :
    ℒₛₑₜ-relation[V] (DecidesMembershipOn P R one τ) := by
  unfold DecidesMembershipOn
  definability

theorem decidesMembershipOn_mono {P R one τ p q X : V} (hR : IsForcingPreorder P R)
    (hp : DecidesMembershipOn P R one τ p X) (hq : q ∈ P) (hqp : ⟨q, p⟩ₖ ∈ R) :
    DecidesMembershipOn P R one τ q X := by
  intro x hx
  rcases mem_union_iff.mp (hp x hx) with h | h
  · exact mem_union_iff.mpr (Or.inl (atomicMembership_mono hR h hq hqp))
  · exact mem_union_iff.mpr (Or.inr (forcingNegation_mono hR h hq hqp))

theorem decidesMembershipOn_dense {P R one τ X : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hDC : InternalDependentChoiceAt (ω : V)) (hclosed : IsForcingClosedAt P R (ω : V))
    (hX : IsInternallyCountable X) :
    ForcingDense P R {q ∈ P ; DecidesMembershipOn P R one τ q X} := by
  let D := definableGraph X (checkedMembershipDecisions P R one τ)
    (checkedMembershipDecisions_definable P R one τ)
  have hD := forcing_countable_denseIntersection hR htop hDC hclosed hX (D := D) (by
    intro x hx
    rw [show D ‘ x = checkedMembershipDecisions P R one τ x from value_definableGraph _ _ _ hx]
    refine ⟨forcing_decisions_dense hR (atomicMembership_subset _ _ _ _), ?_⟩
    intro p hp q hq hqp
    rcases mem_union_iff.mp hp with hp | hp
    · exact mem_union_iff.mpr (Or.inl (atomicMembership_mono hR hp hq hqp))
    · exact mem_union_iff.mpr (Or.inr (forcingNegation_mono hR hp hq hqp)))
  have he : {q ∈ P ; ∀ x ∈ X, q ∈ D ‘ x} = {q ∈ P ; DecidesMembershipOn P R one τ q X} := by
    apply mem_ext
    intro q
    simp only [mem_sep_iff, DecidesMembershipOn]
    apply and_congr Iff.rfl
    apply forall_congr'
    intro x
    apply imp_congr_right
    intro hx
    rw [show D ‘ x = checkedMembershipDecisions P R one τ x from value_definableGraph _ _ _ hx]
  exact he ▸ hD

theorem atomicMembership_of_all_generics [Countable V] {P R one p : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hp : p ∈ P)
    (σ τ : ForcingName P)
    (hh : ∀ G, ∀ hG : IsExternalForcingGeneric P R G, p ∈ G →
      (ForcingContext.mk P R one G hR htop hG).ofName σ ∈
        (ForcingContext.mk P R one G hR htop hG).ofName τ) :
    p ∈ atomicMembership P R σ.val τ.val := by
  apply atomicMembership_dense hR hp
  intro q hq hqp
  obtain ⟨G, hG, hqG⟩ := exists_externalForcingGeneric hR hq
  have hpG := hG.1.2.2.1 q hqG p hp hqp
  obtain ⟨r, hrG, hr⟩ := hh G hG hpG
  obtain ⟨s, hsG, hsr, hsq⟩ := hG.1.2.2.2 r hrG q hqG
  exact ⟨s, atomicMembership_mono hR hr (hG.1.1 s hsG) hsr, hsq⟩

end ZFVP.Schmerl
