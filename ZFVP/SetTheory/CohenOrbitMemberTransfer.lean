import ZFVP.SetTheory.CohenFreshPermutation
import ZFVP.SetTheory.CohenMembershipProjection
import ZFVP.SetTheory.CohenConditionTransport
import ZFVP.SetTheory.CohenAmalgamation

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A transported projected membership condition forces the transported member into the
original name below the equality condition, when the member support is fresh off the overlap. -/
theorem cohen_orbitMember_transfer {E F D τ σ μ p r a t : V}
    (hτ : IsForcingName (cohenConditions (ω : V)) τ)
    (hσ : IsForcingName (cohenConditions (ω : V)) σ)
    (hμ : IsForcingName (cohenConditions (ω : V)) μ)
    (hE : IsCohenNameSupport τ E) (hF : IsCohenNameSupport σ F)
    (hD : IsCohenNameSupport μ D)
    (hp : p ∈ atomicEquality (cohenConditions (ω : V)) (cohenOrder (ω : V)) τ σ)
    (hsupp : cohenSupport p ⊆ E ∪ F)
    (hfresh : ∀ i ∈ D, i ∈ E ∪ F → i ∈ E ∩ F)
    (hrp : ⟨r, p⟩ₖ ∈ cohenOrder (ω : V))
    (hrμ : r ∈ atomicMembership (cohenConditions (ω : V)) (cohenOrder (ω : V)) μ τ)
    (ha : IsInternalPermutation (ω : V) a)
    (hafix : ∀ i ∈ E ∩ F, a ‘ i = i)
    (ht : t ∈ cohenConditions (ω : V))
    (htp : ⟨t, p⟩ₖ ∈ cohenOrder (ω : V))
    (htaq : ⟨t, cohenConditionAction (ω : V) a
      (cohenConditionRestrict r (D ∪ (E ∩ F)))⟩ₖ ∈ cohenOrder (ω : V)) :
    t ∈ atomicMembership (cohenConditions (ω : V)) (cohenOrder (ω : V))
      (nameAction (cohenPermutation (ω : V) a) μ) τ := by
  have hR := (cohen_poset (ω : V)).1
  have hpP := atomicEquality_subset _ _ _ _ p hp
  have hr := atomicMembership_subset _ _ _ _ r hrμ
  let C := E ∩ F
  let B := E ∪ F
  let q := cohenConditionRestrict r (D ∪ C)
  have hB : IsInternallyFinite B := internallyFinite_union hE.2.1 hF.2.1
  have hBω : B ⊆ (ω : V) :=
    fun i hi ↦ (mem_union_iff.mp hi).elim (hE.1 i) (hF.1 i)
  have hC : IsInternallyFinite C :=
    internallyFinite_subset hE.2.1 (fun _ hi ↦ (mem_inter_iff.mp hi).1)
  have hCω : C ⊆ (ω : V) := fun i hi ↦ hE.1 i (mem_inter_iff.mp hi).1
  have hq : q ∈ cohenConditions (ω : V) := cohenConditionRestrict_condition hr _
  obtain ⟨hpqP, hpqμ⟩ := cohen_atomicMembership_overlap_restrict hτ hσ hμ hE hF hD hp hrp hrμ
  apply atomicMembership_dense hR ht
  intro u hu hut
  have hup : ⟨u, p⟩ₖ ∈ cohenOrder (ω : V) := hR.2.2 u hu t ht p hpP hut htp
  have hpu : p ⊆ u := ((pair_mem_cohenOrder _ _ _).mp hup).2.2
  have huaq : ⟨u, cohenConditionAction (ω : V) a q⟩ₖ ∈ cohenOrder (ω : V) :=
    hR.2.2 u hu t ht _ (cohenConditionAction_condition ha hq) hut htaq
  let T := cohenSupport u ∪ B
  have hT : IsInternallyFinite T := internallyFinite_union (cohenSupport_finite hu) hB
  have hTω : T ⊆ (ω : V) :=
    fun i hi ↦ (mem_union_iff.mp hi).elim (cohenSupport_subset hu i) (hBω i)
  obtain ⟨b, hb, hbfix, hbagree, hbmove⟩ := finite_permutation_fresh_extension
    hB hBω hC hCω hD.2.1 hD.1 hT hTω hfresh ha hafix
  have hbq : cohenConditionAction (ω : V) b q = cohenConditionAction (ω : V) a q := by
    apply cohenConditionAction_eq_of_agree hq
    intro i hi
    have hiDC : i ∈ D ∪ C := by
      rw [cohenConditionRestrict_support] at hi
      exact (mem_inter_iff.mp hi).2
    rcases mem_union_iff.mp hiDC with hiD | hiC
    · exact hbagree i hiD
    · exact (hbfix i hiC).trans (hafix i hiC).symm
  have hbμ := cohenNameAction_eq_of_agree_on_support hμ hD.1 hD.2.2 hb ha hbagree
  have hcompat := cohenConditionRestrict_compatible hpP hu hb hbfix
    (fun i hi hiC hin ↦ hbmove i (hsupp i hi) hiC (mem_union_iff.mpr (Or.inl hin)))
    (fun z hz ↦ hpu z (cohenConditionRestrict_subset p C z hz))
  obtain ⟨v, hv, hvu, hvbp⟩ := hcompat
  have hvp : ⟨v, p⟩ₖ ∈ cohenOrder (ω : V) := hR.2.2 v hv u hu p hpP hvu hup
  have hvbτ := cohen_atomicEquality_amalgamation hτ hσ hE hF hp hsupp hb hbfix
    (fun i hiE hiF hin ↦ hbmove i (mem_union_iff.mpr (Or.inl hiE))
      (fun hiC ↦ hiF (mem_inter_iff.mp hiC).2)
      (mem_union_iff.mpr (Or.inr (mem_union_iff.mpr (Or.inr hin))))) hv hvp hvbp
  have hbmem := atomicMembership_nameAction_forward (cohenPermutation_automorphism hb) hμ hτ hpqμ
  rw [cohenPermutation_value hpqP] at hbmem
  have hvimage : ⟨v, cohenConditionAction (ω : V) b (p ∪ q)⟩ₖ ∈ cohenOrder (ω : V) := by
    apply (pair_mem_cohenOrder _ _ _).mpr
    refine ⟨hv, cohenConditionAction_condition hb hpqP, ?_⟩
    rw [cohenConditionAction_union, hbq]
    intro z hz
    rcases mem_union_iff.mp hz with hz | hz
    · exact ((pair_mem_cohenOrder _ _ _).mp hvbp).2.2 z hz
    · exact ((pair_mem_cohenOrder _ _ _).mp hvu).2.2 z
        (((pair_mem_cohenOrder _ _ _).mp huaq).2.2 z hz)
  have hvbmem := atomicMembership_mono hR hbmem hv hvimage
  have hvmem := (atomicEquality_membership_iff hR hvbτ
    (nameAction (cohenPermutation (ω : V) b) μ)).2.mpr hvbmem
  rw [hbμ] at hvmem
  exact ⟨v, hvmem, hvu⟩

end ZFVP
