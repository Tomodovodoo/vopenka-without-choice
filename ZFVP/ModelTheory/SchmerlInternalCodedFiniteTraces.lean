import ZFVP.ModelTheory.SchmerlInternalCodedBinaryUnion
import ZFVP.ModelTheory.SchmerlUniformCodedSource

/-! Frozen finite traces remain internally countable in the actual coded
chain union. All predicates use the represented membership relation. -/
namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsCodedFiniteEndExtension (M N : V) : Prop :=
  ∀ a ∈ structureDomain M, codedUnary M (encodeMembershipFormula internallyFiniteFormula) a →
    ∀ x ∈ structureDomain N, codedMember N x a → x ∈ structureDomain M

def isCodedFiniteEndExtensionFormula : SetTheorySemisentence 2 :=
  f“M N. ∀ a ∈ !structureDomainFormula M,
    !codedUnaryFormula M (!(encodeMembershipFormulaFormula internallyFiniteFormula)) a →
      ∀ x ∈ !structureDomainFormula N, !codedMemberFormula N x a → x ∈ !structureDomainFormula M”

instance isCodedFiniteEndExtensionFormula_defined :
    ℒₛₑₜ-relation[V] IsCodedFiniteEndExtension via isCodedFiniteEndExtensionFormula :=
  ⟨fun v ↦ by simp [isCodedFiniteEndExtensionFormula, IsCodedFiniteEndExtension]⟩

namespace IsInternalRelationalChain
variable {θ C : V} (h : IsInternalRelationalChain membershipLanguageCode θ C)
include h

theorem codedUnary_union_iff {i a φ : V} (hi : i ∈ θ) (ha : a ∈ structureDomain (C ‘ i))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (1 : V)) :
    codedUnary (C ‘ i) φ a ↔ codedUnary (codedChainUnion membershipLanguageCode θ C) φ a := by
  unfold codedUnary codedSatisfies
  exact h.satisfies_union_iff hi (by simp) hφ
    (standardTuple_mem_function ![a] (by intro k; fin_cases k; exact ha))

theorem codedMember_union_iff {i x a : V} (hi : i ∈ θ)
    (hx : x ∈ structureDomain (C ‘ i)) (ha : a ∈ structureDomain (C ‘ i)) :
    codedMember (C ‘ i) x a ↔ codedMember (codedChainUnion membershipLanguageCode θ C) x a := by
  unfold codedMember codedBinary codedSatisfies
  apply h.satisfies_union_iff hi (by simp)
  · exact encodeMembershipFormula_mem _
  · exact standardTuple_mem_function ![x, a] (by intro k; fin_cases k; exact hx; exact ha)

theorem finite_trace_subset_stage
    (hfreeze : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → IsCodedFiniteEndExtension (C ‘ i) (C ‘ j))
    {i a : V} (hi : i ∈ θ) (ha : a ∈ structureDomain (C ‘ i))
    (hf : codedUnary (codedChainUnion membershipLanguageCode θ C)
      (encodeMembershipFormula internallyFiniteFormula) a) :
    codedMemberTrace (codedChainUnion membershipLanguageCode θ C) a ⊆ structureDomain (C ‘ i) := by
  have hfi : codedUnary (C ‘ i) (encodeMembershipFormula internallyFiniteFormula) a :=
    (h.codedUnary_union_iff hi ha
      (encodeMembershipFormula_mem _)).mpr hf
  intro x hx
  obtain ⟨hx, hxa⟩ := (mem_codedMemberTrace _ _ _).mp hx
  rw [structureDomain_codedChainUnion] at hx
  obtain ⟨j, hj, hxj⟩ := (mem_codedChainCarrier _ _ _).mp hx
  obtain ⟨k, hk, hik, hjk⟩ := h.common hi hj
  have hak := h.increasing i hi k hk hik a ha
  have hxk := h.increasing j hj k hk hjk x hxj
  exact hfreeze i hi k hk hik a ha hfi x hxk ((h.codedMember_union_iff hk hxk hak).mpr hxa)

theorem union_finSmall
    (hcount : ∀ i ∈ θ, IsInternallyCountable (structureDomain (C ‘ i)))
    (hfreeze : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → IsCodedFiniteEndExtension (C ‘ i) (C ‘ j)) :
    IsCodedFinSmall (codedChainUnion membershipLanguageCode θ C) := by
  intro a ha hf
  rw [structureDomain_codedChainUnion] at ha
  obtain ⟨i, hi, hai⟩ := (mem_codedChainCarrier _ _ _).mp ha
  exact internallyCountable_subset (hcount i hi) (h.finite_trace_subset_stage hfreeze hi hai hf)

theorem union_codedZF {i : V} (hi : i ∈ θ) (hZF : IsCodedZFModel (C ‘ i)) :
    IsCodedZFModel (codedChainUnion membershipLanguageCode θ C) :=
  ((h.stage_elementary hi).satisfiesCodedOpenTheory_iff).mp hZF

end IsInternalRelationalChain

theorem codedChainCarrier_cardLE (hAC : InternalChoice V) {θ C κ : V} [IsOrdinal κ]
    (hωκ : (ω : V) ⊆ κ) (hθ : θ ≤# κ)
    (hstage : ∀ i ∈ θ, IsInternallyCountable (structureDomain (C ‘ i))) :
    codedChainCarrier θ C ≤# κ := by
  let D := definableGraph θ (fun i ↦ structureDomain (C ‘ i)) (by definability)
  have hc : ∀ i ∈ θ, D ‘ i ≤# (ω : V) := by
    intro i hi
    rw [show D ‘ i = structureDomain (C ‘ i) from value_definableGraph _ _ _ hi]
    exact hstage i hi
  have hu := sUnion_range_cardLE_prod hAC (domain_definableGraph θ _ _) hc
  have hp : θ ×ˢ (ω : V) ≤# κ := by
    apply (prod_cardLE_prod hθ (cardLE_of_subset hωκ)).trans
    have he : κ ∪ (ω : V) = κ := by
      apply mem_ext
      intro x
      simp only [mem_union_iff]
      exact ⟨fun hx ↦ hx.elim id (hωκ x), Or.inl⟩
    have hh := ordinal_prod_cardLE_union_omega κ
    rwa [he] at hh
  have hh := hu.trans hp
  simpa only [D, range_definableGraph, codedChainCarrier] using hh

end ZFVP.Schmerl


