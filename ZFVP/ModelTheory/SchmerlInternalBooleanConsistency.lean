import ZFVP.ModelTheory.SchmerlInternalBooleanTransport
import ZFVP.ModelTheory.SchmerlCodedSatisfiability
import ZFVP.ModelTheory.SchmerlInternalInfinitaryFragmentAgreement

/-! Coded satisfiability excludes Boolean derivations of the negation of
the given sentence, even with that sentence as a hypothesis. The model's
fragment and the derivation's fragment may differ. This is soundness only;
no internal completeness theorem is asserted. -/

namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem sentence_hypothesis_holds {L F M φ : V} (ht : Holds L F M (0 : V) φ ∅) :
    ∀ n ψ, ⟨n, ψ⟩ₖ ∈ ({⟨(0 : V), φ⟩ₖ} : V) →
      ∀ b ∈ structureDomain M ^ n, Holds L F M n ψ b := by
  intro n ψ hψ b hb
  have he : n = (0 : V) ∧ ψ = φ := by simpa using hψ
  obtain ⟨rfl, rfl⟩ := he
  have hb0 : b = ∅ := by
    have hs := subset_prod_of_mem_function hb
    change b ⊆ (∅ : V) ×ˢ structureDomain M at hs
    simpa using hs
  subst b
  exact ht

theorem CodedSatisfiable.not_booleanDerivation_neg {L H φ : V}
    (h : CodedSatisfiable L H φ) (c : V) :
    ¬IsBooleanDerivationCode L {⟨(0 : V), φ⟩ₖ} 0 (negCode φ) c := by
  rintro ⟨F, D, d, rfl, _, _, hp, hd, hl⟩
  obtain ⟨M, _, ht⟩ := h.model
  have hneg : ⟨(0 : V), negCode φ⟩ₖ ∈ F := by
    simpa only [hl] using (hp.2.2 d hd).label_mem
  have htF : Holds L F M (0 : V) φ ∅ :=
    (holds_fragment_iff hp.1 h.fragment 0 φ (hp.1.neg_mem hneg) h.sentence ∅).mpr ht
  have hn : Holds L F M (0 : V) (negCode φ) ∅ := by
    simpa only [hl, kpair.π₁_kpair, kpair.π₂_kpair] using
      hp.sound (sentence_hypothesis_holds htF) d hd ∅
        (by simpa only [hl, kpair.π₁_kpair] using holds_assignment_mem ht)
  exact (holds_neg hp.1 hneg (holds_assignment_mem ht)).mp hn htF

end ZFVP.Infinitary.Internal
