import ZFVP.ModelTheory.SchmerlInternalCoreProofs
import ZFVP.ModelTheory.SchmerlInternalBooleanConsistency

/-! Satisfiability in an end extension rules out an old coded refutation in
the current core calculus. No omega-one preservation is needed for this
syntactic implication. Internal completeness is not assumed or proved. -/

namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem CodedSatisfiable.not_coreDerivation_neg {L H φ : V}
    (h : CodedSatisfiable L H φ) (c : V) :
    ¬IsCoreDerivationCode L {⟨(0 : V), φ⟩ₖ} 0 (negCode φ) c := by
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

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem CodedSatisfiable.not_ground_coreDerivation_neg {L H φ : V}
    (j : MembershipEndExtension V W) (h : CodedSatisfiable (j L) (j H) (j φ)) (c : V) :
    ¬IsCoreDerivationCode L {⟨(0 : V), φ⟩ₖ} 0 (negCode φ) c := by
  intro hc
  apply h.not_coreDerivation_neg (j c)
  have hs : j ({⟨(0 : V), φ⟩ₖ} : V) = {⟨(0 : W), j φ⟩ₖ} := by
    have hv (x : V) : doubleton x x = {x} := by ext; simp
    have hw (x : W) : doubleton x x = {x} := by ext; simp
    simpa only [hv, hw, j.map_kpair,
      (show j (0 : V) = (0 : W) from j.map_numeral 0)] using
      j.map_doubleton ⟨(0 : V), φ⟩ₖ ⟨(0 : V), φ⟩ₖ
  simpa only [hs, EndExtension.map_negCode,
    (show j (0 : V) = (0 : W) from j.map_numeral 0)] using
      EndExtension.coreDerivationCode_map j hc

end ZFVP.Infinitary.Internal
