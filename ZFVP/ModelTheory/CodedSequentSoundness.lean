import ZFVP.ModelTheory.CodedSequentRules

/-! Soundness by induction through the entire internal natural-number domain of a proof. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsCodedSequentProof (T p n Γ : V) : Prop :=
  IsFunction p ∧ ∃ l ∈ (ω : V), domain p = succ l ∧ p ‘ l = ⟨n, Γ⟩ₖ ∧
    ∀ i ∈ domain p, ∃ m Δ, p ‘ i = ⟨m, Δ⟩ₖ ∧ IsCodedSequent m Δ ∧
      IsCodedSequentRule T (range (p ↾ i)) m Δ

instance isCodedSequentProof_definable : ℒₛₑₜ-relation₄[V] IsCodedSequentProof := by
  unfold IsCodedSequentProof
  definability

def CodedSequentConsistent (T : V) : Prop := ¬∃ p, IsCodedSequentProof T p 0 ∅

instance codedSequentConsistent_definable : ℒₛₑₜ-predicate[V] CodedSequentConsistent := by
  unfold CodedSequentConsistent
  definability

theorem codedSequentProof_lines_sound {U T p : V} [IsFunction p]
    (hT : SatisfiesSentenceCodes U T)
    (hsteps : ∀ i ∈ domain p, ∃ m Δ, p ‘ i = ⟨m, Δ⟩ₖ ∧ IsCodedSequent m Δ ∧
      IsCodedSequentRule T (range (p ↾ i)) m Δ) :
    ∀ i ∈ (ω : V), ∀ j ∈ i, j ∈ domain p → ∀ n Γ, p ‘ j = ⟨n, Γ⟩ₖ → CodedSequentTrue U n Γ := by
  apply naturalNumber_induction
    (fun i ↦ ∀ j ∈ i, j ∈ domain p → ∀ n Γ, p ‘ j = ⟨n, Γ⟩ₖ → CodedSequentTrue U n Γ)
    (by definability)
  · intro j hj
    exact False.elim (not_mem_empty hj)
  · intro i _ ih j hj hjp n Γ he
    rcases mem_succ_iff.mp hj with rfl | hj
    · obtain ⟨m, Δ, hline, hvalid, hr⟩ := hsteps j hjp
      obtain ⟨rfl, rfl⟩ := kpair_iff.mp (he.symm.trans hline)
      apply hr.sound hT hvalid.1
      intro m Ξ hΞ
      obtain ⟨q, hq⟩ := mem_range_iff.mp hΞ
      obtain ⟨hqp, hqi⟩ := kpair_mem_restrict_iff.mp hq
      obtain ⟨hqdom, hqval⟩ := kpair_mem_iff_value.mp hqp
      exact ih q hqi hqdom m Ξ hqval
    · exact ih j hj hjp n Γ he

theorem IsCodedSequentProof.sound {U T p n Γ : V} (hp : IsCodedSequentProof T p n Γ)
    (hT : SatisfiesSentenceCodes U T) : CodedSequentTrue U n Γ := by
  rcases hp with ⟨hfun, l, hl, hdom, hlast, hsteps⟩
  let := hfun
  exact codedSequentProof_lines_sound hT hsteps (succ l) (ω_succ_closed hl) l (by simp)
    (by rw [hdom]; simp) n Γ hlast

theorem SatisfiesSentenceCodes.codedSequentConsistent {U T : V} (hT : SatisfiesSentenceCodes U T) :
    CodedSequentConsistent T := by
  rintro ⟨p, hp⟩
  exact not_codedSequentTrue_empty U (hp.sound hT)

end ZFVP
