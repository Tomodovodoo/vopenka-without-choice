import ZFVP.ModelTheory.CodedSequentSoundness

/-! Internally finite proofs with open theory axioms, valid at every assignment. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def SatisfiesOpenCodes (U T : V) : Prop :=
  IsNonempty U ∧ ∀ n φ, ⟨n, φ⟩ₖ ∈ T → IsMembershipFormulaCode n φ ∧
    ∀ b ∈ U ^ n, MembershipSatisfies U n φ b

instance satisfiesOpenCodes_definable : ℒₛₑₜ-relation[V] SatisfiesOpenCodes := by
  unfold SatisfiesOpenCodes
  definability

def IsOpenCodedSequentRule (T P n Γ : V) : Prop :=
  IsCodedSequentRule ∅ P n Γ ∨ ∃ φ, ⟨n, φ⟩ₖ ∈ T ∧ Γ = {φ}

instance isOpenCodedSequentRule_definable : ℒₛₑₜ-relation₄[V] IsOpenCodedSequentRule := by
  unfold IsOpenCodedSequentRule
  definability

theorem IsOpenCodedSequentRule.sound {U T P n Γ : V} (hT : SatisfiesOpenCodes U T)
    (hn : n ∈ (ω : V)) (hP : ∀ m Δ, ⟨m, Δ⟩ₖ ∈ P → CodedSequentTrue U m Δ)
    (hr : IsOpenCodedSequentRule T P n Γ) : CodedSequentTrue U n Γ := by
  rcases hr with hr | ⟨φ, hφ, rfl⟩
  · exact hr.sound ⟨hT.1, fun ψ hψ ↦ False.elim (not_mem_empty hψ)⟩ hn hP
  · intro b hb
    exact ⟨φ, by simp, (hT.2 n φ hφ).2 b hb⟩

def IsOpenCodedSequentProof (T p n Γ : V) : Prop :=
  IsFunction p ∧ ∃ l ∈ (ω : V), domain p = succ l ∧ p ‘ l = ⟨n, Γ⟩ₖ ∧
    ∀ i ∈ domain p, ∃ m Δ, p ‘ i = ⟨m, Δ⟩ₖ ∧ IsCodedSequent m Δ ∧
      IsOpenCodedSequentRule T (range (p ↾ i)) m Δ

instance isOpenCodedSequentProof_definable : ℒₛₑₜ-relation₄[V] IsOpenCodedSequentProof := by
  unfold IsOpenCodedSequentProof
  definability

def OpenCodedSequentConsistent (T : V) : Prop := ¬∃ p, IsOpenCodedSequentProof T p 0 ∅

instance openCodedSequentConsistent_definable : ℒₛₑₜ-predicate[V] OpenCodedSequentConsistent := by
  unfold OpenCodedSequentConsistent
  definability

theorem openCodedSequentProof_lines_sound {U T p : V} [IsFunction p]
    (hT : SatisfiesOpenCodes U T)
    (hsteps : ∀ i ∈ domain p, ∃ m Δ, p ‘ i = ⟨m, Δ⟩ₖ ∧ IsCodedSequent m Δ ∧
      IsOpenCodedSequentRule T (range (p ↾ i)) m Δ) :
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

theorem IsOpenCodedSequentProof.sound {U T p n Γ : V} (hp : IsOpenCodedSequentProof T p n Γ)
    (hT : SatisfiesOpenCodes U T) : CodedSequentTrue U n Γ := by
  rcases hp with ⟨hfun, l, hl, hdom, hlast, hsteps⟩
  let := hfun
  exact openCodedSequentProof_lines_sound hT hsteps (succ l) (ω_succ_closed hl) l (by simp)
    (by rw [hdom]; simp) n Γ hlast

theorem SatisfiesOpenCodes.openCodedSequentConsistent {U T : V} (hT : SatisfiesOpenCodes U T) :
    OpenCodedSequentConsistent T := by
  rintro ⟨p, hp⟩
  exact not_codedSequentTrue_empty U (hp.sound hT)

end ZFVP
