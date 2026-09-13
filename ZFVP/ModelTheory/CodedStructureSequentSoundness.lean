import ZFVP.ModelTheory.CodedZFModel
import ZFVP.Syntax.BinaryRelationInternalSemantics

/-! Soundness of the complete internal sequent checker in arbitrary coded
membership-language structures. The represented relation need not be ambient membership. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def codedStructureSequentHoldsFormula : SetTheorySemisentence 4 :=
  f“M n Γ b. ∃ φ ∈ Γ,
    !satisfiesFormula (!membershipLanguageCodeFormula) (!isEmpty) M (!isEmpty) n φ b”

def codedStructureSequentTrueFormula : SetTheorySemisentence 3 :=
  f“M n Γ. ∀ b ∈ !function.dfn (!structureDomainFormula M) n,
    !codedStructureSequentHoldsFormula M n Γ b”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def CodedStructureSequentHolds (M n Γ b : V) : Prop :=
  ∃ φ ∈ Γ, Satisfies membershipLanguageCode ∅ M ∅ n φ b

def CodedStructureSequentTrue (M n Γ : V) : Prop :=
  ∀ b ∈ structureDomain M ^ n, CodedStructureSequentHolds M n Γ b

instance codedStructureSequentHoldsFormula_defined :
    ℒₛₑₜ-relation₄[V] CodedStructureSequentHolds via codedStructureSequentHoldsFormula :=
  ⟨fun v ↦ by simp [codedStructureSequentHoldsFormula, CodedStructureSequentHolds]⟩

instance codedStructureSequentTrueFormula_defined :
    ℒₛₑₜ-relation₃[V] CodedStructureSequentTrue via codedStructureSequentTrueFormula :=
  ⟨fun v ↦ by simp [codedStructureSequentTrueFormula, CodedStructureSequentTrue]⟩

instance codedStructureSequentTrue_definable : ℒₛₑₜ-relation₃[V] CodedStructureSequentTrue :=
  codedStructureSequentTrueFormula_defined.to_definable

theorem codedStructureSequentHolds_insert (M n Γ φ b : V) :
    CodedStructureSequentHolds M n (insert φ Γ) b ↔
      Satisfies membershipLanguageCode ∅ M ∅ n φ b ∨ CodedStructureSequentHolds M n Γ b := by
  simp [CodedStructureSequentHolds, or_and_right, exists_or]

theorem codedStructureSequentHolds_union (M n Γ Δ b : V) :
    CodedStructureSequentHolds M n (Γ ∪ Δ) b ↔
      CodedStructureSequentHolds M n Γ b ∨ CodedStructureSequentHolds M n Δ b := by
  simp [CodedStructureSequentHolds, or_and_right, exists_or]

theorem codedStructureSequentHolds_rename {M n m r Γ b : V}
    (hM : IsStructureCode membershipLanguageCode M)
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hr : r ∈ m ^ n)
    (hΓ : Γ ⊆ formulaSet membershipLanguageCode ∅ n) (hb : b ∈ structureDomain M ^ m) :
    CodedStructureSequentHolds M m (renameCodedSequent n m r Γ) b ↔
      CodedStructureSequentHolds M n Γ (compose r b) := by
  constructor
  · rintro ⟨ψ, hψ, ht⟩
    obtain ⟨φ, hφ, rfl⟩ := (mem_renameCodedSequent_iff n m r Γ ψ).mp hψ
    exact ⟨φ, hφ, (codedMembershipSatisfies_rename hM hn hm hr (hΓ _ hφ) hb).mp ht⟩
  · rintro ⟨φ, hφ, ht⟩
    exact ⟨renameMembershipFormula n m r φ, (mem_renameCodedSequent_iff _ _ _ _ _).mpr ⟨φ, hφ, rfl⟩,
      (codedMembershipSatisfies_rename hM hn hm hr (hΓ _ hφ) hb).mpr ht⟩

theorem codedStructureSequentHolds_shift {M n Γ b x : V}
    (hM : IsStructureCode membershipLanguageCode M)
    (hn : n ∈ (ω : V)) (hΓ : Γ ⊆ formulaSet membershipLanguageCode ∅ n)
    (hb : b ∈ structureDomain M ^ n) (hx : x ∈ structureDomain M) :
    CodedStructureSequentHolds M (succ n) (shiftCodedSequent n Γ) (assignmentPrepend n b x) ↔
      CodedStructureSequentHolds M n Γ b := by
  have he := codedStructureSequentHolds_rename hM hn (ω_succ_closed hn) (successorIndices_function hn) hΓ
    (assignmentPrepend_mem_function hn hb hx)
  rw [successorIndices_compose_prepend hn hb hx] at he
  exact he

theorem codedMembershipSatisfies_instantiate {M n i φ b : V}
    (hM : IsStructureCode membershipLanguageCode M) (hn : n ∈ (ω : V)) (hi : i ∈ n)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n)) (hb : b ∈ structureDomain M ^ n) :
    Satisfies membershipLanguageCode ∅ M ∅ n (instantiateMembershipFormula n i φ) b ↔
      Satisfies membershipLanguageCode ∅ M ∅ (succ n) φ (assignmentPrepend n b (b ‘ i)) := by
  have hr := assignmentPrepend_mem_function hn (identity_mem_function n) hi
  have he := codedMembershipSatisfies_rename hM (ω_succ_closed hn) hn hr hφ hb
  rw [compose_assignmentPrepend hn (identity_mem_function n) hb hi, graph_identity_compose hb] at he
  exact he

theorem IsCodedSequentRule.coded_structure_sound {M P n Γ : V}
    (hM : IsStructureCode membershipLanguageCode M) (hn : n ∈ (ω : V))
    (hP : ∀ m Δ, ⟨m, Δ⟩ₖ ∈ P → CodedStructureSequentTrue M m Δ)
    (hr : IsCodedSequentRule ∅ P n Γ) : CodedStructureSequentTrue M n Γ := by
  classical
  rcases hr with ⟨rfl, φ, hφ, rfl⟩ | ⟨φ, hφ, rfl⟩ | rfl |
    ⟨Δ, φ, ψ, hφ, hψ, rfl, hp⟩ | ⟨Δ, φ, ψ, hφ, hψ, rfl, hp, hq⟩ |
    ⟨Δ, Ξ, φ, hφ, rfl, hp, hq⟩ | ⟨Δ, φ, hΔ, hφ, rfl, hp⟩ |
    ⟨Δ, φ, i, hi, hφ, rfl, hp⟩ | ⟨Δ, hΔ, hp⟩ | ⟨m, r, Δ, hm, hmr, hΔ, rfl, hp⟩
  · exact (not_mem_empty hφ).elim
  · intro b hb
    by_cases ht : Satisfies membershipLanguageCode ∅ M ∅ n φ b
    · exact ⟨φ, by simp, ht⟩
    · exact ⟨negateFormula membershipLanguageCode ∅ n φ, by simp,
        (satisfies_negateFormula membershipLanguageCode_valid hφ hb).mpr ht⟩
  · intro b hb
    exact ⟨truthCode, by simp, (satisfies_truth membershipLanguageCode_valid hn).mpr hb⟩
  · intro b hb
    have ht := hP _ _ hp b hb
    rw [codedStructureSequentHolds_insert, codedStructureSequentHolds_insert] at ht
    rw [codedStructureSequentHolds_insert, satisfies_or membershipLanguageCode_valid hn hφ hψ hb]
    exact or_assoc.mpr ht
  · intro b hb
    have ht := (codedStructureSequentHolds_insert _ _ _ _ _).mp (hP _ _ hp b hb)
    have hu := (codedStructureSequentHolds_insert _ _ _ _ _).mp (hP _ _ hq b hb)
    rw [codedStructureSequentHolds_insert, satisfies_and membershipLanguageCode_valid hn hφ hψ hb]
    rcases ht with ht | ht
    · exact hu.elim (fun hu ↦ Or.inl ⟨ht, hu⟩) Or.inr
    · exact Or.inr ht
  · intro b hb
    have ht := (codedStructureSequentHolds_insert _ _ _ _ _).mp (hP _ _ hp b hb)
    have hu := (codedStructureSequentHolds_insert _ _ _ _ _).mp (hP _ _ hq b hb)
    rw [satisfies_negateFormula membershipLanguageCode_valid hφ hb] at hu
    rw [codedStructureSequentHolds_union]
    rcases ht with ht | ht
    · exact Or.inr (hu.resolve_left (not_not.mpr ht))
    · exact Or.inl ht
  · intro b hb
    rw [codedStructureSequentHolds_insert]
    by_cases hΔb : CodedStructureSequentHolds M n Δ b
    · exact Or.inr hΔb
    · apply Or.inl
      rw [satisfies_all membershipLanguageCode_valid hn hφ hb]
      intro x hx
      have ht := (codedStructureSequentHolds_insert _ _ _ _ _).mp
        (hP _ _ hp _ (assignmentPrepend_mem_function hn hb hx))
      exact ht.resolve_right (fun hh ↦ hΔb ((codedStructureSequentHolds_shift hM hn hΔ hb hx).mp hh))
  · intro b hb
    have ht := (codedStructureSequentHolds_insert _ _ _ _ _).mp (hP _ _ hp b hb)
    rw [codedStructureSequentHolds_insert]
    rcases ht with ht | ht
    · apply Or.inl
      apply (satisfies_exists membershipLanguageCode_valid hn hφ hb).mpr
      exact ⟨b ‘ i, function_value_mem hb hi, (codedMembershipSatisfies_instantiate hM hn hi hφ hb).mp ht⟩
    · exact Or.inr ht
  · intro b hb
    obtain ⟨φ, hφ, ht⟩ := hP _ _ hp b hb
    exact ⟨φ, hΔ _ hφ, ht⟩
  · intro b hb
    exact (codedStructureSequentHolds_rename hM hm hn hmr hΔ hb).mpr
      (hP _ _ hp _ (compose_function hmr hb))

theorem IsOpenCodedSequentRule.coded_structure_sound {M T P n Γ : V}
    (hT : SatisfiesCodedOpenTheory membershipLanguageCode M T)
    (hn : n ∈ (ω : V)) (hP : ∀ m Δ, ⟨m, Δ⟩ₖ ∈ P → CodedStructureSequentTrue M m Δ)
    (hr : IsOpenCodedSequentRule T P n Γ) : CodedStructureSequentTrue M n Γ := by
  rcases hr with hr | ⟨φ, hφ, rfl⟩
  · exact hr.coded_structure_sound hT.1 hn hP
  · intro b hb
    exact ⟨φ, by simp, (hT.2 n φ hφ).2 b hb⟩

theorem openCodedSequentProof_lines_coded_structure_sound {M T p : V} [IsFunction p]
    (hT : SatisfiesCodedOpenTheory membershipLanguageCode M T)
    (hsteps : ∀ i ∈ domain p, ∃ m Δ, p ‘ i = ⟨m, Δ⟩ₖ ∧ IsCodedSequent m Δ ∧
      IsOpenCodedSequentRule T (range (p ↾ i)) m Δ) :
    ∀ i ∈ (ω : V), ∀ j ∈ i, j ∈ domain p → ∀ n Γ, p ‘ j = ⟨n, Γ⟩ₖ →
      CodedStructureSequentTrue M n Γ := by
  apply naturalNumber_induction
    (fun i ↦ ∀ j ∈ i, j ∈ domain p → ∀ n Γ, p ‘ j = ⟨n, Γ⟩ₖ → CodedStructureSequentTrue M n Γ)
    (by definability)
  · intro j hj
    exact False.elim (not_mem_empty hj)
  · intro i _ ih j hj hjp n Γ he
    rcases mem_succ_iff.mp hj with rfl | hj
    · obtain ⟨m, Δ, hline, hvalid, hr⟩ := hsteps j hjp
      obtain ⟨rfl, rfl⟩ := kpair_iff.mp (he.symm.trans hline)
      apply hr.coded_structure_sound hT hvalid.1
      intro m Ξ hΞ
      obtain ⟨q, hq⟩ := mem_range_iff.mp hΞ
      obtain ⟨hqp, hqi⟩ := kpair_mem_restrict_iff.mp hq
      obtain ⟨hqdom, hqval⟩ := kpair_mem_iff_value.mp hqp
      exact ih q hqi hqdom m Ξ hqval
    · exact ih j hj hjp n Γ he

theorem IsOpenCodedSequentProof.coded_structure_sound {M T p n Γ : V}
    (hp : IsOpenCodedSequentProof T p n Γ)
    (hT : SatisfiesCodedOpenTheory membershipLanguageCode M T) : CodedStructureSequentTrue M n Γ := by
  rcases hp with ⟨hfun, l, hl, hdom, hlast, hsteps⟩
  let := hfun
  exact openCodedSequentProof_lines_coded_structure_sound hT hsteps (succ l) (ω_succ_closed hl)
    l (by simp) (by rw [hdom]; simp) n Γ hlast

theorem SatisfiesCodedOpenTheory.openCodedSequentConsistent {M T : V}
    (hT : SatisfiesCodedOpenTheory membershipLanguageCode M T) : OpenCodedSequentConsistent T := by
  rintro ⟨p, hp⟩
  obtain ⟨φ, hφ, _⟩ := hp.coded_structure_sound hT ∅ (by simp [mem_function_iff, zero_def])
  exact not_mem_empty hφ

theorem IsCodedZFModel.openCodedSequentConsistent {M : V} (hM : IsCodedZFModel M) :
    OpenCodedSequentConsistent (zfOpenAxiomCodes : V) :=
  SatisfiesCodedOpenTheory.openCodedSequentConsistent hM

end ZFVP
