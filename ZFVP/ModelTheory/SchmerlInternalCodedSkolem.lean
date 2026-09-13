import ZFVP.ModelTheory.SchmerlInternalCodedSyntaxCountable
import ZFVP.ModelTheory.SchmerlInternalCodedTarskiVaught

/-! One internally chosen graph supplies function values and both kinds
of satisfaction witnesses for every internally finite formula and tuple. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def codedSkolemIndices (L : V) : V :=
  finiteCodingEnvelope (functionSymbols L ∪ repl kpair.π₂ (by definability) (formulaFamily L ∅))

theorem codedSkolemIndices_countable (hAC : InternalChoice V) {L : V}
    (hL : IsLanguageCode L) (hF : IsInternallyCountable (functionSymbols L))
    (hR : IsInternallyCountable (relationSymbols L)) : IsInternallyCountable (codedSkolemIndices L) :=
  finiteCodingEnvelope_countable hAC (internallyCountable_union hF
    (internallyCountable_repl _ _ (formulaFamily_countable hAC hL hF hR internallyCountable_empty)))

theorem codedSkolemIndices_function {L f : V} (hf : f ∈ functionSymbols L) :
    ⟨(0 : V), f⟩ₖ ∈ codedSkolemIndices L :=
  finiteCodingEnvelope_pair (omega_subset_finiteCodingEnvelope _ _ (by simp))
    (subset_finiteCodingEnvelope _ f (mem_union_iff.mpr (Or.inl hf)))

theorem codedSkolemIndices_formula {L n φ tag : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet L ∅ (succ n)) (htag : tag ∈ (ω : V)) :
    ⟨tag, ⟨n, φ⟩ₖ⟩ₖ ∈ codedSkolemIndices L := by
  apply finiteCodingEnvelope_pair (omega_subset_finiteCodingEnvelope _ _ htag)
  apply finiteCodingEnvelope_pair (omega_subset_finiteCodingEnvelope _ _ hn)
  apply subset_finiteCodingEnvelope
  apply mem_union_iff.mpr
  apply Or.inr
  exact (repl_spec (show ℒₛₑₜ-function₁[V] kpair.π₂ from by definability)).mpr
    ⟨⟨succ n, φ⟩ₖ, (mem_formulaSet_iff _ _ _ _).mp hφ, by simp⟩

def CodedSkolemRequest (L M i b x : V) : Prop :=
  (kpair.π₁ i = 0 ∧ x = ((structureFunctions M) ‘ (kpair.π₂ i)) ‘ b) ∨
  (kpair.π₁ i ≠ 0 ∧ kpair.π₁ i = 1 ∧
    Satisfies L ∅ M ∅ (succ (kpair.π₁ (kpair.π₂ i))) (kpair.π₂ (kpair.π₂ i))
      (assignmentPrepend (kpair.π₁ (kpair.π₂ i)) b x)) ∨
  (kpair.π₁ i ≠ 0 ∧ kpair.π₁ i ≠ 1 ∧
    ¬Satisfies L ∅ M ∅ (succ (kpair.π₁ (kpair.π₂ i))) (kpair.π₂ (kpair.π₂ i))
      (assignmentPrepend (kpair.π₁ (kpair.π₂ i)) b x))

instance codedSkolemRequest_definable (L M : V) : ℒₛₑₜ-relation₃[V] (CodedSkolemRequest L M) := by
  unfold CodedSkolemRequest Satisfies
  definability

theorem codedSkolemRequest_function (L M f b x : V) :
    CodedSkolemRequest L M ⟨(0 : V), f⟩ₖ b x ↔ x = ((structureFunctions M) ‘ f) ‘ b := by
  simp [CodedSkolemRequest]

theorem codedSkolemRequest_positive (L M n φ b x : V) :
    CodedSkolemRequest L M ⟨(1 : V), ⟨n, φ⟩ₖ⟩ₖ b x ↔
      Satisfies L ∅ M ∅ (succ n) φ (assignmentPrepend n b x) := by
  simp [CodedSkolemRequest]

theorem codedSkolemRequest_negative (L M n φ b x : V) :
    CodedSkolemRequest L M ⟨(2 : V), ⟨n, φ⟩ₖ⟩ₖ b x ↔
      ¬Satisfies L ∅ M ∅ (succ n) φ (assignmentPrepend n b x) := by
  have h20 : (2 : V) ≠ 0 := by
    intro he
    have : (2 : ℕ) = 0 := (natCast_eq_iff (V := V) 2 0).mp he
    contradiction
  have h21 : (2 : V) ≠ 1 := by
    intro he
    have : (2 : ℕ) = 1 := (natCast_eq_iff (V := V) 2 1).mp he
    contradiction
  simp [CodedSkolemRequest, h20, h21]

noncomputable def codedSkolemCandidates (L M z : V) : V :=
  {x ∈ structureDomain M ;
    (∃ y ∈ structureDomain M, CodedSkolemRequest L M (kpair.π₁ z) (kpair.π₂ z) y) →
      CodedSkolemRequest L M (kpair.π₁ z) (kpair.π₂ z) x}

instance codedSkolemCandidates_definable (L M : V) : ℒₛₑₜ-function₁[V] (codedSkolemCandidates L M) := by
  have h : ℒₛₑₜ-relation[V] (fun X z ↦ ∀ x, x ∈ X ↔ x ∈ structureDomain M ∧
      ((∃ y ∈ structureDomain M, CodedSkolemRequest L M (kpair.π₁ z) (kpair.π₂ z) y) →
        CodedSkolemRequest L M (kpair.π₁ z) (kpair.π₂ z) x)) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [codedSkolemCandidates, mem_sep_iff]
  rfl

theorem exists_codedSkolemOperator (hAC : InternalChoice V) {L M : V} (hM : IsStructureCode L M) :
    ∃ g, IsFunction g ∧ domain g = codedSkolemIndices L ×ˢ finiteSequences (structureDomain M) ∧
      ∀ i ∈ codedSkolemIndices L, ∀ b ∈ finiteSequences (structureDomain M),
        g ‘ ⟨i, b⟩ₖ ∈ structureDomain M ∧
        ((∃ x ∈ structureDomain M, CodedSkolemRequest L M i b x) →
          CodedSkolemRequest L M i b (g ‘ ⟨i, b⟩ₖ)) := by
  have hne (z : V) : IsNonempty (codedSkolemCandidates L M z) := by
    by_cases hex : ∃ y ∈ structureDomain M, CodedSkolemRequest L M (kpair.π₁ z) (kpair.π₂ z) y
    · obtain ⟨x, hx, hreq⟩ := hex
      exact ⟨x, mem_sep_iff.mpr ⟨hx, fun _ ↦ hreq⟩⟩
    · obtain ⟨x, hx⟩ := hM.domain_nonempty.nonempty
      exact ⟨x, mem_sep_iff.mpr ⟨hx, fun h ↦ False.elim (hex h)⟩⟩
  obtain ⟨g, hg, hd, hv⟩ := choice_for_definable_family hAC
    (codedSkolemIndices L ×ˢ finiteSequences (structureDomain M))
    (codedSkolemCandidates L M) inferInstance (fun z _ ↦ hne z)
  refine ⟨g, hg, hd, ?_⟩
  intro i hi b hb
  have h := mem_sep_iff.mp (hv ⟨i, b⟩ₖ (kpair_mem_iff.mpr ⟨hi, hb⟩))
  simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using h

end ZFVP.Schmerl
