import ZFVP.Syntax.FixedZFAxiomCodes
import ZFVP.Syntax.TailTemplateDefinability

/-! The complete internal ZF axiom set, indexed by each formula's parameter context. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance separationCode_definable : ℒₛₑₜ-function₂[V] separationCode :=
  MembershipTemplate.compileTail_definable separationTemplate

instance replacementCode_definable : ℒₛₑₜ-function₂[V] replacementCode :=
  MembershipTemplate.compileTail_definable replacementTemplate

def IsZFOpenAxiom (n ψ : V) : Prop :=
  (n = 0 ∧ ψ ∈ (fixedZFSentenceCodes : V)) ∨
  (n ∈ (ω : V) ∧ ∃ φ, IsMembershipFormulaCode (succ n) φ ∧ ψ = separationCode n φ) ∨
  (n ∈ (ω : V) ∧ ∃ φ, IsMembershipFormulaCode (succ (succ n)) φ ∧ ψ = replacementCode n φ)

private theorem axiomSelector_definable (S : V) (F G : V → V → V)
    [ℒₛₑₜ-function₂[V] F] [ℒₛₑₜ-function₂[V] G] :
    ℒₛₑₜ-relation[V] (fun n ψ ↦ (n = 0 ∧ ψ ∈ S) ∨
      (n ∈ (ω : V) ∧ ∃ φ, IsMembershipFormulaCode (succ n) φ ∧ ψ = F n φ) ∨
      (n ∈ (ω : V) ∧ ∃ φ, IsMembershipFormulaCode (succ (succ n)) φ ∧ ψ = G n φ)) := by
  definability

instance isZFOpenAxiom_definable : ℒₛₑₜ-relation[V] IsZFOpenAxiom :=
  axiomSelector_definable fixedZFSentenceCodes separationCode replacementCode

theorem IsZFOpenAxiom.valid {n ψ : V} (hψ : IsZFOpenAxiom n ψ) : IsMembershipFormulaCode n ψ := by
  rcases hψ with ⟨rfl, hψ⟩ | ⟨hn, φ, hφ, rfl⟩ | ⟨hn, φ, hφ, rfl⟩
  · exact fixedZFSentenceCodes_valid hψ
  · exact separationCode_valid hn hφ
  · exact replacementCode_valid hn hφ

noncomputable def zfOpenAxiomCodes : V :=
  {p ∈ formulaFamily membershipLanguageCode ∅ ; ∃ n ψ, p = ⟨n, ψ⟩ₖ ∧ IsZFOpenAxiom n ψ}

theorem mem_zfOpenAxiomCodes_iff (n ψ : V) : ⟨n, ψ⟩ₖ ∈ (zfOpenAxiomCodes : V) ↔ IsZFOpenAxiom n ψ := by
  unfold zfOpenAxiomCodes
  rw [mem_sep_iff]
  constructor
  · rintro ⟨_, m, χ, he, hχ⟩
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    exact hχ
  · intro hψ
    exact ⟨hψ.valid, n, ψ, rfl, hψ⟩

theorem SatisfiesSentenceCodes.all_assignments {U T ψ : V} (hT : SatisfiesSentenceCodes U T)
    (hψ : ψ ∈ T) {b : V} (hb : b ∈ U ^ (0 : V)) : MembershipSatisfies U 0 ψ b := by
  obtain ⟨χ, hχ, hh⟩ := codedSequentTrue_theory hT hψ b hb
  have he : χ = ψ := by simpa using hχ
  subst χ
  exact hh

theorem IsInternalZFModel.satisfies_open_codes {U : V} (hU : IsInternalZFModel U) :
    SatisfiesOpenCodes U zfOpenAxiomCodes := by
  refine ⟨hU.1.1, fun n ψ hψ ↦ ?_⟩
  have hax := (mem_zfOpenAxiomCodes_iff n ψ).mp hψ
  refine ⟨hax.valid, fun b hb ↦ ?_⟩
  rcases hax with ⟨rfl, hfixed⟩ | ⟨hn, φ, hφ, rfl⟩ | ⟨hn, φ, hφ, rfl⟩
  · exact hU.1.satisfies_codes.all_assignments hfixed hb
  · exact hU.2.1.satisfies_code hU.1.1 hn hφ hb
  · exact hU.2.2.satisfies_code hU.1.1 hn hφ hb

theorem satisfiesOpenCodes_zf_iff (U : V) : SatisfiesOpenCodes U zfOpenAxiomCodes ↔ IsInternalZFModel U := by
  constructor
  · intro hU
    refine ⟨(internalFixedZFAxioms_iff_satisfies_codes U).mpr ⟨hU.1, ?_⟩,
      (internalSeparation_iff_satisfies_codes hU.1).mpr ?_,
      (internalReplacement_iff_satisfies_codes hU.1).mpr ?_⟩
    · intro ψ hψ
      have h := hU.2 0 ψ ((mem_zfOpenAxiomCodes_iff 0 ψ).mpr (Or.inl ⟨rfl, hψ⟩))
      exact ⟨h.1, h.2 ∅ (by simp [mem_function_iff, zero_def])⟩
    · intro n hn φ hφ b hb
      exact (hU.2 n (separationCode n φ) ((mem_zfOpenAxiomCodes_iff _ _).mpr
        (Or.inr (Or.inl ⟨hn, φ, hφ, rfl⟩)))).2 b hb
    · intro n hn φ hφ b hb
      exact (hU.2 n (replacementCode n φ) ((mem_zfOpenAxiomCodes_iff _ _).mpr
        (Or.inr (Or.inr ⟨hn, φ, hφ, rfl⟩)))).2 b hb
  · exact IsInternalZFModel.satisfies_open_codes

theorem IsInternalZFModel.openCodedSequentConsistent {U : V} (hU : IsInternalZFModel U) :
    OpenCodedSequentConsistent (zfOpenAxiomCodes : V) := hU.satisfies_open_codes.openCodedSequentConsistent

end ZFVP
