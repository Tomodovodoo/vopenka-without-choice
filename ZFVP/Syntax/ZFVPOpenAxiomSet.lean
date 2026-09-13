import ZFVP.Syntax.ZFOpenAxiomSet

/-! The internal ZF+VP axiom set and its exact coded model condition. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsZFVPOpenAxiom (n ψ : V) : Prop := IsZFOpenAxiom n ψ ∨ n = 0 ∧ ψ ∈ (vopenkaAxiomCodes : V)

instance isZFVPOpenAxiom_definable : ℒₛₑₜ-relation[V] IsZFVPOpenAxiom := by
  unfold IsZFVPOpenAxiom
  definability

theorem IsZFVPOpenAxiom.valid {n ψ : V} (hψ : IsZFVPOpenAxiom n ψ) : IsMembershipFormulaCode n ψ := by
  rcases hψ with hψ | ⟨rfl, hψ⟩
  · exact hψ.valid
  · exact vopenkaAxiomCodes_sentence hψ

noncomputable def zfVPOpenAxiomCodes : V :=
  {p ∈ formulaFamily membershipLanguageCode ∅ ; ∃ n ψ, p = ⟨n, ψ⟩ₖ ∧ IsZFVPOpenAxiom n ψ}

theorem mem_zfVPOpenAxiomCodes_iff (n ψ : V) : ⟨n, ψ⟩ₖ ∈ (zfVPOpenAxiomCodes : V) ↔ IsZFVPOpenAxiom n ψ := by
  unfold zfVPOpenAxiomCodes
  rw [mem_sep_iff]
  constructor
  · rintro ⟨_, m, χ, he, hχ⟩
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    exact hχ
  · intro hψ
    exact ⟨hψ.valid, n, ψ, rfl, hψ⟩

theorem satisfiesOpenCodes_zfVP_iff (U : V) :
    SatisfiesOpenCodes U zfVPOpenAxiomCodes ↔ IsInternalZFModel U ∧
      ∀ φ : V, IsMembershipFormulaCode (2 : V) φ → MembershipSatisfies U 0 (vopenkaCode φ) ∅ := by
  constructor
  · intro hU
    have hzf : SatisfiesOpenCodes U zfOpenAxiomCodes := by
      refine ⟨hU.1, fun n ψ hψ ↦ ?_⟩
      exact hU.2 n ψ ((mem_zfVPOpenAxiomCodes_iff n ψ).mpr
        (Or.inl ((mem_zfOpenAxiomCodes_iff n ψ).mp hψ)))
    refine ⟨(satisfiesOpenCodes_zf_iff U).mp hzf, fun φ hφ ↦ ?_⟩
    have hmem : ⟨(0 : V), vopenkaCode φ⟩ₖ ∈ (zfVPOpenAxiomCodes : V) :=
      (mem_zfVPOpenAxiomCodes_iff _ _).mpr (Or.inr ⟨rfl, (mem_vopenkaAxiomCodes_iff _).mpr ⟨φ, hφ, rfl⟩⟩)
    exact (hU.2 0 _ hmem).2 ∅ (by simp [mem_function_iff, zero_def])
  · rintro ⟨hzf, hvp⟩
    have hT : SatisfiesSentenceCodes U vopenkaAxiomCodes := by
      refine ⟨hzf.1.1, fun ψ hψ ↦ ⟨vopenkaAxiomCodes_sentence hψ, ?_⟩⟩
      obtain ⟨φ, hφ, rfl⟩ := (mem_vopenkaAxiomCodes_iff ψ).mp hψ
      exact hvp φ hφ
    refine ⟨hzf.1.1, fun n ψ hψ ↦ ?_⟩
    have hax := (mem_zfVPOpenAxiomCodes_iff n ψ).mp hψ
    refine ⟨hax.valid, fun b hb ↦ ?_⟩
    rcases hax with hax | ⟨rfl, hmem⟩
    · exact (hzf.satisfies_open_codes.2 n ψ ((mem_zfOpenAxiomCodes_iff n ψ).mpr hax)).2 b hb
    · exact hT.all_assignments hmem hb

theorem codedZFVP_model_consistent {U : V} (hzf : IsInternalZFModel U)
    (hvp : ∀ φ : V, IsMembershipFormulaCode (2 : V) φ → MembershipSatisfies U 0 (vopenkaCode φ) ∅) :
    OpenCodedSequentConsistent (zfVPOpenAxiomCodes : V) :=
  ((satisfiesOpenCodes_zfVP_iff U).mpr ⟨hzf, hvp⟩).openCodedSequentConsistent

end ZFVP
