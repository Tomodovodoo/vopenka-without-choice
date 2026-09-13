import ZFVP.Syntax.VopenkaCodes
import ZFVP.Syntax.FormulaSubstitutionDefinability

/-! The internal set of compiled Vopenka axioms and its model condition. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₅.comp

instance boundVariableAssignment_definable : ℒₛₑₜ-function₁[V] boundVariableAssignment := by
  unfold boundVariableAssignment
  definability

instance renameMembershipFormula_definable : ℒₛₑₜ-function₄[V] renameMembershipFormula := by
  unfold renameMembershipFormula
  definability

instance MembershipTemplate.compile_definable {a n : ℕ} (t : MembershipTemplate a n) :
    ℒₛₑₜ-function₁[V] (fun φ ↦ t.compile φ) := by
  induction t with
  | fixed ψ => change ℒₛₑₜ-function₁[V] (fun _ ↦ encodeMembershipFormula ψ); definability
  | hole r => simp only [MembershipTemplate.compile]; definability
  | conj s t ihs iht => simp only [MembershipTemplate.compile]; definability
  | disj s t ihs iht => simp only [MembershipTemplate.compile]; definability
  | neg s ih => simp only [MembershipTemplate.compile]; definability
  | all s ih => simp only [MembershipTemplate.compile]; definability
  | exs s ih => simp only [MembershipTemplate.compile]; definability

instance vopenkaCode_definable : ℒₛₑₜ-function₁[V] vopenkaCode :=
  MembershipTemplate.compile_definable vopenkaTemplate

noncomputable def vopenkaAxiomCodes : V :=
  {ψ ∈ formulaSet membershipLanguageCode ∅ (0 : V) ;
    ∃ φ, IsMembershipFormulaCode (2 : V) φ ∧ ψ = vopenkaCode φ}

theorem mem_vopenkaAxiomCodes_iff (ψ : V) : ψ ∈ (vopenkaAxiomCodes : V) ↔
    ∃ φ, IsMembershipFormulaCode (2 : V) φ ∧ ψ = vopenkaCode φ := by
  unfold vopenkaAxiomCodes
  rw [mem_sep_iff]
  constructor
  · exact And.right
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨(vopenkaCode_valid hφ).valid, φ, hφ, rfl⟩

theorem vopenkaAxiomCodes_sentence {ψ : V} (hψ : ψ ∈ (vopenkaAxiomCodes : V)) :
    IsMembershipFormulaCode (0 : V) ψ := by
  obtain ⟨φ, hφ, rfl⟩ := (mem_vopenkaAxiomCodes_iff ψ).mp hψ
  exact vopenkaCode_valid hφ

def SatisfiesSentenceCodes (U T : V) : Prop :=
  IsNonempty U ∧ ∀ ψ ∈ T, IsMembershipFormulaCode (0 : V) ψ ∧ MembershipSatisfies U 0 ψ ∅

theorem satisfiesSentenceCodes_vopenka_iff (U : V) :
    SatisfiesSentenceCodes U vopenkaAxiomCodes ↔
      IsNonempty U ∧ ∀ φ : V, IsMembershipFormulaCode (2 : V) φ → LocalCodedVopenka U φ := by
  constructor
  · rintro ⟨hU, hT⟩
    refine ⟨hU, fun φ hφ ↦ ?_⟩
    exact (vopenkaCode_satisfies hU hφ).mp
      (hT (vopenkaCode φ) ((mem_vopenkaAxiomCodes_iff _).mpr ⟨φ, hφ, rfl⟩)).2
  · rintro ⟨hU, hVP⟩
    refine ⟨hU, fun ψ hψ ↦ ?_⟩
    obtain ⟨φ, hφ, rfl⟩ := (mem_vopenkaAxiomCodes_iff ψ).mp hψ
    exact ⟨vopenkaCode_valid hφ, (vopenkaCode_satisfies hU hφ).mpr (hVP φ hφ)⟩

end ZFVP
