import ZFVP.ModelTheory.CodedSequentSemantics
import ZFVP.Syntax.MembershipSwap

/-! Internally finite variable renaming and the two sequent quantifier rules. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

noncomputable def successorIndices (n : V) : V := definableGraph n succ (by definability)

instance successorIndices_definable : ℒₛₑₜ-function₁[V] successorIndices := by
  unfold successorIndices
  definability

theorem successorIndices_function {n : V} (hn : n ∈ (ω : V)) : successorIndices n ∈ succ n ^ n :=
  definableGraph_mem_function_of_mapsTo _ _ _ (by definability) (fun _ hi ↦ succ_mem_succ_of_natural_mem hn hi)

theorem successorIndices_compose_prepend {n U b x : V} (hn : n ∈ (ω : V))
    (hb : b ∈ U ^ n) (hx : x ∈ U) :
    compose (successorIndices n) (assignmentPrepend n b x) = b := by
  have hr := successorIndices_function hn
  have hp := assignmentPrepend_mem_function hn hb hx
  apply function_eq_of_values (compose_function hr hp) hb
  intro i hi
  rw [value_compose_of_mem_function hr hp hi,
    show (successorIndices n) ‘ i = succ i from value_definableGraph _ _ _ hi,
    assignmentPrepend_succ hn hi]

noncomputable def renameCodedSequent (n m r Γ : V) : V :=
  repl (fun φ ↦ renameMembershipFormula n m r φ) (by definability) Γ

instance renameCodedSequent_definable : ℒₛₑₜ-function₄[V] renameCodedSequent := by
  have hh : ℒₛₑₜ-relation₅ (fun R n m r Γ : V ↦
      ∀ ψ, ψ ∈ R ↔ ∃ φ ∈ Γ, ψ = renameMembershipFormula n m r φ) := by definability
  apply Language.Definable.of_iff hh
  intro v
  change v 0 = renameCodedSequent (v 1) (v 2) (v 3) (v 4) ↔ _
  simp only [mem_ext_iff, renameCodedSequent, repl_spec]

theorem mem_renameCodedSequent_iff (n m r Γ ψ : V) :
    ψ ∈ renameCodedSequent n m r Γ ↔ ∃ φ ∈ Γ, ψ = renameMembershipFormula n m r φ := repl_spec _

noncomputable def shiftCodedSequent (n Γ : V) : V := renameCodedSequent n (succ n) (successorIndices n) Γ

instance shiftCodedSequent_definable : ℒₛₑₜ-function₂[V] shiftCodedSequent := by
  unfold shiftCodedSequent
  definability

noncomputable def instantiateMembershipFormula (n i φ : V) : V :=
  renameMembershipFormula (succ n) n (assignmentPrepend n (identity n) i) φ

instance instantiateMembershipFormula_definable : ℒₛₑₜ-function₃[V] instantiateMembershipFormula := by
  unfold instantiateMembershipFormula
  definability

theorem membershipSatisfies_instantiate {U n i φ b : V} (hU : IsNonempty U)
    (hn : n ∈ (ω : V)) (hi : i ∈ n)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n)) (hb : b ∈ U ^ n) :
    MembershipSatisfies U n (instantiateMembershipFormula n i φ) b ↔
      MembershipSatisfies U (succ n) φ (assignmentPrepend n b (b ‘ i)) := by
  have hr := assignmentPrepend_mem_function hn (identity_mem_function n) hi
  have he := membershipSatisfies_rename hU (ω_succ_closed hn) hn hr hφ hb
  rw [compose_assignmentPrepend hn (identity_mem_function n) hb hi, graph_identity_compose hb] at he
  exact he

theorem codedSequentHolds_rename {U n m r Γ b : V} (hU : IsNonempty U)
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hr : r ∈ m ^ n)
    (hΓ : Γ ⊆ formulaSet membershipLanguageCode ∅ n) (hb : b ∈ U ^ m) :
    CodedSequentHolds U m (renameCodedSequent n m r Γ) b ↔ CodedSequentHolds U n Γ (compose r b) := by
  constructor
  · rintro ⟨ψ, hψ, ht⟩
    obtain ⟨φ, hφ, rfl⟩ := (mem_renameCodedSequent_iff n m r Γ ψ).mp hψ
    exact ⟨φ, hφ, (membershipSatisfies_rename hU hn hm hr (hΓ _ hφ) hb).mp ht⟩
  · rintro ⟨φ, hφ, ht⟩
    exact ⟨renameMembershipFormula n m r φ, (mem_renameCodedSequent_iff _ _ _ _ _).mpr ⟨φ, hφ, rfl⟩,
      (membershipSatisfies_rename hU hn hm hr (hΓ _ hφ) hb).mpr ht⟩

theorem codedSequentTrue_rename {U n m r Γ : V} (hU : IsNonempty U)
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hr : r ∈ m ^ n)
    (hΓ : Γ ⊆ formulaSet membershipLanguageCode ∅ n) (ht : CodedSequentTrue U n Γ) :
    CodedSequentTrue U m (renameCodedSequent n m r Γ) := by
  intro b hb
  exact (codedSequentHolds_rename hU hn hm hr hΓ hb).mpr (ht _ (compose_function hr hb))

theorem codedSequentHolds_shift {U n Γ b x : V} (hU : IsNonempty U)
    (hn : n ∈ (ω : V)) (hΓ : Γ ⊆ formulaSet membershipLanguageCode ∅ n)
    (hb : b ∈ U ^ n) (hx : x ∈ U) :
    CodedSequentHolds U (succ n) (shiftCodedSequent n Γ) (assignmentPrepend n b x) ↔
      CodedSequentHolds U n Γ b := by
  have he := codedSequentHolds_rename hU hn (ω_succ_closed hn) (successorIndices_function hn) hΓ
    (assignmentPrepend_mem_function hn hb hx)
  rw [successorIndices_compose_prepend hn hb hx] at he
  exact he

theorem codedSequentTrue_all {U n Γ φ : V} (hU : IsNonempty U)
    (hn : n ∈ (ω : V)) (hΓ : Γ ⊆ formulaSet membershipLanguageCode ∅ n)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n))
    (ht : CodedSequentTrue U (succ n) (insert φ (shiftCodedSequent n Γ))) :
    CodedSequentTrue U n (insert (allCode φ) Γ) := by
  classical
  intro b hb
  rw [codedSequentHolds_insert]
  by_cases hΓb : CodedSequentHolds U n Γ b
  · exact Or.inr hΓb
  · apply Or.inl
    apply (membershipSatisfies_all hn hφ hb).mpr
    intro x hx
    have hh := (codedSequentHolds_insert _ _ _ _ _).mp (ht _ (assignmentPrepend_mem_function hn hb hx))
    exact hh.resolve_right (fun hs ↦ hΓb ((codedSequentHolds_shift hU hn hΓ hb hx).mp hs))

theorem codedSequentTrue_exists {U n Γ φ i : V} (hU : IsNonempty U)
    (hn : n ∈ (ω : V)) (hi : i ∈ n)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n))
    (ht : CodedSequentTrue U n (insert (instantiateMembershipFormula n i φ) Γ)) :
    CodedSequentTrue U n (insert (existsCode φ) Γ) := by
  intro b hb
  have hh := (codedSequentHolds_insert _ _ _ _ _).mp (ht b hb)
  rw [codedSequentHolds_insert]
  rcases hh with hh | hh
  · exact Or.inl ((membershipSatisfies_exists hn hφ hb).mpr
      ⟨b ‘ i, function_value_mem hb hi, (membershipSatisfies_instantiate hU hn hi hφ hb).mp hh⟩)
  · exact Or.inr hh

end ZFVP
