import ZFVP.Syntax.Universe

/-! Internal term codes matching Foundation's bound/free/function constructors.
The term set is the least internally closed subset of a proved coding bound. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def boundVarCode (i : V) : V := ⟨(0 : V), i⟩ₖ
noncomputable def freeVarCode (x : V) : V := ⟨(1 : V), x⟩ₖ
noncomputable def functionTermCode (f args : V) : V := ⟨(2 : V), ⟨f, args⟩ₖ⟩ₖ

instance boundVarCode_definable : ℒₛₑₜ-function₁[V] boundVarCode := by
  unfold boundVarCode
  definability
instance freeVarCode_definable : ℒₛₑₜ-function₁[V] freeVarCode := by
  unfold freeVarCode
  definability
instance functionTermCode_definable : ℒₛₑₜ-function₂[V] functionTermCode := by
  unfold functionTermCode
  definability

def IsTermClosed (L Γ n T : V) : Prop :=
  (∀ i ∈ n, boundVarCode i ∈ T) ∧ (∀ x ∈ Γ, freeVarCode x ∈ T) ∧
  ∀ f ∈ functionSymbols L, ∀ args ∈ T ^ ((functionArities L) ‘ f), functionTermCode f args ∈ T

instance isTermClosed_definable : ℒₛₑₜ-relation₄[V] IsTermClosed := by
  unfold IsTermClosed
  definability

noncomputable def termSet (L Γ n : V) : V :=
  {t ∈ syntaxUniverse L Γ ; ∀ T, IsTermClosed L Γ n T → t ∈ T}

instance termSet_definable : ℒₛₑₜ-function₃[V] termSet := by
  have h : ℒₛₑₜ-relation₄ (fun X L Γ n : V ↦ ∀ t,
      t ∈ X ↔ t ∈ syntaxUniverse L Γ ∧ ∀ T, IsTermClosed L Γ n T → t ∈ T) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = termSet (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp [termSet]

theorem mem_termSet_iff (L Γ n t : V) :
    t ∈ termSet L Γ n ↔ t ∈ syntaxUniverse L Γ ∧ ∀ T, IsTermClosed L Γ n T → t ∈ T := by
  simp [termSet]

theorem termSet_minimal {L Γ n T : V} (hT : IsTermClosed L Γ n T) : termSet L Γ n ⊆ T :=
  fun t ht ↦ ((mem_termSet_iff L Γ n t).mp ht).2 T hT

theorem syntaxUniverse_termClosed {L n : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V)) (Γ : V) :
    IsTermClosed L Γ n (syntaxUniverse L Γ) := by
  have h0 : (0 : V) ∈ syntaxUniverse L Γ := codingUniverse_natural_mem _ (by simp)
  have h1 : (1 : V) ∈ syntaxUniverse L Γ := codingUniverse_natural_mem _ (by simp)
  have h2 : (2 : V) ∈ syntaxUniverse L Γ := codingUniverse_natural_mem _ (by simp)
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hiω : i ∈ (ω : V) := IsOrdinal.toIsTransitive.mem_trans hi hn
    exact codingUniverse_kpair_closed h0 (codingUniverse_natural_mem _ hiω)
  · intro x hx
    exact codingUniverse_kpair_closed h1
      ((syntaxUniverse_transitive L Γ).mem_trans hx (freeVariables_mem_syntaxUniverse L Γ))
  · intro f hf args ha
    have hfU := (syntaxUniverse_transitive L Γ).mem_trans hf (functionSymbols_mem_syntaxUniverse hL Γ)
    have haU : args ∈ syntaxUniverse L Γ := finiteSequence_mem_codingUniverse _
      ((mem_finiteSequences_iff _ _).mpr ⟨(functionArities L) ‘ f, hL.function_arity_natural hf, ha⟩)
    exact codingUniverse_kpair_closed h2 (codingUniverse_kpair_closed hfU haU)

theorem termSet_closed {L n : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V)) (Γ : V) :
    IsTermClosed L Γ n (termSet L Γ n) := by
  have hU := syntaxUniverse_termClosed hL hn Γ
  have hsub : termSet L Γ n ⊆ syntaxUniverse L Γ := termSet_minimal hU
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact (mem_termSet_iff L Γ n _).mpr ⟨hU.1 i hi, fun T hT ↦ hT.1 i hi⟩
  · intro x hx
    exact (mem_termSet_iff L Γ n _).mpr ⟨hU.2.1 x hx, fun T hT ↦ hT.2.1 x hx⟩
  · intro f hf args ha
    refine (mem_termSet_iff L Γ n _).mpr ⟨?_, ?_⟩
    · exact hU.2.2 f hf args (mem_function_of_mem_function_of_subset ha hsub)
    · intro T hT
      exact hT.2.2 f hf args (mem_function_of_mem_function_of_subset ha (termSet_minimal hT))

end ZFVP
