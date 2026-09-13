import ZFVP.ModelTheory.NamedMembershipStructure
import ZFVP.Syntax.LiftSubstitution

/-! Coded elementary embeddings preserve every named element. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem namedMembership_constantTerm_mem {I n i : V} (hn : n ∈ (ω : V)) (hi : i ∈ I) :
    functionTermCode i ∅ ∈ termSet (namedMembershipLanguageCode I) ∅ n := by
  apply (functionTermCode_mem_iff (namedMembershipLanguageCode_valid I) hn ∅ i ∅).mpr
  simp only [namedMembershipLanguageCode, functionSymbols_code, functionArities_code]
  refine ⟨hi, ?_⟩
  rw [value_constantGraph _ _ hi]
  simp [mem_function_iff, zero_def]

theorem namedMembership_constantTerm_eval {I A c n i : V} (hn : n ∈ (ω : V)) (hi : i ∈ I) (b : V) :
    (termEvaluation (namedMembershipLanguageCode I) ∅ n
      (namedMembershipStructureCode I A c) b ∅) ‘ (functionTermCode i ∅) = c ‘ i := by
  rw [termEvaluation_function (namedMembershipLanguageCode_valid I) hn ∅ _ b ∅
    (namedMembership_constantTerm_mem hn hi), graph_empty_compose]
  exact namedMembershipStructureCode_function_value hi (by simp [mem_function_iff, zero_def])

noncomputable def namedPointArguments (i : V) : V :=
  standardTuple ![boundVarCode (0 : V), functionTermCode i ∅]

noncomputable def namedPointCode (i : V) : V := atomCode equalityToken (namedPointArguments i)

theorem namedPointArguments_valid {I i : V} (hi : i ∈ I) :
    IsAtomicArguments (namedMembershipLanguageCode I) ∅ (1 : V) equalityToken (namedPointArguments i) := by
  refine Or.inl ⟨rfl, ?_⟩
  apply standardTuple_mem_function
  intro j
  refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ Fin.elim0 k) j) j
  · exact (termSet_closed (namedMembershipLanguageCode_valid I) (by simp) ∅).1 0 (by simp)
  · exact namedMembership_constantTerm_mem (by simp) hi

theorem namedPointCode_mem {I i : V} (hi : i ∈ I) :
    namedPointCode i ∈ formulaSet (namedMembershipLanguageCode I) ∅ (1 : V) :=
  (formulaSet_atoms (namedMembershipLanguageCode_valid I) (by simp) (namedPointArguments_valid hi)).1

theorem namedPointArguments_evaluated {I A c i : V} (hi : i ∈ I) (b : V) :
    evaluatedArguments (namedMembershipLanguageCode I) ∅ (namedMembershipStructureCode I A c) ∅
      (1 : V) b (namedPointArguments i) = standardTuple ![b ‘ (0 : V), c ‘ i] := by
  unfold evaluatedArguments evaluateWithFreeAssignment namedPointArguments
  rw [compose_standardTuple]
  · congr 1
    funext j
    refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ Fin.elim0 k) j) j
    · exact termEvaluation_boundVar (namedMembershipLanguageCode_valid I) (by simp) ∅ _ b ∅ (by simp)
    · exact namedMembership_constantTerm_eval (by simp) hi b
  · intro j
    rw [domain_termEvaluation]
    refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ Fin.elim0 k) j) j
    · exact (termSet_closed (namedMembershipLanguageCode_valid I) (by simp) ∅).1 0 (by simp)
    · exact namedMembership_constantTerm_mem (by simp) hi

theorem satisfies_namedPointCode {I A c i b : V} (hi : i ∈ I) (hb : b ∈ A ^ (1 : V)) :
    Satisfies (namedMembershipLanguageCode I) ∅ (namedMembershipStructureCode I A c) ∅
      (1 : V) (namedPointCode i) b ↔ b ‘ (0 : V) = c ‘ i := by
  have hb' : b ∈ structureDomain (namedMembershipStructureCode I A c) ^ (1 : V) := by simpa using hb
  rw [namedPointCode, satisfies_atom (namedMembershipLanguageCode_valid I) (by simp)
    (namedPointArguments_valid hi) hb', atomicHolds_equality, namedPointArguments_evaluated hi b]
  exact Iff.of_eq (congrArg₂ Eq (value_standardTuple _ 0) (value_standardTuple _ 1))

theorem IsCodedElementaryEmbedding.named_values {I A B c d f : V}
    (h : IsCodedElementaryEmbedding (namedMembershipLanguageCode I)
      (namedMembershipStructureCode I A c) (namedMembershipStructureCode I B d) f)
    (hc : c ∈ A ^ I) {i : V} (hi : i ∈ I) : f ‘ (c ‘ i) = d ‘ i := by
  have hf : f ∈ B ^ A := by simpa only [namedMembershipStructureCode_domain] using h.function
  let := IsFunction.of_mem hf
  have hb : standardTuple ![c ‘ i] ∈ A ^ (1 : V) :=
    standardTuple_mem_function _ (by simpa using function_value_mem hc hi)
  have hs : Satisfies (namedMembershipLanguageCode I) ∅ (namedMembershipStructureCode I A c) ∅
      (1 : V) (namedPointCode i) (standardTuple ![c ‘ i]) :=
    (satisfies_namedPointCode hi hb).mpr (value_standardTuple _ 0)
  have ht := (h.satisfies_iff (by simp) (namedPointCode_mem hi) (by simpa using hb)).mp hs
  have ht' := (satisfies_namedPointCode hi (compose_function hb hf)).mp ht
  have hz : (standardTuple ![c ‘ i]) ‘ (0 : V) = c ‘ i := value_standardTuple _ (0 : Fin 1)
  rw [value_compose_of_mem_function hb hf (show (0 : V) ∈ (1 : V) by simp), hz] at ht'
  exact ht'

end ZFVP
