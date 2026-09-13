import ZFVP.ModelTheory.InternalReindexTables
import ZFVP.Syntax.MembershipRenaming

/-! Finite substitution states for the explicit renaming program. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def reindexSource (r d : V) : V := ordinalAdd (listLength.evalSet r) d

instance reindexSource_definable : ℒₛₑₜ-function₂[V] reindexSource := by
  unfold reindexSource
  definability

theorem reindexSource_natural {r d : V} (hr : r ∈ (ω : V)) (hd : d ∈ (ω : V)) :
    reindexSource r d ∈ (ω : V) := ordinalAdd_natural (evalSet_natural listLength hr) hd

theorem reindexSource_zero (r : V) : reindexSource r 0 = listLength.evalSet r := ordinalAdd_zero _

theorem reindexSource_succ {r d : V} (hr : r ∈ (ω : V)) (hd : d ∈ (ω : V)) :
    reindexSource r (succ d) = succ (reindexSource r d) := by
  have : IsOrdinal (listLength.evalSet r) := IsOrdinal.of_mem (evalSet_natural listLength hr)
  have : IsOrdinal d := IsOrdinal.of_mem hd
  exact ordinalAdd_succ _ _

noncomputable def finiteReindexBoundTable (r d : V) : V :=
  definableGraph (reindexSource r d) (fun i ↦ boundVarCode (naturalReindexVariable r d i)) (by definability)

instance finiteReindexBoundTable_definable : ℒₛₑₜ-function₂[V] finiteReindexBoundTable := by
  have h : ℒₛₑₜ-relation₃ (fun B r d : V ↦ ∀ p, p ∈ B ↔
      ∃ i ∈ reindexSource r d, p = ⟨i, boundVarCode (naturalReindexVariable r d i)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = finiteReindexBoundTable (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [finiteReindexBoundTable, mem_definableGraph_iff]

theorem finiteReindexBoundTable_value {r d i : V} (hi : i ∈ reindexSource r d) :
    (finiteReindexBoundTable r d) ‘ i = boundVarCode (naturalReindexVariable r d i) :=
  value_definableGraph _ _ _ hi

theorem finiteReindexBoundTable_mem {r m d : V}
    (hr : r ∈ (ω : V)) (hm : m ∈ (ω : V)) (hd : d ∈ (ω : V))
    (hR : ∀ j ∈ listLength.evalSet r, listGet.evalSet (naturalSquarePair r j) ∈ m) :
    finiteReindexBoundTable r d ∈ termSet membershipLanguageCode ∅ (ordinalAdd m d) ^ reindexSource r d := by
  apply definableGraph_mem_function_of_mapsTo
  intro i hi
  exact (termSet_closed membershipLanguageCode_valid (ordinalAdd_natural hm hd) ∅).1 _
    (naturalReindexVariable_bound hr hm hd hR hi)

noncomputable def reindexState (r m d : V) : V :=
  substitutionState (reindexSource r d) (ordinalAdd m d) (finiteReindexBoundTable r d) ∅

instance reindexState_definable : ℒₛₑₜ-function₃[V] reindexState := by
  unfold reindexState
  definability

theorem reindexState_valid {r m d : V}
    (hr : r ∈ (ω : V)) (hm : m ∈ (ω : V)) (hd : d ∈ (ω : V))
    (hR : ∀ j ∈ listLength.evalSet r, listGet.evalSet (naturalSquarePair r j) ∈ m) :
    IsSubstitutionState membershipLanguageCode ∅ ∅ (reindexState r m d) := by
  simp only [reindexState, IsSubstitutionState, stateSource_code, stateTarget_code, stateBound_code, stateFree_code]
  exact ⟨reindexSource_natural hr hd, ordinalAdd_natural hm hd, finiteReindexBoundTable_mem hr hm hd hR,
    by apply mem_function.intro <;> simp⟩

end ZFVP
