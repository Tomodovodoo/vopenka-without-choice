import ZFVP.Syntax.BinaryRelationSatisfaction
import ZFVP.Syntax.MembershipTailTemplates
import ZFVP.Syntax.DirectMembershipAtoms

/-! Renaming and schema-template semantics for an arbitrary coded relation.
Both logical equality tokens and the set language's equality relation use literal equality. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem codedMembershipSatisfies_rename {M n m r φ b : V}
    (hM : IsStructureCode membershipLanguageCode M)
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hr : r ∈ m ^ n)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hb : b ∈ structureDomain M ^ m) :
    Satisfies membershipLanguageCode ∅ M ∅ m (renameMembershipFormula n m r φ) b ↔
      Satisfies membershipLanguageCode ∅ M ∅ n φ (compose r b) := by
  have he : (∅ : V) ∈ structureDomain M ^ (∅ : V) := by simp [mem_function_iff]
  have hT := termEvaluation_mem_function hM hm ∅ hb he
  have hB := boundVariableAssignment_mem hm
  have hev : compose (boundVariableAssignment m)
      (termEvaluation membershipLanguageCode ∅ m M b ∅) = b := by
    apply function_eq_of_values (compose_function hB hT) hb
    intro i hi
    rw [value_compose_of_mem_function hB hT hi, boundVariableAssignment_value hi,
      termEvaluation_boundVar membershipLanguageCode_valid hm ∅ _ _ _ hi]
  have hs := satisfies_substituteFormula (φ := φ) (b := b) hM (membershipRenaming_state hn hm hr) he
    (by simpa only [stateSource_code] using hφ) (by simpa only [stateTarget_code] using hb)
  simp only [stateTarget_code, stateSource_code, stateFree_code, stateBound_code,
    graph_empty_compose, graph_compose_assoc, hev] at hs
  exact hs

theorem binaryAtomic_logicalEquality {n i j : V} (hn : n ∈ (ω : V)) (hi : i ∈ n) (hj : j ∈ n)
    (D E b : V) : AtomicHolds membershipLanguageCode ∅ (binaryRelationStructureCode D E) ∅ n b
      equalityToken (boundPairArguments i j) ↔ b ‘ i = b ‘ j := by
  rw [atomicHolds_equality, boundPair_evaluatedArguments hn hi hj]
  change (standardTuple ![b ‘ i, b ‘ j]) ‘ (((0 : Fin 2).val : ℕ) : V) =
    (standardTuple ![b ‘ i, b ‘ j]) ‘ (((1 : Fin 2).val : ℕ) : V) ↔ _
  simp only [value_standardTuple]
  rfl

theorem binaryAtomic_relationEquality {D E n b i j : V} (hn : n ∈ (ω : V)) (hi : i ∈ n) (hj : j ∈ n)
    (hb : b ∈ D ^ n) : AtomicHolds membershipLanguageCode ∅ (binaryRelationStructureCode D E) ∅ n b
      (relationToken (0 : V)) (boundPairArguments i j) ↔ b ‘ i = b ‘ j := by
  have hr : (0 : V) ∈ relationSymbols membershipLanguageCode :=
    (membershipSymbol_valid (V := V) Language.Set.Rel.eq).1
  rw [atomicHolds_relation, and_iff_right hr, binaryRelationStructureCode_equality,
    boundPair_evaluatedArguments hn hi hj]
  apply standardTuple_mem_equalityRelation
  simpa using And.intro (function_value_mem hb hi) (function_value_mem hb hj)

theorem binaryAtomic_membership {D E n b i j : V} (hn : n ∈ (ω : V)) (hi : i ∈ n) (hj : j ∈ n)
    (hb : b ∈ D ^ n) : AtomicHolds membershipLanguageCode ∅ (binaryRelationStructureCode D E) ∅ n b
      (relationToken (1 : V)) (boundPairArguments i j) ↔ ⟨b ‘ i, b ‘ j⟩ₖ ∈ E := by
  have hr : (1 : V) ∈ relationSymbols membershipLanguageCode :=
    (membershipSymbol_valid (V := V) Language.Set.Rel.mem).1
  rw [atomicHolds_relation, and_iff_right hr, binaryRelationStructureCode_relation,
    boundPair_evaluatedArguments hn hi hj]
  apply standardTuple_mem_binaryTupleRelation
  simpa using And.intro (function_value_mem hb hi) (function_value_mem hb hj)

namespace MembershipTemplate

theorem compileTail_binarySatisfies {a m : ℕ} {n φ D E b : V} (hD : IsNonempty D) (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (prefixSize a n)) (hb : b ∈ D ^ n)
    (t : MembershipTemplate a m) (v : Fin m → BinaryRelationDomain D E) :
    Satisfies membershipLanguageCode ∅ (binaryRelationStructureCode D E) ∅
      (prefixSize m n) (t.compileTail n φ) (prependTuple n b (fun i ↦ (v i).val)) ↔
      t.Eval (fun w ↦ Satisfies membershipLanguageCode ∅ (binaryRelationStructureCode D E) ∅
        (prefixSize a n) φ (prependTuple n b (fun i ↦ (w i).val))) v := by
  have hv {j : ℕ} (w : Fin j → BinaryRelationDomain D E) :
      prependTuple n b (fun i ↦ (w i).val) ∈ D ^ prefixSize j n :=
    prependTuple_function hn hb _ (fun i ↦ (w i).property)
  have hM := binaryRelationStructureCode_valid hD E
  induction t with
  | fixed ψ =>
    have he := codedMembershipSatisfies_rename hM (by simp) (prefixSize_natural _ hn)
      (standardTuple_mem_function _ (natCast_mem_prefixSize hn)) (encodeMembershipFormula_mem ψ)
      (by simpa only [binaryRelationStructureCode_domain] using hv v)
    rw [standardIndices_compose_prependTuple hn hb _ (fun i ↦ (v i).property)] at he
    exact he.trans (satisfies_encodeBinaryRelationFormula hD ψ v)
  | hole r =>
    have he := codedMembershipSatisfies_rename hM (prefixSize_natural _ hn) (prefixSize_natural _ hn)
      (prefixRenaming_function r hn) hφ (by simpa only [binaryRelationStructureCode_domain] using hv v)
    rw [prefixRenaming_compose r hn hb _ (fun i ↦ (v i).property)] at he
    exact he
  | conj s t ihs iht =>
    exact (satisfies_and (M := binaryRelationStructureCode D E) (e := ∅) membershipLanguageCode_valid
      (prefixSize_natural _ hn) (s.compileTail_valid hn hφ) (t.compileTail_valid hn hφ)
      (by simpa only [binaryRelationStructureCode_domain] using hv v)).trans (and_congr (ihs v) (iht v))
  | disj s t ihs iht =>
    exact (satisfies_or (M := binaryRelationStructureCode D E) (e := ∅) membershipLanguageCode_valid
      (prefixSize_natural _ hn) (s.compileTail_valid hn hφ) (t.compileTail_valid hn hφ)
      (by simpa only [binaryRelationStructureCode_domain] using hv v)).trans (or_congr (ihs v) (iht v))
  | neg s ih =>
    exact (satisfies_negateFormula (M := binaryRelationStructureCode D E) (e := ∅) membershipLanguageCode_valid
      (s.compileTail_valid hn hφ) (by simpa only [binaryRelationStructureCode_domain] using hv v)).trans
      (not_congr (ih v))
  | @all m s ih =>
    rw [compileTail, satisfies_all membershipLanguageCode_valid (prefixSize_natural _ hn)
      (s.compileTail_valid hn hφ) (by simpa only [binaryRelationStructureCode_domain] using hv v),
      binaryRelationStructureCode_domain]
    change (∀ x : V, x ∈ D → _) ↔ ∀ x : BinaryRelationDomain D E, s.Eval _ (x :> v)
    constructor
    · intro hh x
      apply (ih (x :> v)).mp
      simpa only [prefixSize, prependTuple, Matrix.cons_val_zero, Matrix.cons_val_succ] using hh x.val x.property
    · intro hh x hx
      let x' : BinaryRelationDomain D E := ⟨x, hx⟩
      have he := (ih (x' :> v)).mpr (hh x')
      simpa only [prefixSize, prependTuple, Matrix.cons_val_zero, Matrix.cons_val_succ] using he
  | @exs m s ih =>
    rw [compileTail, satisfies_exists membershipLanguageCode_valid (prefixSize_natural _ hn)
      (s.compileTail_valid hn hφ) (by simpa only [binaryRelationStructureCode_domain] using hv v),
      binaryRelationStructureCode_domain]
    change (∃ x : V, x ∈ D ∧ _) ↔ ∃ x : BinaryRelationDomain D E, s.Eval _ (x :> v)
    constructor
    · rintro ⟨x, hx, hh⟩
      let x' : BinaryRelationDomain D E := ⟨x, hx⟩
      refine ⟨x', (ih (x' :> v)).mp ?_⟩
      simpa only [prefixSize, prependTuple, Matrix.cons_val_zero, Matrix.cons_val_succ] using hh
    · rintro ⟨x, hx⟩
      refine ⟨x.val, x.property, ?_⟩
      have he := (ih (x :> v)).mpr hx
      simpa only [prefixSize, prependTuple, Matrix.cons_val_zero, Matrix.cons_val_succ] using he

end MembershipTemplate

end ZFVP
