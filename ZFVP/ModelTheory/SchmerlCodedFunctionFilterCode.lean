import ZFVP.ModelTheory.SchmerlCodedFunctionTransport

/-! Rubin-definable function filters have membership codes in the represented
model, since the full finite-function poset is bounded by one of its sets. -/

set_option autoImplicit false

namespace ZFVP.BinaryRelationRepresentation

open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (R : BinaryRelationRepresentation (V := V) W)

theorem functionNodeSubset_has_code (hω : HasStandardOmega V) (s : W) {A : V}
    (hA : IsCodedDefinableSet R.code A)
    (hsub : A ⊆ codedFunctionNodes R.code (R.equiv s).val) :
    ∃ m ∈ structureDomain R.code, codedMemberTrace R.code m = A := by
  have hdef := R.predicate_of_isCodedDefinableSet hω hA
  let m : W := sep (finitePartialFunctions s ((2 : ℕ) : W)) (fun p ↦ (R.equiv p).val ∈ A) hdef
  have hm (p : W) : p ∈ m ↔ (R.equiv p).val ∈ A := by
    rw [show p ∈ m ↔ p ∈ finitePartialFunctions s ((2 : ℕ) : W) ∧ (R.equiv p).val ∈ A from mem_sep_iff]
    exact ⟨And.right, fun hp ↦ ⟨(R.functionNode_mem_iff s p).mp (hsub _ hp), hp⟩⟩
  have hmem (p : W) : codedMember R.code (R.equiv p).val (R.equiv m).val ↔ p ∈ m := by
    simpa [codedMember] using R.codedBinary_iff (“x a. x ∈ a” : SetTheorySemisentence 2) p m
  refine ⟨(R.equiv m).val, by
    simpa only [code, binaryRelationStructureCode_domain] using (R.equiv m).property, ?_⟩
  apply mem_ext
  intro x
  by_cases hx : x ∈ R.carrier
  · let p : W := R.equiv.symm ⟨x, hx⟩
    have hp : (R.equiv p).val = x := congrArg Subtype.val (R.equiv.apply_symm_apply _)
    rw [← hp, mem_codedMemberTrace, hmem, hm, and_iff_right]
    simpa only [code, binaryRelationStructureCode_domain] using (R.equiv p).property
  · have hnD : x ∉ structureDomain R.code := by simpa only [code, binaryRelationStructureCode_domain] using hx
    have hnA : x ∉ A := fun ha ↦ hnD (hA.1 x ha)
    simp only [mem_codedMemberTrace, hnD, hnA, false_and]

theorem codedFunctionBranchFilter_has_code (hω : HasStandardOmega V) (s : W)
    {κ c B : V} [IsOrdinal κ]
    (hc : IsInternalCofinalStrictChain κ (codedFiniteDomains R.code (R.equiv s).val)
      (codedFiniteDomainOrder R.code (R.equiv s).val) c)
    (hB : IsInternalCofinalBranch (codedSelectedFunctionNodes R.code (R.equiv s).val κ c)
      (codedSelectedFunctionOrder R.code (R.equiv s).val κ c) κ
      (codedSelectedFunctionRank R.code (R.equiv s).val κ c) B)
    (hRubin : IsCodedRubin R.code κ) :
    ∃ m ∈ structureDomain R.code,
      codedMemberTrace R.code m = codedFunctionBranchFilter R.code (R.equiv s).val B :=
  R.functionNodeSubset_has_code hω s (R.codedFunctionBranchFilter_isCodedDefinable s hc hB hRubin)
    (fun _ hp ↦ ((mem_codedFunctionBranchFilter _ _ _ _).mp hp).1)

end ZFVP.BinaryRelationRepresentation
