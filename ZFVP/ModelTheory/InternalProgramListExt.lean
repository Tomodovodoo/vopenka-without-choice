import ZFVP.ModelTheory.InternalProgramLists
import ZFVP.Syntax.PrimitiveProgramListExt
import ZFVP.Syntax.Assignments

/-! Injectivity and constructors of the uniform internal list decoder. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

@[simp] theorem internalArithmeticVal_succ (w : InternalArithmetic V) :
    internalArithmeticVal (w + 1) = SetTheory.succ (internalArithmeticVal w) := by
  simp only [internalArithmeticVal_add, internalArithmeticVal_one]
  exact ordinalAdd_one_natural (internalArithmeticVal_mem w)

namespace PrimitiveProgram

theorem evalSet_listGet_cons_zero {x xs : V} (hx : x ∈ (ω : V)) (hxs : xs ∈ (ω : V)) :
    listGet.evalSet (naturalSquarePair (SetTheory.succ (naturalSquarePair x xs)) 0) = x := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hx
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hxs
  rw [← internalArithmeticVal_pair, ← internalArithmeticVal_succ,
    ← internalArithmeticVal_zero, evalSet_pair_val, evalArithmetic_listGet_cons_zero]

theorem evalSet_listGet_cons_succ {x xs i : V}
    (hx : x ∈ (ω : V)) (hxs : xs ∈ (ω : V)) (hi : i ∈ (ω : V)) :
    listGet.evalSet (naturalSquarePair (SetTheory.succ (naturalSquarePair x xs)) (SetTheory.succ i)) =
      listGet.evalSet (naturalSquarePair xs i) := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hx
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hxs
  obtain ⟨w, rfl⟩ := internalArithmeticVal_surjective hi
  rw [← internalArithmeticVal_pair, ← internalArithmeticVal_succ, ← internalArithmeticVal_succ,
    evalSet_pair_val, evalArithmetic_listGet_cons_succ, evalSet_pair_val]

end PrimitiveProgram

open PrimitiveProgram

theorem decodedNaturalList_injective {x y : V} (hx : x ∈ (ω : V)) (hy : y ∈ (ω : V))
    (h : decodedNaturalList x = decodedNaturalList y) : x = y := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hx
  obtain ⟨v, rfl⟩ := internalArithmeticVal_surjective hy
  apply congrArg internalArithmeticVal
  apply listCode_ext u v
  · apply internalArithmeticVal_injective
    have hd := congrArg SetTheory.domain h
    simpa only [domain_decodedNaturalList, ← evalArithmetic_agreement] using hd
  · intro i hi
    apply internalArithmeticVal_injective
    have hiu : internalArithmeticVal i ∈ listLength.evalSet (internalArithmeticVal u) := by
      rw [← evalArithmetic_agreement, ← internalArithmetic_lt]
      exact hi
    have hiv : internalArithmeticVal i ∈ listLength.evalSet (internalArithmeticVal v) := by
      have hd := congrArg SetTheory.domain h
      simp only [domain_decodedNaturalList] at hd
      exact hd ▸ hiu
    have he := congrArg (fun s : V ↦ s ‘ (internalArithmeticVal i)) h
    simpa only [value_decodedNaturalList hiu, value_decodedNaturalList hiv, evalSet_pair_val] using he

theorem decodedNaturalList_cons {x xs : V} (hx : x ∈ (ω : V)) (hxs : xs ∈ (ω : V)) :
    decodedNaturalList (SetTheory.succ (naturalSquarePair x xs)) =
      assignmentPrepend (listLength.evalSet xs) (decodedNaturalList xs) x := by
  have hlen := evalSet_natural listLength hxs
  have hc := ω_succ_closed (naturalSquarePair_natural hx hxs)
  have hdom := evalSet_listLength_cons hx hxs
  have hf : decodedNaturalList (SetTheory.succ (naturalSquarePair x xs)) ∈
      (ω : V) ^ SetTheory.succ (listLength.evalSet xs) := hdom ▸ decodedNaturalList_mem_function hc
  have hg := assignmentPrepend_mem_function hlen (decodedNaturalList_mem_function hxs) hx
  apply function_ext hf hg
  intro i hi y _ hiy
  apply kpair_mem_iff_value.mpr
  refine ⟨by simpa using hi, ?_⟩
  have hv := value_eq_of_kpair_mem hiy
  rw [value_decodedNaturalList (hdom.symm ▸ hi)] at hv
  have hiω : i ∈ (ω : V) := IsTransitive.transitive _ (ω_succ_closed hlen) _ hi
  rcases internalNatural_cases hiω with rfl | ⟨j, hj, rfl⟩
  · rw [assignmentPrepend_zero hlen]
    exact (evalSet_listGet_cons_zero hx hxs).symm.trans hv
  · have hne : SetTheory.succ j ≠ (0 : V) := by
      intro he
      have hm : j ∈ SetTheory.succ j := by simp
      simp [he, zero_def] at hm
    have hjlen : j ∈ listLength.evalSet xs := by
      have hpred := natural_predecessor_mem hlen hi hne
      have : IsOrdinal j := IsOrdinal.of_mem hj
      simpa only [sUnion_succ_of_transitive] using hpred
    rw [assignmentPrepend_succ hlen hjlen, value_decodedNaturalList hjlen]
    exact (evalSet_listGet_cons_succ hx hxs hj).symm.trans hv

end ZFVP
