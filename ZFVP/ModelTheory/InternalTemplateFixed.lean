import ZFVP.ModelTheory.InternalReindexSubstitution
import ZFVP.ModelTheory.InternalPrefixProgram
import ZFVP.ModelTheory.InternalStandardRequirements
import ZFVP.Syntax.PrimitiveProgramTemplate

/-! Fixed template formulas are unchanged by adjoining unused internal parameters. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem decodedNaturalList_encode_ofFn {m : ℕ} (v : Fin m → ℕ) :
    decodedNaturalList (Encodable.encode (List.ofFn v) : V) = standardTuple (fun i ↦ (v i : V)) := by
  induction m with
  | zero => exact decodedNaturalList_encode_tuple []
  | succ m ih =>
    rw [List.ofFn_succ, Encodable.encode_list_cons, Encodable.encode_nat, ← naturalCons_natCast,
      decodedNaturalList_cons (by simp) (by simp), evalSet_listLength_encode, List.length_ofFn, ih]
    rfl

theorem renameMembershipFormula_encode_prefix {m : ℕ} (ψ : SetTheorySemisentence m)
    {n : V} (hn : n ∈ (ω : V)) :
    renameMembershipFormula (m : V) (prefixSize m n) (standardTuple (fun i : Fin m ↦ (i.val : V)))
      (encodeMembershipFormula ψ) = encodeMembershipFormula ψ := by
  let r := List.ofFn (fun i : Fin m ↦ i.val)
  have hlen : listLength.evalSet (Encodable.encode r : V) = (m : V) := by
    simp only [r, evalSet_listLength_encode, List.length_ofFn]
  have hR : decodedNaturalList (Encodable.encode r : V) ∈ prefixSize m n ^ listLength.evalSet (Encodable.encode r : V) := by
    rw [hlen, decodedNaturalList_encode_ofFn]
    exact standardTuple_mem_function _ (natCast_mem_prefixSize hn)
  have hv : requirementFits ((formulaRequirement false).evalSet (Encodable.encode ψ : V))
      (listLength.evalSet (Encodable.encode r : V)) := by
    rw [hlen]
    exact requirementFits_encode false Empty.elim ψ
  have he := decodedNaturalFormula_reindex_rename (r := (Encodable.encode r : V)) (by simp)
    (prefixSize_natural m hn) (by simp) hR hv
  rw [hlen, decodedNaturalList_encode_ofFn, decodedNaturalFormula_membership] at he
  rw [← he]
  change decodedNaturalFormula (reindexCode.evalSet (naturalSquarePair (Encodable.encode r : V)
    (naturalSquarePair (0 : ℕ) (Encodable.encode ψ : V)))) = _
  rw [naturalSquarePair_natCast, naturalSquarePair_natCast, evalSet_natCast]
  have hp := reindexCode_boundIndexRew_encode (fun i : Fin m ↦ i) ψ
  rw [encodeNatFormula_sameIndices _ (fun i ↦ ⟨i, rfl, rfl⟩)] at hp
  rw [hp, decodedNaturalFormula_membership]

end ZFVP
