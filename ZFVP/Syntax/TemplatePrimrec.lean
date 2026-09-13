import ZFVP.Syntax.NaturalIndexRenamingPrimrec

/-! Primitive recursive template instantiation for each fixed template. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

theorem reindexNatFormula_boundIndexRew {n m : ℕ} (r : Fin n → Fin m) (φ : SetTheorySemisentence n) :
    reindexNatFormula (List.ofFn (fun i ↦ (r i).val)) 0 (Encodable.encode φ) =
      Encodable.encode (boundIndexRew r ▹ φ) := by
  apply reindexNatFormula_encode
  intro i
  refine ⟨r i, rfl, ?_⟩
  simp [reindexNatVariable, List.getD_eq_getElem?_getD, i.isLt]

theorem boundIndexRew_primrec {n m : ℕ} (r : Fin n → Fin m) :
    Primrec (fun φ : SetTheorySemisentence n ↦ boundIndexRew r ▹ φ) := by
  apply Primrec.encode_iff.mp
  exact (reindexNatFormula_primrec.comp (Primrec.const (List.ofFn (fun i ↦ (r i).val)))
    (Primrec₂.pair.comp (Primrec.const 0) Primrec.encode)).of_eq (reindexNatFormula_boundIndexRew r)

theorem MembershipTemplate.instantiate_primrec {a m : ℕ} (t : MembershipTemplate a m) :
    Primrec (fun φ : SetTheorySemisentence a ↦ t.instantiate φ) := by
  induction t with
  | fixed ψ => exact Primrec.const ψ
  | hole r => exact boundIndexRew_primrec r
  | conj s t ihs iht => exact Semiformula.primrec₂_and.comp ihs iht
  | disj s t ihs iht => exact Semiformula.primrec₂_or.comp ihs iht
  | neg s ih => exact (membershipFormula_neg_primrec _).comp ih
  | all s ih => exact (membershipFormula_all_primrec _).comp ih
  | exs s ih => exact (membershipFormula_exs_primrec _).comp ih

end ZFVP
