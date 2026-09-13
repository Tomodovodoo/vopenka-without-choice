import ZFVP.Syntax.TemplatePrimrec

/-! Uniform natural-number lists representing the schema parameter renamings. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

theorem ofFn_prefixVector {α : Type*} {k m : ℕ} (v : Fin m → α) (b : Fin k → α) :
    List.ofFn (prefixVector v b) = List.ofFn v ++ List.ofFn b := by
  induction m with
  | zero => simp [prefixVector]
  | succ m ih => simp [prefixVector, List.ofFn_succ, ih]

def natPrefixRenaming {a m : ℕ} (r : Fin a → Fin m) (k : ℕ) : List ℕ :=
  List.ofFn (fun i ↦ (r i).val) ++ (List.range k).map (fun i ↦ i + m)

theorem natPrefixRenaming_eq {a m : ℕ} (r : Fin a → Fin m) (k : ℕ) :
    natPrefixRenaming r k = List.ofFn (fun i ↦ (prefixIndexMap k r i).val) := by
  have he : (fun i ↦ (prefixIndexMap k r i).val) =
      prefixVector (fun i ↦ (r i).val) (fun i : Fin k ↦ i.val + m) := by
    exact prefixVector_map Fin.val _ _
  rw [he, ofFn_prefixVector]
  unfold natPrefixRenaming
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem natPrefixRenaming_primrec {a m : ℕ} (r : Fin a → Fin m) : Primrec (natPrefixRenaming r) :=
  Primrec.list_append.comp (Primrec.const (List.ofFn (fun i ↦ (r i).val)))
    (Primrec.list_map Primrec.list_range (Primrec.nat_add.comp Primrec.snd (Primrec.const m)))

end ZFVP
