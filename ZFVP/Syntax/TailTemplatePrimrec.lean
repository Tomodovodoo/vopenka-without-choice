import ZFVP.Syntax.NaturalEncodingInvariance

/-! Uniform primitive recursive schema compilation for arbitrary finite parameter counts. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipTemplate

def compileTailNat {a : ℕ} (k e : ℕ) : {m : ℕ} → MembershipTemplate a m → ℕ
  | _, .fixed ψ => Encodable.encode ψ
  | _, .hole r => reindexNatFormula (natPrefixRenaming r k) 0 e
  | _, .conj s t => Nat.pair 4 (Nat.pair (s.compileTailNat k e) (t.compileTailNat k e)) + 1
  | _, .disj s t => Nat.pair 5 (Nat.pair (s.compileTailNat k e) (t.compileTailNat k e)) + 1
  | _, .neg s => negateNatFormula (s.compileTailNat k e)
  | _, .all s => Nat.pair 6 (s.compileTailNat k e) + 1
  | _, .exs s => Nat.pair 7 (s.compileTailNat k e) + 1

theorem compileTailNat_encode {a m k : ℕ} (φ : SetTheorySemisentence (k + a)) (t : MembershipTemplate a m) :
    t.compileTailNat k (Encodable.encode φ) = Encodable.encode (t.instantiateTail k φ) := by
  induction t with
  | @fixed m ψ =>
    exact (encodeNatFormula_sameIndices (boundIndexRew (Fin.castLE (Nat.le_add_left m k)))
      (fun i ↦ ⟨Fin.castLE (Nat.le_add_left m k) i, rfl, rfl⟩) ψ).symm
  | hole r =>
    simpa only [compileTailNat, natPrefixRenaming_eq, instantiateTail] using
      reindexNatFormula_boundIndexRew (prefixIndexMap k r) φ
  | conj s t ihs iht => exact congrArg₂ (fun x y ↦ Nat.pair 4 (Nat.pair x y) + 1) ihs iht
  | disj s t ihs iht => exact congrArg₂ (fun x y ↦ Nat.pair 5 (Nat.pair x y) + 1) ihs iht
  | neg s ih => exact (congrArg negateNatFormula ih).trans (negateNatFormula_encode _)
  | all s ih => exact congrArg (fun x ↦ Nat.pair 6 x + 1) ih
  | exs s ih => exact congrArg (fun x ↦ Nat.pair 7 x + 1) ih

theorem compileTailNat_primrec {a m : ℕ} (t : MembershipTemplate a m) : Primrec₂ t.compileTailNat := by
  induction t with
  | fixed ψ => exact Primrec.const (Encodable.encode ψ)
  | hole r =>
    exact reindexNatFormula_primrec.comp ((natPrefixRenaming_primrec r).comp Primrec.fst)
      (Primrec₂.pair.comp (Primrec.const 0) Primrec.snd)
  | conj s t ihs iht =>
    exact Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 4) (Primrec₂.natPair.comp ihs iht))
  | disj s t ihs iht =>
    exact Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 5) (Primrec₂.natPair.comp ihs iht))
  | neg s ih => exact negateNatFormula_primrec.comp ih
  | all s ih => exact Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 6) ih)
  | exs s ih => exact Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 7) ih)

end MembershipTemplate
end ZFVP
