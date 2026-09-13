import ZFVP.Syntax.PrimitiveProgramPrefixRenaming
import ZFVP.Syntax.PrimitiveProgramReindexStandard
import ZFVP.Syntax.TailTemplatePrimrec

/-! Explicit programs compile template instances with any internally finite parameter tail. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

namespace MembershipTemplate

def compileTailProgram {a : ℕ} : {m : ℕ} → MembershipTemplate a m → PrimitiveProgram
  | _, .fixed ψ => constant (Encodable.encode ψ)
  | _, .hole r => .comp reindexCode (.pair (.comp (PrimitiveProgram.prefixRenaming r) .left) (.pair .zero .right))
  | _, .conj s t => tagged 4 (.pair s.compileTailProgram t.compileTailProgram)
  | _, .disj s t => tagged 5 (.pair s.compileTailProgram t.compileTailProgram)
  | _, .neg s => .comp negateCode s.compileTailProgram
  | _, .all s => tagged 6 s.compileTailProgram
  | _, .exs s => tagged 7 s.compileTailProgram

def closedTailProgram {a : ℕ} (t : MembershipTemplate a 0) : PrimitiveProgram :=
  .comp universalClosure (.pair .left t.compileTailProgram)

theorem compileTailProgram_encode {a m k : ℕ} (t : MembershipTemplate a m)
    (φ : SetTheorySemisentence (k + a)) :
    t.compileTailProgram.eval (Nat.pair k (Encodable.encode φ)) = Encodable.encode (t.instantiateTail k φ) := by
  induction t with
  | fixed ψ =>
    rw [compileTailProgram, evalNat_constant]
    exact (MembershipTemplate.fixed ψ).compileTailNat_encode φ
  | hole r =>
    simp only [compileTailProgram, evalNat_comp, evalNat_pair, evalNat_left, evalNat_right,
      evalNat_zero, Nat.unpair_pair, prefixRenaming_nat, natPrefixRenaming_eq]
    exact reindexCode_boundIndexRew_encode (prefixIndexMap k r) φ
  | conj s t ihs iht =>
    simp only [compileTailProgram, evalNat_tagged, evalNat_pair, ihs, iht]
    rfl
  | disj s t ihs iht =>
    simp only [compileTailProgram, evalNat_tagged, evalNat_pair, ihs, iht]
    rfl
  | neg s ih =>
    simp only [compileTailProgram, evalNat_comp, ih, negateCode_encode]
    rfl
  | all s ih =>
    simp only [compileTailProgram, evalNat_tagged, ih]
    rfl
  | exs s ih =>
    simp only [compileTailProgram, evalNat_tagged, ih]
    rfl

theorem closedTailProgram_encode {a k : ℕ} (t : MembershipTemplate a 0)
    (φ : SetTheorySemisentence (k + a)) :
    t.closedTailProgram.eval (Nat.pair k (Encodable.encode φ)) = Encodable.encode (∀¹* t.instantiateTail k φ) := by
  simp only [closedTailProgram, evalNat_comp, evalNat_pair, evalNat_left, Nat.unpair_pair,
    compileTailProgram_encode]
  exact universalClosure_encode (t.instantiateTail k φ)

end MembershipTemplate
end ZFVP
