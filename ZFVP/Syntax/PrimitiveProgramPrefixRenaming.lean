import ZFVP.Syntax.PrimitiveProgramTabulateStandard
import ZFVP.Syntax.NaturalPrefixRenaming

/-! Explicit parameter-tail renaming tables for each fixed template hole. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace PrimitiveProgram

def prefixRenaming {a m : ℕ} (r : Fin a → Fin m) : PrimitiveProgram :=
  .comp listAppend (.pair
    (.comp (forwardTabulate addition) (.pair (constant m) identity))
    (constant (Encodable.encode (List.ofFn (fun i ↦ (r i).val)))))

theorem prefixRenaming_nat {a m : ℕ} (r : Fin a → Fin m) (k : ℕ) :
    (prefixRenaming r).eval k = Encodable.encode (natPrefixRenaming r k) := by
  simp only [prefixRenaming, evalNat_comp, evalNat_pair, evalNat_constant, evalNat_identity,
    forwardTabulate_encode, evalNat_addition, listAppend_encode, natPrefixRenaming, Nat.add_comm]

end PrimitiveProgram
end ZFVP
