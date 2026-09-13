import ZFVP.SetTheory.AtomicForcingDictionary
import ZFVP.SetTheory.ForcingQuantifiers
import ZFVP.Syntax.StandardTuples

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingTermValue {n : ℕ} : Semiterm ℒₛₑₜ Empty n → V → V
  | .bvar i, b => b ‘ (i.val : V)
  | .fvar x, _ => Empty.elim x
  | .func f _, _ => Empty.elim f

instance forcingTermValue_definable {n : ℕ} (t : Semiterm ℒₛₑₜ Empty n) :
    ℒₛₑₜ-function₁[V] (forcingTermValue t) := by
  cases t with
  | bvar i => unfold forcingTermValue; definability
  | fvar x => exact Empty.elim x
  | func f _ => exact Empty.elim f

noncomputable def forcingAtomic (P R : V) {n k : ℕ} (r : Language.Set.Rel k)
    (ts : Fin k → Semiterm ℒₛₑₜ Empty n) (b : V) : V :=
  match r with
  | .eq => atomicEquality P R (forcingTermValue (ts 0) b) (forcingTermValue (ts 1) b)
  | .mem => atomicMembership P R (forcingTermValue (ts 0) b) (forcingTermValue (ts 1) b)

instance forcingAtomic_definable (P R : V) {n k : ℕ} (r : Language.Set.Rel k)
    (ts : Fin k → Semiterm ℒₛₑₜ Empty n) : ℒₛₑₜ-function₁[V] (forcingAtomic P R r ts) := by
  cases r <;> unfold forcingAtomic <;> definability

theorem forcingAtomic_regular {P R : V} (hR : IsForcingPreorder P R) {n k : ℕ}
    (r : Language.Set.Rel k) (ts : Fin k → Semiterm ℒₛₑₜ Empty n) (b : V) :
    IsForcingRegular P R (forcingAtomic P R r ts b) := by
  cases r with
  | eq => exact atomicEquality_regular hR _ _
  | mem => exact atomicMembership_regular hR _ _

end ZFVP
