import ZFVP.ModelTheory.SymmetricModelZF
import ZFVP.ModelTheory.ForcingModelRank

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SymmetricContext

theorem inclusion_defined_bounded (S : SymmetricContext V) {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsBoundedSetFormula φ) (P : (Fin n → S.Model) → Prop)
    (Q : (Fin n → S.toForcingContext.Model) → Prop)
    [Defined P φ] [Defined Q φ] (b : Fin n → S.Model) : P b ↔ Q (fun i ↦ S.toOrdinary (b i)) :=
  (Defined.eval_iff b).symm.trans ((S.inclusion.bounded_elementary hφ b).trans (Defined.eval_iff _))

theorem toOrdinary_ordinal_iff (S : SymmetricContext V) (x : S.Model) :
    IsOrdinal (S.toOrdinary x) ↔ IsOrdinal x :=
  (S.inclusion_defined_bounded isOrdinalFormula_bounded (fun v ↦ IsOrdinal (v 0))
    (fun v ↦ IsOrdinal (v 0)) ![x]).symm

theorem check_ordinal_iff (S : SymmetricContext V) (x : V) : IsOrdinal (S.check x) ↔ IsOrdinal x := by
  rw [← S.toOrdinary_ordinal_iff, S.toOrdinary_check]
  exact S.toForcingContext.check_ordinal_iff x

instance check_ordinal (S : SymmetricContext V) (x : V) [IsOrdinal x] : IsOrdinal (S.check x) :=
  (S.check_ordinal_iff x).mpr inferInstance

theorem ordinal_eq_check (S : SymmetricContext V) (α : S.Model) [IsOrdinal α] :
    ∃ β : V, IsOrdinal β ∧ α = S.check β := by
  have : IsOrdinal (S.toOrdinary α) := (S.toOrdinary_ordinal_iff α).mpr inferInstance
  obtain ⟨β, hβ, he⟩ := S.toForcingContext.ordinal_eq_check (S.toOrdinary α)
  exact ⟨β, hβ, S.toOrdinary_injective he⟩

end SymmetricContext
end ZFVP
