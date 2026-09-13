import ZFVP.ModelTheory.ForcingModel
import ZFVP.SetTheory.BoundedCodingPrimitives
import ZFVP.SetTheory.FunctionValue

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem check_defined_bounded (S : ForcingContext V) {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsBoundedSetFormula φ) (P : (Fin n → V) → Prop) (Q : (Fin n → S.Model) → Prop)
    [Defined P φ] [Defined Q φ] (b : Fin n → V) : P b ↔ Q (fun i ↦ S.check (b i)) :=
  (Defined.eval_iff b).symm.trans ((S.check_bounded hφ b).trans (Defined.eval_iff _))

theorem check_empty (S : ForcingContext V) : S.check ∅ = ∅ :=
  (S.check_defined_bounded boundedEmptyFormula_bounded (fun v ↦ v 0 = ∅) (fun v ↦ v 0 = ∅) ![∅]).mp rfl

theorem check_singleton (S : ForcingContext V) (x : V) : S.check ({x} : V) = {S.check x} :=
  (S.check_defined_bounded boundedSingletonFormula_bounded (fun v ↦ v 0 = {v 1})
    (fun v ↦ v 0 = {v 1}) ![{x}, x]).mp rfl

theorem check_pair (S : ForcingContext V) (x y : V) : S.check ({x, y} : V) = {S.check x, S.check y} := by
  have h := (S.check_defined_bounded boundedDoubletonFormula_bounded (fun v ↦ v 0 = doubleton (v 1) (v 2))
    (fun v ↦ v 0 = doubleton (v 1) (v 2)) ![doubleton x y, x, y]).mp rfl
  simpa [← pair_eq_doubleton] using h

theorem check_kpair (S : ForcingContext V) (x y : V) : S.check ⟨x, y⟩ₖ = ⟨S.check x, S.check y⟩ₖ :=
  (S.check_defined_bounded boundedKpairFormula_bounded (fun v ↦ v 0 = ⟨v 1, v 2⟩ₖ)
    (fun v ↦ v 0 = ⟨v 1, v 2⟩ₖ) ![⟨x, y⟩ₖ, x, y]).mp rfl

theorem check_succ (S : ForcingContext V) (x : V) : S.check (succ x) = succ (S.check x) :=
  (S.check_defined_bounded boundedSuccFormula_bounded (fun v ↦ v 0 = succ (v 1))
    (fun v ↦ v 0 = succ (v 1)) ![succ x, x]).mp rfl

theorem check_ordinal_iff (S : ForcingContext V) (x : V) : IsOrdinal (S.check x) ↔ IsOrdinal x :=
  (S.check_defined_bounded isOrdinalFormula_bounded (fun v ↦ IsOrdinal (v 0))
    (fun v ↦ IsOrdinal (v 0)) ![x]).symm

instance check_ordinal (S : ForcingContext V) (x : V) [IsOrdinal x] : IsOrdinal (S.check x) :=
  (S.check_ordinal_iff x).mpr inferInstance

theorem check_function_iff (S : ForcingContext V) (f A B : V) :
    S.check f ∈ S.check B ^ S.check A ↔ f ∈ B ^ A :=
  (S.check_defined_bounded boundedFunctionFormula_bounded (fun v ↦ v 0 ∈ v 2 ^ v 1)
    (fun v ↦ v 0 ∈ v 2 ^ v 1) ![f, A, B]).symm

instance check_isFunction (S : ForcingContext V) (f : V) [IsFunction f] : IsFunction (S.check f) :=
  ⟨S.check (domain f), S.check (range f),
    (S.check_function_iff f (domain f) (range f)).mpr (IsFunction.mem_function f)⟩

theorem check_domain (S : ForcingContext V) (f : V) [IsFunction f] : domain (S.check f) = S.check (domain f) :=
  domain_eq_of_mem_function ((S.check_function_iff f (domain f) (range f)).mpr (IsFunction.mem_function f))

theorem check_value (S : ForcingContext V) {f x : V} [IsFunction f] (hx : x ∈ domain f) :
    (S.check f) ‘ (S.check x) = S.check (f ‘ x) := by
  apply value_eq_of_kpair_mem
  rw [← S.check_kpair, S.check_mem_iff]
  exact kpair_mem_iff_value.mpr ⟨hx, rfl⟩

end ForcingContext
end ZFVP
