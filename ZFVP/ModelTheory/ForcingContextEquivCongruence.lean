import ZFVP.ModelTheory.ForcingContextCongruence

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext

theorem modelCongr_trans_mem {A B C : ForcingContext V} (h : A = B) (e : B.Model ≃ C.Model)
    (he : ∀ x y, e x ∈ e y ↔ x ∈ y) (x y : A.Model) :
    ((modelCongr h).trans e) x ∈ ((modelCongr h).trans e) y ↔ x ∈ y := by
  subst B
  exact he x y

theorem modelCongr_trans_check {A B C : ForcingContext V} (h : A = B) (e : B.Model ≃ C.Model)
    (he : ∀ x : V, e (B.check x) = C.check x) (x : V) :
    ((modelCongr h).trans e) (A.check x) = C.check x := by
  subst B
  exact he x

end ForcingContext
end ZFVP
