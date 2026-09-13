import ZFVP.ModelTheory.ForcingModel

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem eq_of_data_eq (A B : ForcingContext V) (hP : A.P = B.P) (hR : A.R = B.R)
    (hone : A.one = B.one) (hG : A.G = B.G) : A = B := by
  cases A
  cases B
  cases hP
  cases hR
  cases hone
  cases hG
  rfl

def modelCongr {A B : ForcingContext V} (h : A = B) : A.Model ≃ B.Model :=
  Equiv.cast (congrArg ForcingContext.Model h)

theorem modelCongr_mem_iff {A B : ForcingContext V} (h : A = B) (x y : A.Model) :
    modelCongr h x ∈ modelCongr h y ↔ x ∈ y := by
  subst B
  rfl

theorem modelCongr_check {A B : ForcingContext V} (h : A = B) (x : V) :
    modelCongr h (A.check x) = B.check x := by
  subst B
  rfl

end ForcingContext
end ZFVP
