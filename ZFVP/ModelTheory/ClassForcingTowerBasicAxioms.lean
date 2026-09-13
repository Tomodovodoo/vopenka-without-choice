import ZFVP.ModelTheory.MembershipDirectedLimitBasic
import ZFVP.ModelTheory.ClassForcingTowerModel

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace DefinableForcingTower
variable (T : DefinableForcingTower V) {G : Set V}
    (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)

local instance : ∀ i, Nonempty ((T.directedSystem hG).Model i) :=
  fun i ↦ inferInstanceAs (Nonempty ((T.boundedContext hG i.val).Model))

local instance : ∀ i, ((T.directedSystem hG).Model i)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 :=
  fun i ↦ inferInstanceAs (((T.boundedContext hG i.val).Model)↓[ℒₛₑₜ] ⊧* 𝗭𝗙)

theorem classModel_models_empty : (T.ClassModel hG)↓[ℒₛₑₜ] ⊧ Axiom.empty :=
  (T.directedSystem hG).limit_models_empty

theorem classModel_models_extensionality : (T.ClassModel hG)↓[ℒₛₑₜ] ⊧ Axiom.extentionality :=
  (T.directedSystem hG).limit_models_extensionality

theorem classModel_models_pairing : (T.ClassModel hG)↓[ℒₛₑₜ] ⊧ Axiom.pairing :=
  (T.directedSystem hG).limit_models_pairing

theorem classModel_models_union : (T.ClassModel hG)↓[ℒₛₑₜ] ⊧ Axiom.union :=
  (T.directedSystem hG).limit_models_union

theorem classModel_models_infinity : (T.ClassModel hG)↓[ℒₛₑₜ] ⊧ Axiom.infinity :=
  (T.directedSystem hG).limit_models_infinity

theorem classModel_models_foundation : (T.ClassModel hG)↓[ℒₛₑₜ] ⊧ Axiom.foundation :=
  (T.directedSystem hG).limit_models_foundation

end DefinableForcingTower
end ZFVP
