import ZFVP.SetTheory.EndExtensionRelations
import ZFVP.SetTheory.ForcingSeparativeOrder

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
namespace MembershipEndExtension
variable {V W : Type*} [SetStructure V] [SetStructure W] [Nonempty V] [Nonempty W]
  [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingCompatible_iff (j : MembershipEndExtension V W) (P R p q : V) :
    ForcingCompatible (j P) (j R) (j p) (j q) ↔ ForcingCompatible P R p q := by
  unfold ForcingCompatible
  rw [j.exists_mem_iff]
  simp only [← j.map_kpair, j.mem_iff]

theorem forcingSeparativeOrder_iff (j : MembershipEndExtension V W) (P R p q : V) :
    ⟨j p, j q⟩ₖ ∈ forcingSeparativeOrder (j P) (j R) ↔
      ⟨p, q⟩ₖ ∈ forcingSeparativeOrder P R := by
  rw [kpair_mem_forcingSeparativeOrder, kpair_mem_forcingSeparativeOrder, j.mem_iff, j.mem_iff,
    j.forall_mem_iff]
  simp only [← j.map_kpair, j.mem_iff, j.forcingCompatible_iff]

end MembershipEndExtension
end ZFVP
