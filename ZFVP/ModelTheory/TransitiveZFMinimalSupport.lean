import ZFVP.ModelTheory.ForcingRecodedSparse
import ZFVP.ModelTheory.TransitiveZFLimitColumns
import ZFVP.ModelTheory.TransitiveZFSparsePair
import ZFVP.ModelTheory.RankNormalizationLimitMaps

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem isMinimalSectionPoint_iff (P E k p : SetDomain U) :
    IsMinimalSectionPoint P E k p ↔ IsMinimalSectionPoint P.val E.val k.val p.val := by
  unfold IsMinimalSectionPoint
  rw [← value_val_total U P k]
  apply and_congr_right
  intro _
  apply forall_mem_val_iff U
  intro j
  rw [← value_val_total U P j]
  apply forall_mem_val_iff U
  intro q
  rw [← kpair_val U, ← value_val_total U, ← value_val_total U]
  exact not_congr ⟨congrArg Subtype.val, Subtype.ext⟩

theorem forcingSparseCodes_val (θ s A : SetDomain U) :
    (forcingSparseCodes θ s A).val = forcingSparseCodes θ.val s.val A.val := by
  unfold forcingSparseCodes forcingMinimalSupportCodes
  rw [← prod_val U]
  apply sep_val U
  intro a _
  rw [isMinimalSectionPoint_iff U, forcingCodeP_val U, forcingCodeE_val U,
    kpair_first_val U, kpair_second_val U]

theorem forcingSparseDecode_val (θ s A : SetDomain U) :
    (forcingSparseDecode θ s A).val = forcingSparseDecode θ.val s.val A.val := by
  unfold forcingSparseDecode forcingMinimalSupportMap
  rw [← forcingSparseCodes, ← forcingSparseCodes, ← forcingSparseCodes_val U]
  apply definableGraph_val U
  intro a _
  simp only [forcingMinimalSupportDecode, forcingSectionThread_val U, forcingCodeπ_val U,
    forcingCodeE_val U, kpair_first_val U, kpair_second_val U]

theorem forcingSparseEncode_val (θ s A : SetDomain U) :
    (forcingSparseEncode θ s A).val = forcingSparseEncode θ.val s.val A.val := by
  unfold forcingSparseEncode
  rw [converseGraph_val U, forcingSparseDecode_val U]
end TransitiveZF
end ZFVP

