import ZFVP.ModelTheory.TransitiveZFCardinalSmall
import ZFVP.SetTheory.Hartogs

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {ξ : V} [IsOrdinal ξ] [Nonempty (SetDomain (hierarchy ξ))]
  [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rank_hartogsNumber_val (hs : ∀ β ∈ ξ, succ β ∈ ξ)
    (A : SetDomain (hierarchy ξ)) :
    (hartogsNumber A).val = hartogsNumber A.val := by
  let := hierarchy_transitive ξ
  let H := hartogsNumber A
  have hH : IsOrdinal H.val :=
    (TransitiveZF.ordinal_iff (hierarchy ξ) H).mp inferInstance
  let := hH
  apply SetTheory.subset_antisymm
  · intro β hβ
    let b : SetDomain (hierarchy ξ) :=
      ⟨β, (hierarchy_transitive ξ).mem_trans hβ H.property⟩
    have hb : b ∈ hartogsNumber A := hβ
    have hc := (rank_cardLE_iff hs b A).mp (cardLE_of_mem_hartogsNumber hb)
    let := IsOrdinal.of_mem hβ
    exact ordinal_cardLE_iff_mem_hartogsNumber.mp hc
  · exact hartogsNumber_minimal (fun h ↦ not_hartogsNumber_cardLE A
      ((rank_cardLE_iff hs H A).mpr h))

end ZFVP

