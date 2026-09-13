import ZFVP.ModelTheory.TransitiveZFCoding
import ZFVP.ModelTheory.EmbeddingCriticalPointImage
import ZFVP.SetTheory.HartogsDictionary

/-! Internal elementary graphs, critical points and cardinal witnesses in transitive ZF models. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem embedding_of_embedding (A B f : SetDomain U)
    (hf : IsCodedMembershipEmbedding A.val B.val f.val) : IsCodedMembershipEmbedding A B f :=
  (eval_piOneMembershipEmbeddingFormula A B f).mp (codedMembershipEmbedding_downward U A B f hf)

theorem criticalPoint_iff (A B f κ : SetDomain U) [IsTransitive A] [IsTransitive A.val]
    (hf : f ∈ B ^ A) : IsCriticalPoint A f κ ↔ IsCriticalPoint A.val f.val κ.val := by
  rw [criticalPoint_iff_graphSpec hf, criticalPoint_iff_graphSpec ((function_iff U f A B).mp hf)]
  exact bounded_defined_absolute U boundedCriticalPointFormula_bounded
    (fun v ↦ CriticalPointGraphSpec (v 0) (v 1) (v 2))
    (fun v ↦ CriticalPointGraphSpec (v 0) (v 1) (v 2)) ![A, f, κ]

theorem initial_of_noLowRankCofinalMaps (κ : SetDomain U) (hκ : IsOrdinal κ.val)
    (hn : NoLowRankCofinalMaps κ.val) : IsInitialOrdinal κ := by
  let := hκ
  refine ⟨(ordinal_iff U κ).mpr hκ, ?_⟩
  intro α hα hbad
  obtain ⟨g, hg, hr⟩ := surjection_of_injection hbad ⟨α, hα⟩
  have hgV : g.val ∈ κ.val ^ α.val ∧ range g.val = κ.val :=
    (bounded_defined_absolute U boundedSurjectionFormula_bounded
      (fun v ↦ v 0 ∈ v 2 ^ v 1 ∧ range (v 0) = v 2)
      (fun v ↦ v 0 ∈ v 2 ^ v 1 ∧ range (v 0) = v 2) ![g, α, κ]).mp ⟨hg, hr⟩
  apply hn α.val (ordinal_subset_hierarchy κ.val _ hα) g.val
  refine ⟨hgV.1, ?_⟩
  intro β hβ
  obtain ⟨x, hxβ⟩ := mem_range_iff.mp (hgV.2.symm ▸ hβ)
  let := IsFunction.of_mem hgV.1
  exact ⟨x, (mem_of_mem_functions hgV.1 hxβ).1, (value_eq_of_kpair_mem hxβ).symm ▸ subset_refl β⟩

end TransitiveZF

end ZFVP
