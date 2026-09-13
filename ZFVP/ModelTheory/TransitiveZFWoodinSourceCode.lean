import ZFVP.ModelTheory.WoodinSourceCode
import ZFVP.ModelTheory.TransitiveZFIterationHistory
import ZFVP.ModelTheory.TransitiveZFCoding
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSourceIndex_val (α : SetDomain U) (hα : IsOrdinal α) :
    (woodinSourceIndex α).val = woodinSourceIndex α.val := by
  let := hα
  let := (ordinal_iff U α).mp hα
  by_cases hn : α ∈ (ω : SetDomain U)
  · rw [woodinSourceIndex_natural hn, woodinSourceIndex_natural ((natural_iff U α).mp hn), succ_val U]
  · rw [woodinSourceIndex_infinite hn,
      woodinSourceIndex_infinite (fun hc ↦ hn ((natural_iff U α).mpr hc))]

theorem woodinRecursiveIndex_val (β : SetDomain U) :
    (woodinRecursiveIndex β).val = woodinRecursiveIndex β.val := by
  classical
  by_cases hn : β ∈ (ω : SetDomain U)
  · simp only [woodinRecursiveIndex, hn, (natural_iff U β).mp hn, ↓reduceIte, sUnion_val U]
  · have hn' : β.val ∉ (ω : V) := fun hc ↦ hn ((natural_iff U β).mpr hc)
    simp only [woodinRecursiveIndex, hn, hn', ↓reduceIte]

theorem woodinInsertSeedValue_val (f a β : SetDomain U) :
    (woodinInsertSeedValue f a β).val = woodinInsertSeedValue f.val a.val β.val := by
  classical
  by_cases hz : β = ∅
  · subst β
    simp only [woodinInsertSeedValue, empty_val U, ↓reduceIte]
  · have hz' : β.val ≠ ∅ := by
      intro he
      apply hz
      apply Subtype.ext
      simpa only [empty_val U] using he
    simp only [woodinInsertSeedValue, hz, hz', ↓reduceIte, value_val_total U, woodinRecursiveIndex_val U]

theorem woodinInsertSeed_val (θ f a : SetDomain U) (hθ : IsOrdinal θ) :
    (woodinInsertSeed θ f a).val = woodinInsertSeed θ.val f.val a.val := by
  unfold woodinInsertSeed
  rw [← woodinSourceIndex_val U θ hθ]
  apply definableGraph_val U
  intro β _
  exact woodinInsertSeedValue_val U f a β

theorem woodinSeedMatrixValue_val (M C z : SetDomain U) :
    (woodinSeedMatrixValue M C z).val = woodinSeedMatrixValue M.val C.val z.val := by
  classical
  by_cases hz : kpair.π₁ z = ∅
  · have hz' : kpair.π₁ z.val = ∅ := by
      rw [← kpair_first_val U]
      simpa only [empty_val U] using congrArg Subtype.val hz
    simp only [woodinSeedMatrixValue, hz, hz', ↓reduceIte, value_val_total U, kpair_second_val U]
  · have hz' : kpair.π₁ z.val ≠ ∅ := by
      intro he
      apply hz
      apply Subtype.ext
      rw [kpair_first_val U, empty_val U]
      exact he
    simp only [woodinSeedMatrixValue, hz, hz', ↓reduceIte, value_val_total U, kpair_val U,
      woodinRecursiveIndex_val U, kpair_first_val U, kpair_second_val U]

theorem woodinSeedMatrix_val (θ M C : SetDomain U) (hθ : IsOrdinal θ) :
    (woodinSeedMatrix θ M C).val = woodinSeedMatrix θ.val M.val C.val := by
  unfold woodinSeedMatrix
  rw [← woodinSourceIndex_val U θ hθ, ← prod_val U]
  apply definableGraph_val U
  intro z _
  exact woodinSeedMatrixValue_val U M C z

theorem woodinSeedProjectionColumn_val (θ Q : SetDomain U) (hθ : IsOrdinal θ) :
    (woodinSeedProjectionColumn θ Q).val = woodinSeedProjectionColumn θ.val Q.val := by
  unfold woodinSeedProjectionColumn
  rw [← woodinSourceIndex_val U θ hθ]
  apply definableGraph_val U
  intro j _
  rw [prod_val U, value_val_total U, singleton_val U, empty_val U]

theorem woodinSeedSectionColumn_val (θ t : SetDomain U) (hθ : IsOrdinal θ) :
    (woodinSeedSectionColumn θ t).val = woodinSeedSectionColumn θ.val t.val := by
  unfold woodinSeedSectionColumn
  rw [← woodinSourceIndex_val U θ hθ]
  apply definableGraph_val U
  intro j _
  rw [prod_val U, singleton_val U, singleton_val U, empty_val U, value_val_total U]

theorem woodinSeedLiftMap_val (Q : SetDomain U) :
    (woodinSeedLiftMap Q).val = woodinSeedLiftMap Q.val := by
  unfold woodinSeedLiftMap
  rw [← empty_val U, ← singleton_val U, ← prod_val U]
  apply definableGraph_val U
  intro z _
  exact kpair_first_val U z

theorem woodinSeedLiftColumn_val (θ Q : SetDomain U) (hθ : IsOrdinal θ) :
    (woodinSeedLiftColumn θ Q).val = woodinSeedLiftColumn θ.val Q.val := by
  unfold woodinSeedLiftColumn
  rw [← woodinSourceIndex_val U θ hθ]
  apply definableGraph_val U
  intro j _
  rw [woodinSeedLiftMap_val U, value_val_total U]

theorem woodinSeedProjections_val (θ P π : SetDomain U) (hθ : IsOrdinal θ) :
    (woodinSeedProjections θ P π).val = woodinSeedProjections θ.val P.val π.val := by
  simp only [woodinSeedProjections, woodinSeedMatrix_val U _ _ _ hθ,
    woodinSeedProjectionColumn_val U _ _ hθ, woodinInsertSeed_val U _ _ _ hθ,
    singleton_val U, empty_val U]

theorem woodinSeedSections_val (θ E t : SetDomain U) (hθ : IsOrdinal θ) :
    (woodinSeedSections θ E t).val = woodinSeedSections θ.val E.val t.val := by
  simp only [woodinSeedSections, woodinSeedMatrix_val U _ _ _ hθ,
    woodinSeedSectionColumn_val U _ _ hθ, woodinInsertSeed_val U _ _ _ hθ, empty_val U]

theorem woodinSeedLifts_val (θ P L : SetDomain U) (hθ : IsOrdinal θ) :
    (woodinSeedLifts θ P L).val = woodinSeedLifts θ.val P.val L.val := by
  simp only [woodinSeedLifts, woodinSeedMatrix_val U _ _ _ hθ,
    woodinSeedLiftColumn_val U _ _ hθ, woodinInsertSeed_val U _ _ _ hθ, singleton_val U, empty_val U]

theorem woodinSourceCode_val (θ s : SetDomain U) (hθ : IsOrdinal θ) :
    (woodinSourceCode θ s).val = woodinSourceCode θ.val s.val := by
  simp only [woodinSourceCode, forcingIterationCode_val U,
    woodinInsertSeed_val U _ _ _ hθ, woodinSeedProjections_val U _ _ _ hθ,
    woodinSeedSections_val U _ _ _ hθ, woodinSeedLifts_val U _ _ _ hθ,
    forcingCodeP_val U, forcingCodeR_val U, forcingCodeπ_val U, forcingCodeE_val U,
    forcingCodeL_val U, forcingCodet_val U, singleton_val U, prod_val U, empty_val U]

theorem woodinSourceCardinals_val (θ K : SetDomain U) (hθ : IsOrdinal θ)
    (hseed : (woodinSeedCardinal : SetDomain U).val = (woodinSeedCardinal : V)) :
    (woodinSourceCardinals θ K).val = woodinSourceCardinals θ.val K.val := by
  simp only [woodinSourceCardinals, woodinInsertSeed_val U _ _ _ hθ, hseed]
end TransitiveZF
end ZFVP
