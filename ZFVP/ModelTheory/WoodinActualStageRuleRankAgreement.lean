import ZFVP.ModelTheory.WoodinActualInverseRankThreshold
import ZFVP.ModelTheory.WoodinActualSuccessorRankThreshold
import ZFVP.ModelTheory.WoodinInitialCodeRankAgreement
import ZFVP.ModelTheory.TransitiveZFWoodinPrefixAgreement
import ZFVP.ModelTheory.TransitiveZFLimitColumns
import ZFVP.ModelTheory.WoodinRecursionSuccessor
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rank_woodinStageRule_val_of_actual {δ ξ ηS ηI : V} [IsOrdinal ξ]
    [Nonempty (SetDomain (hierarchy ξ))] [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) (hξ : IsChoicelessInaccessible ξ)
    (t s K : SetDomain (hierarchy ξ)) (ht : IsOrdinal t) (htδ : t.val ∈ δ)
    (hs : s.val = woodinIterationPrefix t.val) (hK : K.val = woodinIterationCardinalPrefix t.val)
    (hinit : (woodinInitialCode : SetDomain (hierarchy ξ)).val = (woodinInitialCode : V) ∧
      (woodinInitialCardinals : SetDomain (hierarchy ξ)).val = (woodinInitialCardinals : V))
    (hS : ∀ k ∈ t.val, IsWoodinActualSuccessorRankThreshold k ηS)
    (hI : IsWoodinActualInverseRankThreshold t.val ηI) (hSξ : ηS ∈ ξ) (hIξ : ηI ∈ ξ) :
    (woodinStageRule t s K).val = woodinStageRule t.val s.val K.val := by
  classical
  let := hierarchy_transitive ξ
  let := ht
  let := (TransitiveZF.ordinal_iff (hierarchy ξ) t).mp ht
  let := hδ.inaccessible.1
  have hclosed : ∀ β ∈ ξ, succ β ∈ ξ := fun _ hb ↦ regularCardinal_succ_closed hξ.regular hb
  by_cases hz : t = ∅
  · subst t
    simp only [TransitiveZF.empty_val, woodinStageRule_initial, TransitiveZF.kpair_val, hinit.1, hinit.2]
  have hzv : t.val ≠ ∅ := by
    intro hh
    apply hz
    apply Subtype.ext
    simpa only [TransitiveZF.empty_val] using hh
  have hsuccval : (succ (⋃ˢ t)).val = succ (⋃ˢ t.val) := by
    rw [TransitiveZF.succ_val, TransitiveZF.sUnion_val]
  by_cases hsucc : t = succ (⋃ˢ t)
  · have hsuccv : t.val = succ (⋃ˢ t.val) := (congrArg Subtype.val hsucc).trans hsuccval
    have hk : ⋃ˢ t.val ∈ t.val := (congrArg (fun θ : V ↦ (⋃ˢ t.val) ∈ θ) hsuccv).mpr
      (mem_succ_self (⋃ˢ t.val))
    let := IsOrdinal.of_mem hk
    have hh := woodinIterationHistory_of_stages
      (fun i (hi : i ∈ succ (⋃ˢ t.val)) ↦
        ((woodinIterationExit hδ hAC).2.1 i
          (IsOrdinal.toIsTransitive.mem_trans (hsuccv ▸ hi) htδ)).1)
    have hp := woodinIterationPrefix_successor hh
    have hs' : s.val = kpair.π₁ (woodinIterationRec (⋃ˢ t.val)) :=
      hs.trans ((congrArg woodinIterationPrefix hsuccv).trans hp.1)
    have hK' : K.val = kpair.π₂ (woodinIterationRec (⋃ˢ t.val)) :=
      hK.trans ((congrArg woodinIterationCardinalPrefix hsuccv).trans hp.2)
    have he := (hS _ hk).agreement hSξ hξ s K (⋃ˢ t) hs' hK'
      (TransitiveZF.sUnion_val (hierarchy ξ) t)
    simp only [woodinStageRule, ite_eq_right hz, ite_eq_left hsucc,
      ite_eq_right hzv, ite_eq_left hsuccv, TransitiveZF.kpair_val]
    rw [he.1, he.2, hs', hK']
  have hnsv : t.val ≠ succ (⋃ˢ t.val) := by
    intro hh
    exact hsucc (Subtype.ext (hh.trans hsuccval.symm))
  have hiiff : IsChoicelessInaccessible (woodinLimitCardinal K) ↔
      IsChoicelessInaccessible (woodinLimitCardinal K.val) := by
    rw [rank_choicelessInaccessible_iff hclosed, TransitiveZF.woodinLimitCardinal_val]
  by_cases hi : IsChoicelessInaccessible (woodinLimitCardinal K)
  · simp only [woodinStageRule, ite_eq_right hz, ite_eq_right hsucc,
      ite_eq_right hzv, ite_eq_right hnsv, ite_eq_left hi, ite_eq_left (hiiff.mp hi),
      TransitiveZF.kpair_val, rank_forcingDirectCode_val hclosed,
      TransitiveZF.forcingFamilyNext_val, TransitiveZF.woodinLimitCardinal_val]
  · have hn : ¬IsChoicelessInaccessible (woodinLimitCardinal K.val) := fun hc ↦ hi (hiiff.mpr hc)
    have he := hI.agreement hzv (ordinal_limit_of_not_successor hnsv) (hK ▸ hn) hIξ hξ t s K rfl hs hK
    simp only [woodinStageRule, ite_eq_right hz, ite_eq_right hsucc,
      ite_eq_right hzv, ite_eq_right hnsv, ite_eq_right hi, ite_eq_right hn, TransitiveZF.kpair_val]
    rw [he.1, he.2, hs, hK]
end ZFVP
