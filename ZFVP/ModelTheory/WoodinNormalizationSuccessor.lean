import ZFVP.ModelTheory.NormalizedMapDefinability
import ZFVP.ModelTheory.WoodinIterationDefinability
import ZFVP.SetTheory.ForcingRetractionFixedPoints

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinNormalizationSuccessorMap (k s K m : V) : V :=
  let P := (forcingCodeP s) ‘ k
  let R := (forcingCodeR s) ‘ k
  let one := (forcingCodet s) ‘ k
  let κ := K ‘ k
  let c := woodinPrefixCutoff P R one κ
  let N := forcingMapFixedPoints P (m ‘ k)
  normalizedBaseTwoStepMap P R N (forcingOrderRestriction N R) one c
    (saturatedWoodinPrefixPosetName P R one κ c) (m ‘ k)

instance woodinNormalizationSuccessorMap_definable : ℒₛₑₜ-function₄[V] woodinNormalizationSuccessorMap := by
  unfold woodinNormalizationSuccessorMap
  dsimp only
  apply normalizedBaseTwoStepMap_comp
  · definability
  · definability
  · definability
  · definability
  · definability
  · apply Language.DefinableFunction₄.comp <;> definability
  · apply Language.DefinableFunction₅.comp
    · definability
    · definability
    · definability
    · definability
    · apply Language.DefinableFunction₄.comp <;> definability
  · definability

noncomputable def woodinNormalizationSuccessor (k s K m : V) : V :=
  forcingFamilyNext (succ k) m (woodinNormalizationSuccessorMap k s K m)

instance woodinNormalizationSuccessor_definable : ℒₛₑₜ-function₄[V] woodinNormalizationSuccessor := by
  unfold woodinNormalizationSuccessor
  apply Language.DefinableFunction₃.comp
  · definability
  · definability
  · apply Language.DefinableFunction₄.comp <;> definability

theorem woodinNormalizationSuccessor_old {k s K m i : V} (hi : i ∈ succ k) :
    (woodinNormalizationSuccessor k s K m) ‘ i = m ‘ i := forcingFamilyNext_old hi

theorem woodinNormalizationSuccessor_new (k s K m : V) :
    (woodinNormalizationSuccessor k s K m) ‘ (succ k) = woodinNormalizationSuccessorMap k s K m :=
  forcingFamilyNext_new _ _ _

theorem woodinNormalizationSuccessor_table (k s K m : V) :
    IsIterationTable (succ (succ k)) (woodinNormalizationSuccessor k s K m) :=
  forcingFamilyNext_table _ _ _

variable {k s K m N T : V}
local notation "P" => (forcingCodeP s) ‘ k
local notation "R" => (forcingCodeR s) ‘ k
local notation "o" => (forcingCodet s) ‘ k
local notation "κ" => K ‘ k
local notation "c" => woodinPrefixCutoff P R o κ
local notation "Q" => saturatedWoodinPrefixPosetName P R o κ c
local notation "S" => saturatedWoodinPrefixOrderName P R o κ c

theorem woodinNormalizationSuccessorMap_eq
    (hr : IsForcingRetraction N T P R (m ‘ k)) (hT : IsForcingPreorder N T) :
    woodinNormalizationSuccessorMap k s K m = normalizedBaseTwoStepMap P R N T o c Q (m ‘ k) := by
  unfold woodinNormalizationSuccessorMap
  dsimp only
  rw [hr.fixedPoints_eq, hr.orderRestriction_eq hT]

theorem woodinNormalizationSuccessorMap_retraction
    (hr : IsForcingRetraction N T P R (m ‘ k)) (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (ht : IsForcingTop P R o) (hone : o ∈ N) (hc : IsChoicelessInaccessible c) (hP : P ∈ hierarchy c)
    (hκc : κ ⊆ c) (he : ∀ p ∈ P, ⟨(m ‘ k) ‘ p, p⟩ₖ ∈ R ∧ ⟨p, (m ‘ k) ‘ p⟩ₖ ∈ R)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName o κ])) :
    IsForcingRetraction (normalizedNameTwoStep N T o c (nameAction (m ‘ k) Q))
      (nameTwoStepOrderOn N T (nameAction (m ‘ k) S) (normalizedNameTwoStep N T o c (nameAction (m ‘ k) Q)))
      ((forcingCodeP (woodinIterationSuccessor k s K)) ‘ (succ k))
      ((forcingCodeR (woodinIterationSuccessor k s K)) ‘ (succ k))
      (woodinNormalizationSuccessorMap k s K m) := by
  rw [woodinNormalizationSuccessorMap_eq hr hT]
  simpa only [woodinIterationSuccessor, forcingSuccessorCode_poset, forcingSuccessorCode_order] using
    saturatedWoodinPrefix_normalizedBase_retraction hr hR hT ht hone hc hP hκc he hκ

theorem woodinNormalizationSuccessorMap_prefix {z : V}
    (hr : IsForcingRetraction N T P R (m ‘ k)) (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (ht : IsForcingTop P R o) (hone : o ∈ N) (hc : IsChoicelessInaccessible c) (hP : P ∈ hierarchy c)
    (hκc : κ ⊆ c) (he : ∀ p ∈ P, ⟨(m ‘ k) ‘ p, p⟩ₖ ∈ R ∧ ⟨p, (m ‘ k) ‘ p⟩ₖ ∈ R)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName o κ]))
    (hz : z ∈ (forcingCodeP (woodinIterationSuccessor k s K)) ‘ (succ k)) :
    kpair.π₁ ((woodinNormalizationSuccessorMap k s K m) ‘ z) = (m ‘ k) ‘ (kpair.π₁ z) := by
  rw [woodinNormalizationSuccessorMap_eq hr hT]
  have hz' : z ∈ boundedNameTwoStep P R c Q := by
    simpa only [woodinIterationSuccessor, forcingSuccessorCode_poset,
      saturatedWoodinPrefix_twoStep_eq_bounded hR hc hP] using hz
  exact normalizedBaseTwoStepMap_prefix hr hR hT ht hone hc hP he
    (saturatedWoodinPrefix_iterand hR ht hc hP hκc hκ) hz'

theorem woodinNormalizationSuccessorMap_empty_tail {p : V}
    (hr : IsForcingRetraction N T P R (m ‘ k)) (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (ht : IsForcingTop P R o) (hone : o ∈ N) (hc : IsChoicelessInaccessible c) (hP : P ∈ hierarchy c)
    (hκc : κ ⊆ c) (he : ∀ p ∈ P, ⟨(m ‘ k) ‘ p, p⟩ₖ ∈ R ∧ ⟨p, (m ‘ k) ‘ p⟩ₖ ∈ R)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName o κ]))
    (hp : p ∈ P) :
    (woodinNormalizationSuccessorMap k s K m) ‘ ⟨p, ∅⟩ₖ = ⟨(m ‘ k) ‘ p, ∅⟩ₖ := by
  rw [woodinNormalizationSuccessorMap_eq hr hT]
  exact normalizedBaseTwoStepMap_empty_tail hr hR hT ht hone hc hP he
    (saturatedWoodinPrefix_iterand hR ht hc hP hκc hκ) hp

theorem IsWoodinIteration.normalizationSuccessor_inputs {Ω : V} [IsOrdinal k]
    (hΩ : IsWoodinSupercompact Ω) (h : IsWoodinIteration Ω (succ k) s K) :
    IsForcingPreorder P R ∧ IsForcingTop P R o ∧ IsChoicelessInaccessible c ∧ P ∈ hierarchy c ∧ κ ⊆ c ∧
      ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName o κ]) := by
  let := hΩ.inaccessible.1
  let x := woodinIterationStage s K k
  have hx := h.stage k (mem_succ_self k)
  have hs := h.small k (mem_succ_self k)
  have hb : woodinStageCardinal x ∈ Ω := by
    simpa only [x, woodinIterationStage, woodinStageCardinal_code] using h.bounded k (mem_succ_self k)
  have hPΩ := hs Ω hΩ.inaccessible hb
  have hRΩ := hx.order_mem_hierarchy hΩ.inaccessible.rankCriterion.2.2.1 hPΩ
  obtain ⟨d, _, hd⟩ := hΩ.strictPrefixCutoff hx.1 hx.2.1 hPΩ hRΩ hb hx.2.2.2.1 hx.2.2.2.2
  have hnew : IsWoodinPrefixCutoff P R o κ c := by
    simpa only [x, woodinIterationStage, woodinStagePoset_code, woodinStageOrder_code,
      woodinStageTop_code, woodinStageCardinal_code] using (woodinPrefixCutoff_spec hd).2.1
  have hPc : P ∈ hierarchy c := by
    have hmem : woodinStageCardinal (woodinIterationStage s K k) ∈ c := by
      simpa only [woodinIterationStage, woodinStageCardinal_code] using hnew.1
    simpa only [woodinIterationStage, woodinStagePoset_code] using hs c hnew.2.1 hmem
  let := hnew.2.1.1
  simp only [IsWoodinStage, woodinIterationStage, woodinStagePoset_code, woodinStageOrder_code,
    woodinStageTop_code, woodinStageCardinal_code] at hx
  exact ⟨hx.1, hx.2.1, hnew.2.1, hPc, IsOrdinal.toIsTransitive.transitive _ hnew.1, hx.2.2.2.1⟩

theorem IsWoodinIteration.normalizationSuccessor_retraction {Ω : V} [IsOrdinal k]
    (hΩ : IsWoodinSupercompact Ω) (h : IsWoodinIteration Ω (succ k) s K)
    (hr : IsForcingRetraction N T P R (m ‘ k)) (hT : IsForcingPreorder N T) (hone : o ∈ N)
    (he : ∀ p ∈ P, ⟨(m ‘ k) ‘ p, p⟩ₖ ∈ R ∧ ⟨p, (m ‘ k) ‘ p⟩ₖ ∈ R) :
    IsForcingRetraction (normalizedNameTwoStep N T o c (nameAction (m ‘ k) Q))
      (nameTwoStepOrderOn N T (nameAction (m ‘ k) S) (normalizedNameTwoStep N T o c (nameAction (m ‘ k) Q)))
      ((forcingCodeP (woodinIterationSuccessor k s K)) ‘ (succ k))
      ((forcingCodeR (woodinIterationSuccessor k s K)) ‘ (succ k))
      (woodinNormalizationSuccessorMap k s K m) := by
  obtain ⟨hR, ht, hc, hP, hκc, hκ⟩ := h.normalizationSuccessor_inputs hΩ
  exact woodinNormalizationSuccessorMap_retraction hr hR hT ht hone hc hP hκc he hκ

end ZFVP
