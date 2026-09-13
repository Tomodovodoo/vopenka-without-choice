import ZFVP.ModelTheory.WoodinCoordinateTailEmpty
import ZFVP.ModelTheory.InverseSplitProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinBoundInverseTail_empty [Countable V] {δ θ i k p X : V} [IsOrdinal θ]
    (hs : ∀ l ∈ θ, IsWoodinIteration δ (succ l) (kpair.π₁ (woodinIterationRec l))
      (kpair.π₂ (woodinIterationRec l)))
    (hk : k ∈ θ) (hi : i ∈ k) (hlim : k ≠ succ (⋃ˢ k))
    (hinac : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix k)))
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ∀ (A : ForcingContext V),
      A.P = (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i →
      A.R = (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i →
      A.one = (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i → p ∈ A.G →
      ∀ g : ForcingName A.P, g.val = f.val →
      A.ofName g ∈ A.check (forcingInverseCodePoset θ (woodinIterationPrefix θ)) ^ A.check X ∧
      ∀ a ∈ A.check X, ∀ d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ),
        (A.ofName g) ‘ a = A.check d → kpair.π₂ (d ‘ k) = ∅) :
    woodinBoundInverseTail θ i p f.val k = ∅ := by
  let := IsOrdinal.of_mem hk
  let := IsOrdinal.of_mem hi
  have hiθ := IsOrdinal.toIsTransitive.mem_trans hi hk
  have h0 : k ≠ ∅ := by rintro rfl; exact not_mem_empty hi
  have h0k : (∅ : V) ∈ k := (IsOrdinal.subset_iff.mp (empty_subset k)).resolve_left
    (fun he ↦ h0 he.symm)
  let s := woodinIterationPrefix k
  let γ := woodinLimitCardinal (woodinIterationCardinalPrefix k)
  let c := forcingInverseSourceCutoff k s γ
  let Q := forcingInverseCollapseName k s c (forcingInverseHartogsName k s γ)
    (forcingInverseRestorationName k s γ)
  have h := woodinIterationPrefix_of_stages
    (fun l hl ↦ hs l (IsOrdinal.toIsTransitive.mem_trans hl hk))
  have col := h.code.system.inverseColumn h0k h.code.subset_universe
  have hU : IsForcingPreorder (forcingInverseCodePoset k s) (forcingInverseCodeOrder k s) := col.order.preorder
  have ht : IsForcingTop (forcingInverseCodePoset k s) (forcingInverseCodeOrder k s)
      (forcingInverseCodeTop k s) := col.tops.top
  have hRi := (hs i hiθ).code.system.order.preorder i (mem_succ_self i)
  have hoi := (hs i hiθ).code.system.tops.top i (mem_succ_self i)
  have hPi : (forcingCodeP s) ‘ i = (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    woodinIterationPrefix_poset_value
      (fun l hl ↦ hs l (IsOrdinal.toIsTransitive.mem_trans hl hk)) hi (mem_succ_self i)
  have hRie : (forcingCodeR s) ‘ i = (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    ((hs i hiθ).code.tableR.value_of_subset h.code.tableR
      (woodinIterationRec_extends_to_prefix hi).subR (mem_succ_self i)).symm
  have hsplit := forcingInverseLimit_splitProjection h.code.system.split h.code.system.lifts
    hi h.code.subset_universe (fun a ha b hb hab ↦ h.code.system.splitProjection ha hb hab)
  change IsForcingSplitProjection ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
    (forcingInverseCodePoset k s) (forcingInverseCodeOrder k s) _ _ at hsplit
  rw [hPi, hRie] at hsplit
  have hQ : IsForcingName (forcingInverseCodePoset k s) Q := forcingSaturatedName_isName _ _ _ _
  have hnames : ∀ ν ∈ twoStepNames Q ∅, IsForcingName (forcingInverseCodePoset k s) ν := by
    intro ν hν
    rcases mem_union_iff.mp hν with hν | hν
    · obtain ⟨q, hq⟩ := mem_domain_iff.mp hν
      exact forcingName_subname hQ hq
    · exact (mem_singleton_iff.mp hν).symm ▸ empty_forcingName _
  have hρ : forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) k ∈
      twoStepConditions (forcingInverseCodePoset k s) (forcingInverseCodeOrder k s) Q ∅ ^
        forcingInverseCodePoset θ (woodinIterationPrefix θ) := by
    apply definableGraph_mem_function_of_mapsTo
    intro d hd
    have hdj := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hd).2.1 k hk
    rw [woodinIterationPrefix_poset_value hs hk (mem_succ_self _),
      woodinIterationRec_inverse h0 hlim hinac, kpair.π₁_kpair] at hdj
    simpa only [woodinInverseSourceCode, forcingInverseSourceCollapseCode, forcingInverseCollapseCode,
      forcingInverseTwoStepCode, forcingTwoStepColumnCode, forcingIterationCodeNext,
      forcingCodeP_code, forcingFamilyNext_new, s, γ, c, Q, forcingInverseCodePoset,
      forcingInverseCodeOrder] using hdj
  unfold woodinBoundInverseTail woodinBoundTailName
  dsimp only
  simp only [woodinStagePoset_code, woodinStageOrder_code, woodinStageTop_code, woodinStageCardinal_code]
  apply localSelectedUnion_action_empty_of_names_countable hRi hoi hU ht hsplit hp hnames
    ⟨woodinBoundCoordinateName θ i f.val k, woodinBoundCoordinateName_isName _ _ _ _⟩
  intro G hG hpG
  let A : ForcingContext V := ⟨_, _, _, G, hRi, hoi, hG⟩
  obtain ⟨hfun, htail⟩ := hf A rfl rfl rfl hpG f rfl
  exact ⟨A.check X, A.woodinCoordinate_sequence_empty rfl rfl rfl f hρ hfun htail⟩

end ZFVP
