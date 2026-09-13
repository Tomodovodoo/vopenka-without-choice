import ZFVP.ModelTheory.WoodinCoordinateTailEmpty

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

set_option maxHeartbeats 600000 in
theorem woodinBoundSuccessorTail_empty [Countable V] {δ θ i k p X : V} [IsOrdinal θ]
    (hs : ∀ l ∈ θ, IsWoodinIteration δ (succ l) (kpair.π₁ (woodinIterationRec l))
      (kpair.π₂ (woodinIterationRec l)))
    (hk : succ k ∈ θ) (hi : i ∈ succ k)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ∀ (A : ForcingContext V),
      A.P = (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i →
      A.R = (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i →
      A.one = (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i → p ∈ A.G →
      ∀ g : ForcingName A.P, g.val = f.val →
      A.ofName g ∈ A.check (forcingInverseCodePoset θ (woodinIterationPrefix θ)) ^ A.check X ∧
      ∀ a ∈ A.check X, ∀ d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ),
        (A.ofName g) ‘ a = A.check d → kpair.π₂ (d ‘ (succ k)) = ∅) :
    woodinBoundSuccessorTail θ i p f.val k = ∅ := by
  let := IsOrdinal.of_mem hk
  let := IsOrdinal.of_mem (mem_succ_self k)
  let := IsOrdinal.of_mem hi
  have hiθ := IsOrdinal.toIsTransitive.mem_trans hi hk
  have hkθ := IsOrdinal.toIsTransitive.mem_trans (mem_succ_self k) hk
  have hhist := woodinIterationHistory_of_stages
    (fun l hl ↦ hs l (IsOrdinal.toIsTransitive.mem_trans hl hk))
  have he := woodinIterationPrefix_successor hhist
  let s := woodinIterationPrefix (succ k)
  let K := woodinIterationCardinalPrefix (succ k)
  have h : IsWoodinIteration δ (succ k) s K := by
    simpa only [s, K, he.1, he.2] using hs k hkθ
  have hn : IsWoodinIteration δ (succ (succ k)) (woodinIterationSuccessor k s K)
      (woodinIterationCardinalNext k s K) := by
    have hh := hs (succ k) hk
    rw [woodinIterationRec_successor_of_history hhist, kpair.π₁_kpair, kpair.π₂_kpair] at hh
    simpa only [s, K, he.1, he.2] using hh
  let c := woodinPrefixCutoff ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k)
    ((forcingCodet s) ‘ k) (K ‘ k)
  have hnew : (woodinIterationCardinalNext k s K) ‘ (succ k) = c := by
    simp only [c, woodinIterationCardinalNext, forcingFamilyNext_new, woodinSuccessorStep,
      woodinSuccessorAt, woodinIterationStage, woodinStagePoset_code, woodinStageOrder_code,
      woodinStageTop_code, woodinStageCardinal_code]
  have hci : IsChoicelessInaccessible c := hnew ▸ hn.inaccessible (succ k) (mem_succ_self _)
  let := hci.1
  have hold : (woodinIterationCardinalNext k s K) ‘ k = K ‘ k := forcingFamilyNext_old (mem_succ_self k)
  have hκc : K ‘ k ∈ c := by
    simpa only [hnew, hold] using
      hn.increasing k (mem_succ_iff.mpr (Or.inr (mem_succ_self k))) (succ k)
        (mem_succ_self _) (mem_succ_self k)
  have hP : (forcingCodeP s) ‘ k ∈ hierarchy c := by
    have hh := h.small k (mem_succ_self k) c hci
    simp only [woodinIterationStage, woodinStageCardinal_code, woodinStagePoset_code] at hh
    exact hh hκc
  have hκ : ∀ q ∈ (forcingCodeP s) ‘ k, q ∈ forcingFormula ((forcingCodeP s) ‘ k)
      ((forcingCodeR s) ‘ k) regularCardinalFormula
      (standardTuple ![checkName ((forcingCodet s) ‘ k) (K ‘ k)]) := by
    simpa only [woodinIterationStage, woodinStagePoset_code, woodinStageOrder_code,
      woodinStageTop_code, woodinStageCardinal_code] using (h.stage k (mem_succ_self k)).2.2.2.1
  have hU := h.code.system.order.preorder k (mem_succ_self k)
  have ht := h.code.system.tops.top k (mem_succ_self k)
  have hiter := saturatedWoodinPrefix_iterand hU ht hci hP
    (IsOrdinal.toIsTransitive.transitive _ hκc) hκ
  have hRi := (hs i hiθ).code.system.order.preorder i (mem_succ_self i)
  have hoi := (hs i hiθ).code.system.tops.top i (mem_succ_self i)
  have hPi : (forcingCodeP s) ‘ i = (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    woodinIterationPrefix_poset_value
      (fun l hl ↦ hs l (IsOrdinal.toIsTransitive.mem_trans hl hk)) hi (mem_succ_self i)
  have hRie : (forcingCodeR s) ‘ i = (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    ((hs i hiθ).code.tableR.value_of_subset h.code.tableR
      (woodinIterationRec_extends_to_prefix hi).subR (mem_succ_self i)).symm
  have hsplit := h.code.system.splitProjection hi (mem_succ_self k)
    (IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hi))
  rw [hPi, hRie] at hsplit
  have hρ : forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) (succ k) ∈
      twoStepConditions ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k)
        (saturatedWoodinPrefixPosetName ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k)
          ((forcingCodet s) ‘ k) (K ‘ k) c) ∅ ^
        forcingInverseCodePoset θ (woodinIterationPrefix θ) := by
    apply definableGraph_mem_function_of_mapsTo
    intro d hd
    have hdj := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hd).2.1 (succ k) hk
    rw [woodinIterationPrefix_poset_value hs hk (mem_succ_self _),
      woodinIterationRec_successor_of_history hhist, kpair.π₁_kpair] at hdj
    simpa only [woodinIterationSuccessor, forcingSuccessorCode_poset, s, K, c, he.1, he.2] using hdj
  unfold woodinBoundSuccessorTail woodinBoundTailName
  dsimp only
  simp only [woodinStagePoset_code, woodinStageOrder_code, woodinStageTop_code, woodinStageCardinal_code]
  apply localSelectedUnion_action_empty_countable hRi hoi hU ht hsplit hp hiter
    ⟨woodinBoundCoordinateName θ i f.val (succ k), woodinBoundCoordinateName_isName _ _ _ _⟩
  intro G hG hpG
  let A : ForcingContext V := ⟨_, _, _, G, hRi, hoi, hG⟩
  obtain ⟨hfun, htail⟩ := hf A rfl rfl rfl hpG f rfl
  exact ⟨A.check X, A.woodinCoordinate_sequence_empty rfl rfl rfl f hρ hfun htail⟩

end ZFVP
