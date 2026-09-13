import ZFVP.ModelTheory.ActionSelectedUnionEmpty
import ZFVP.ModelTheory.WoodinUniformTailSupport

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Evaluation of the fixed coordinate name preserves the original selected
thread, so an empty ground tail gives an empty selected tail. -/
theorem ForcingContext.woodinCoordinate_sequence_empty
    {θ i j X T U Q t : V}
    (A : ForcingContext V)
    (hP : A.P = (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (hR : A.R = (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (ho : A.one = (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName A.P)
    (hρ : forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) j ∈
      twoStepConditions T U Q t ^ forcingInverseCodePoset θ (woodinIterationPrefix θ))
    (hf : A.ofName f ∈ A.check (forcingInverseCodePoset θ (woodinIterationPrefix θ)) ^ A.check X)
    (htail : ∀ a ∈ A.check X, ∀ d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ),
      (A.ofName f) ‘ a = A.check d → kpair.π₂ (d ‘ j) = ∅) :
    let μ : ForcingName A.P := ⟨woodinBoundCoordinateName θ i f.val j,
      by simpa only [← hP] using woodinBoundCoordinateName_isName θ i f.val j⟩
    A.ofName μ ∈ A.check (twoStepConditions T U Q t) ^ A.check X ∧
      ∀ a ∈ A.check X, ∀ c ∈ twoStepConditions T U Q t,
        (A.ofName μ) ‘ a = A.check c → kpair.π₂ c = ∅ := by
  let := IsFunction.of_mem hρ
  let D := forcingInverseCodePoset θ (woodinIterationPrefix θ)
  let ρ := forcingThreadCoordinate D j
  let μ : ForcingName A.P := ⟨woodinBoundCoordinateName θ i f.val j,
    by simpa only [← hP] using woodinBoundCoordinateName_isName θ i f.val j⟩
  have hv : A.ofName μ = compose (A.ofName f) (A.check ρ) := by
    have he := A.forcingCompositionName_value f ⟨checkName A.one ρ, checkName_isName A.top.1 _⟩
    change A.ofName ⟨forcingCompositionName A.P A.R f.val (checkName A.one ρ), _⟩ =
      compose (A.ofName f) (A.check ρ) at he
    simpa only [μ, woodinBoundCoordinateName, ← hP, ← hR, ← ho, ρ, D] using he
  dsimp only
  change A.ofName μ ∈ _ ∧ _
  have hρ' := (A.check_function_iff _ _ _).mpr hρ
  refine ⟨hv ▸ compose_function hf hρ', ?_⟩
  intro a ha c hc hac
  obtain ⟨d, hd, had⟩ := (A.mem_check_iff _ _).mp (function_value_mem hf ha)
  have hval : (A.ofName μ) ‘ a = A.check (d ‘ j) := by
    rw [hv, value_compose_of_mem_function hf hρ' ha, had,
      A.check_value ((domain_eq_of_mem_function hρ).symm ▸ hd), forcingThreadCoordinate_value hd]
  have hdc : d ‘ j = c := (A.check_eq_iff _ _).mp (hval.symm.trans hac)
  exact hdc ▸ htail a ha d hd had

theorem woodinBoundTailName_coordinate_empty [Countable V]
    {θ i j X x Q S π E p : V}
    (hR : IsForcingPreorder ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (ho : IsForcingTop ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hU : IsForcingPreorder (woodinStagePoset x) (woodinStageOrder x))
    (ht : IsForcingTop (woodinStagePoset x) (woodinStageOrder x) (woodinStageTop x))
    (hπ : IsForcingSplitProjection
      ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
      (woodinStagePoset x) (woodinStageOrder x) π E)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (hiter : IsForcingIterand (woodinStagePoset x) (woodinStageOrder x) Q S ∅)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hρ : forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) j ∈
      twoStepConditions (woodinStagePoset x) (woodinStageOrder x) Q ∅ ^
        forcingInverseCodePoset θ (woodinIterationPrefix θ))
    (hf : ∀ (G : Set V) (hG : IsExternalForcingGeneric
      ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) G), p ∈ G →
      let A : ForcingContext V := ⟨_, _, _, G, hR, ho, hG⟩
      A.ofName f ∈ A.check (forcingInverseCodePoset θ (woodinIterationPrefix θ)) ^ A.check X ∧
      ∀ a ∈ A.check X, ∀ d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ),
        (A.ofName f) ‘ a = A.check d → kpair.π₂ (d ‘ j) = ∅) :
    woodinBoundTailName x (E ‘ p) Q E (woodinBoundCoordinateName θ i f.val j) = ∅ := by
  apply localSelectedUnion_action_empty_countable hR ho hU ht hπ hp hiter
    ⟨woodinBoundCoordinateName θ i f.val j, woodinBoundCoordinateName_isName _ _ _ _⟩
  intro G hG hpG
  let A : ForcingContext V := ⟨_, _, _, G, hR, ho, hG⟩
  obtain ⟨hfun, htail⟩ := hf G hG hpG
  exact ⟨A.check X, A.woodinCoordinate_sequence_empty rfl rfl rfl f hρ hfun htail⟩

end ZFVP
