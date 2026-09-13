import ZFVP.ModelTheory.ForcingNormalizedSystem

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The original prefix-replacement operations preserve normalized conditions. -/
def IsForcingNormalizationLiftClosed (θ s m : V) : Prop :=
  ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j →
    ∀ a ∈ (forcingNormalizationCarriers θ s m) ‘ j,
    ∀ b ∈ (forcingNormalizationCarriers θ s m) ‘ i,
    ⟨b, ((forcingCodeπ s) ‘ ⟨i, j⟩ₖ) ‘ a⟩ₖ ∈ (forcingCodeR s) ‘ i →
      ((forcingCodeL s) ‘ ⟨i, j⟩ₖ) ‘ ⟨a, b⟩ₖ ∈ (forcingNormalizationCarriers θ s m) ‘ j

instance IsForcingNormalizationLiftClosed_definable :
    ℒₛₑₜ-relation₃[V] IsForcingNormalizationLiftClosed := by
  unfold IsForcingNormalizationLiftClosed
  definability

theorem forcingNormalizationCarriers_next_old {θ s m Q T ρ F M u n i : V} (hi : i ∈ θ) :
    (forcingNormalizationCarriers (succ θ) (forcingIterationCodeNext θ s Q T ρ F M u)
      (forcingFamilyNext θ m n)) ‘ i = (forcingNormalizationCarriers θ s m) ‘ i := by
  rw [forcingNormalizationCarriers_value (mem_succ_iff.mpr (Or.inr hi)),
    forcingNormalizationCarriers_value hi]
  simp only [forcingIterationCodeNext, forcingCodeP_code, forcingFamilyNext_old hi]

theorem forcingNormalizationCarriers_next_new (θ s m Q T ρ F M u n : V) :
    (forcingNormalizationCarriers (succ θ) (forcingIterationCodeNext θ s Q T ρ F M u)
      (forcingFamilyNext θ m n)) ‘ θ = forcingMapFixedPoints Q n := by
  rw [forcingNormalizationCarriers_value (mem_succ_self θ)]
  simp only [forcingIterationCodeNext, forcingCodeP_code, forcingFamilyNext_new]

theorem IsForcingNormalizationLiftClosed.extend {θ s m Q T ρ F M u n : V}
    (h : IsForcingNormalizationLiftClosed θ s m)
    (hc : ∀ i ∈ θ, ∀ a ∈ forcingMapFixedPoints Q n,
      ∀ b ∈ (forcingNormalizationCarriers θ s m) ‘ i,
      ⟨b, (ρ ‘ i) ‘ a⟩ₖ ∈ (forcingCodeR s) ‘ i →
        (M ‘ i) ‘ ⟨a, b⟩ₖ ∈ forcingMapFixedPoints Q n) :
    IsForcingNormalizationLiftClosed (succ θ) (forcingIterationCodeNext θ s Q T ρ F M u)
      (forcingFamilyNext θ m n) := by
  intro i hi j hj hij a ha b hb hle
  rcases mem_succ_iff.mp hj with rfl | hj
  · rw [forcingNormalizationCarriers_next_new] at ha ⊢
    rcases mem_succ_iff.mp hi with rfl | hi
    · rw [forcingNormalizationCarriers_next_new] at hb
      simp only [forcingIterationCodeNext, forcingCodeL_code, forcingMatrixNext_diagonal]
      rw [forcingIdentityLift_value (mem_sep_iff.mp ha).1 (mem_sep_iff.mp hb).1]
      exact hb
    · rw [forcingNormalizationCarriers_next_old hi] at hb
      simp only [forcingIterationCodeNext, forcingCodeπ_code, forcingCodeR_code,
        forcingMatrixNext_column hi, forcingFamilyNext_old hi] at hle
      simpa only [forcingIterationCodeNext, forcingCodeL_code, forcingMatrixNext_column hi]
        using hc i hi a ha b hb hle
  · have hiθ : i ∈ θ := by
      rcases mem_succ_iff.mp hi with rfl | hi
      · exact (mem_irrefl j (hij j hj)).elim
      · exact hi
    rw [forcingNormalizationCarriers_next_old hj] at ha ⊢
    rw [forcingNormalizationCarriers_next_old hiθ] at hb
    simp only [forcingIterationCodeNext, forcingCodeπ_code, forcingCodeR_code,
      forcingMatrixNext_old hi hj, forcingFamilyNext_old hiθ] at hle
    simpa only [forcingIterationCodeNext, forcingCodeL_code, forcingMatrixNext_old hi hj]
      using h i hiθ j hj hij a ha b hb hle

theorem forcingNormalization_singleton_liftClosed {s m : V}
    (h : IsForcingNormalizationFamily (succ ∅) s m) (hs : IsForcingIterationCode (succ ∅) s) :
    IsForcingNormalizationLiftClosed (succ ∅) s m := by
  intro i hi j hj hij a ha b hb hle
  have hi0 : i = ∅ := by simpa only [mem_succ_iff, not_mem_empty, or_false] using hi
  have hj0 : j = ∅ := by simpa only [mem_succ_iff, not_mem_empty, or_false] using hj
  subst i j
  have hl := hs.system.lifts.lift ∅ hi ∅ hj hij a (h.inclusion ∅ hj a ha)
    b (h.inclusion ∅ hi b hb) hle
  have he := hl.2.2
  rw [hs.system.split.projId hi hl.1] at he
  rwa [he]

theorem IsForcingNormalizationLiftClosed.code {θ s m : V} [IsOrdinal θ]
    (h : IsForcingNormalizationLiftClosed θ s m)
    (hn : IsForcingNormalizationFamily θ s m) (hs : IsForcingIterationCode θ s) :
    IsForcingIterationCode θ (forcingNormalizedCode θ s m) := forcingNormalized_code hn hs h

end ZFVP
