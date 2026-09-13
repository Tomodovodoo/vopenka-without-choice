import ZFVP.ModelTheory.WoodinCanonicalBoundRawOrder
import ZFVP.ModelTheory.WoodinCanonicalBoundRawSuccessor
import ZFVP.ModelTheory.WoodinCanonicalBoundRawInverse
import ZFVP.ModelTheory.WoodinCanonicalBoundInduction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

set_option maxHeartbeats 1000000 in
/-- Transfinite induction assembling the four raw-order steps. From the base coordinate `i`
upward the lift of any condition below the canonical quotient bound, taken below a base
condition, stays below the selected ground thread `d`. The successor and packed-limit steps
need a decision premise about the coordinate name; it is carried here in exactly the shape the
two step lemmas consume, split into the successor shape (`hdecideSucc`) and the packed-limit
shape (`hdecideInv`). -/
theorem woodinRawLiftBound_all_stages [Countable V] {δ θ i p f d e : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hi : i ∈ θ)
    (hd : d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ))
    (he : e ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i)
    (hde : ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i)
    (hmem : ∀ j ∈ θ, woodinQuotientBoundRec θ i p f j ∈
      (forcingCodeP (woodinIterationPrefix θ)) ‘ j)
    (hnorm : ∀ j ∈ θ, IsWoodinBoundNormalizationAt θ i p f j)
    (hiter : ∀ j ∈ θ, i ∈ j → j ≠ succ (⋃ˢ j) →
      ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)) →
      IsForcingIterand (forcingInverseCodePoset j (woodinIterationPrefix j))
        (forcingInverseCodeOrder j (woodinIterationPrefix j))
        (forcingInverseCollapseName j (woodinIterationPrefix j)
          (forcingInverseSourceCutoff j (woodinIterationPrefix j)
            (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
          (forcingInverseHartogsName j (woodinIterationPrefix j)
            (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
          (forcingInverseRestorationName j (woodinIterationPrefix j)
            (woodinLimitCardinal (woodinIterationCardinalPrefix j))))
        (reverseInclusionOrderName (forcingInverseCodePoset j (woodinIterationPrefix j))
          (forcingInverseCodeOrder j (woodinIterationPrefix j))
          (forcingInverseCollapseName j (woodinIterationPrefix j)
            (forcingInverseSourceCutoff j (woodinIterationPrefix j)
              (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
            (forcingInverseHartogsName j (woodinIterationPrefix j)
              (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
            (forcingInverseRestorationName j (woodinIterationPrefix j)
              (woodinLimitCardinal (woodinIterationCardinalPrefix j))))) ∅)
    (hdecideSucc : ∀ k, succ k ∈ θ → i ∈ succ k →
      ∀ (G : Set V) (hG : IsExternalForcingGeneric
          ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
          ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) G)
        (hR : IsForcingPreorder ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
          ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i))
        (ho : IsForcingTop ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
          ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
          ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)), e ∈ G →
        let A : ForcingContext V := ⟨_, _, _, G, hR, ho, hG⟩
        let μ : ForcingName A.P := ⟨woodinBoundCoordinateName θ i f (succ k),
          woodinBoundCoordinateName_isName θ i f (succ k)⟩
        ∃ X a : A.Model,
          A.ofName μ ∈ A.check ((forcingCodeP (woodinIterationPrefix θ)) ‘ (succ k)) ^ X ∧
            a ∈ X ∧ (A.ofName μ) ‘ a = A.check (d ‘ (succ k)))
    (hdecideInv : ∀ j ∈ θ, i ∈ j → j ≠ succ (⋃ˢ j) →
      ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)) →
      ∀ (G : Set V) (hG : IsExternalForcingGeneric
          ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
          ((forcingCodeR (woodinIterationPrefix θ)) ‘ i) G), e ∈ G →
        ∀ (hRi : IsForcingPreorder ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
            ((forcingCodeR (woodinIterationPrefix θ)) ‘ i))
          (hti : IsForcingTop ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
            ((forcingCodeR (woodinIterationPrefix θ)) ‘ i)
            ((forcingCodet (woodinIterationPrefix θ)) ‘ i))
          (μ : ForcingName ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)),
          μ.val = woodinBoundCoordinateName θ i f j →
          let A : ForcingContext V := ⟨_, _, _, G, hRi, hti, hG⟩
          ∃ X a : A.Model, A.ofName μ ∈
              A.check ((forcingCodeP (woodinIterationPrefix θ)) ‘ j) ^ X ∧
            a ∈ X ∧ (A.ofName μ) ‘ a = A.check (d ‘ j)) :
    ∀ j ∈ θ, i ⊆ j → IsWoodinRawLiftBoundAt θ i p f d e j := by
  let := IsOrdinal.of_mem hi
  have hall := transfinite_induction
    (fun j : V ↦ j ∈ θ → i ⊆ j → IsWoodinRawLiftBoundAt θ i p f d e j)
    (by definability) ?_
  · intro j hj hij
    let := IsOrdinal.of_mem hj
    exact hall (IsOrdinal.toOrdinal j) hj hij
  intro j ih hj hsub
  have hprev : ∀ m ∈ (j : V), i ⊆ m → IsWoodinRawLiftBoundAt θ i p f d e m := by
    intro m hm him
    let := IsOrdinal.of_mem hm
    exact ih (IsOrdinal.toOrdinal m) hm (IsOrdinal.toIsTransitive.mem_trans hm hj) him
  rcases IsOrdinal.subset_iff.mp hsub with rfl | hij
  · exact isWoodinRawLiftBoundAt_base hs hi hde
  by_cases hsucc : (j : V) = succ (⋃ˢ (j : V))
  · have hkprev : ⋃ˢ (j : V) ∈ (j : V) :=
      (congrArg (fun x : V ↦ (⋃ˢ (j : V)) ∈ x) hsucc).mpr (mem_succ_self (⋃ˢ (j : V)))
    let := IsOrdinal.of_mem hkprev
    have hkθ : succ (⋃ˢ (j : V)) ∈ θ := by rw [← hsucc]; exact hj
    have hik : i ∈ succ (⋃ˢ (j : V)) := by rw [← hsucc]; exact hij
    have hiksub : i ⊆ ⋃ˢ (j : V) := IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hik)
    have hprevk : IsWoodinRawLiftBoundAt θ i p f d e (⋃ˢ (j : V)) :=
      hprev _ hkprev hiksub
    have hmem' : ∀ l ∈ succ (succ (⋃ˢ (j : V))),
        woodinQuotientBoundRec θ i p f l ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ l := by
      intro l hl
      rcases mem_succ_iff.mp hl with rfl | hl
      · exact hmem _ hkθ
      · exact hmem l (IsOrdinal.toIsTransitive.mem_trans hl hkθ)
    rw [hsucc]
    unfold IsWoodinRawLiftBoundAt
    dsimp only
    exact woodinRawLift_successor hs hkθ hik hd hmem' (hnorm _ hkθ) hprevk
      (hdecideSucc _ hkθ hik)
  by_cases hinac :
      IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix (j : V)))
  · exact isWoodinRawLiftBoundAt_direct hs hj hij hsucc hinac hd hde hprev
  have hmem' : ∀ l ∈ succ (j : V),
      woodinQuotientBoundRec θ i p f l ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ l := by
    intro l hl
    rcases mem_succ_iff.mp hl with rfl | hl
    · exact hmem _ hj
    · exact hmem l (IsOrdinal.toIsTransitive.mem_trans hl hj)
  unfold IsWoodinRawLiftBoundAt
  dsimp only
  exact woodinRawLift_inverse hs hj hij hsucc hinac hd he hde
    (hiter _ hj hij hsucc hinac) hmem' (hnorm _ hj)
    (fun m hm him ↦ hprev m hm him) (hdecideInv _ hj hij hsucc hinac)

set_option maxHeartbeats 1000000 in
/-- The canonical lift of any thread below the whole bound history, taken below a base
condition, is below the selected ground thread `d` in the raw inverse-limit order at `θ`. -/
theorem woodinInverseCodeLift_le_thread_of_stages [Countable V] {δ θ i p f d e : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hi : i ∈ θ) (h0 : ∅ ∈ θ)
    (hd : d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ))
    (he : e ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i)
    (hde : ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i)
    (hmem : ∀ j ∈ θ, woodinQuotientBoundRec θ i p f j ∈
      (forcingCodeP (woodinIterationPrefix θ)) ‘ j)
    (hnorm : ∀ j ∈ θ, IsWoodinBoundNormalizationAt θ i p f j)
    (hiter : ∀ j ∈ θ, i ∈ j → j ≠ succ (⋃ˢ j) →
      ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)) →
      IsForcingIterand (forcingInverseCodePoset j (woodinIterationPrefix j))
        (forcingInverseCodeOrder j (woodinIterationPrefix j))
        (forcingInverseCollapseName j (woodinIterationPrefix j)
          (forcingInverseSourceCutoff j (woodinIterationPrefix j)
            (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
          (forcingInverseHartogsName j (woodinIterationPrefix j)
            (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
          (forcingInverseRestorationName j (woodinIterationPrefix j)
            (woodinLimitCardinal (woodinIterationCardinalPrefix j))))
        (reverseInclusionOrderName (forcingInverseCodePoset j (woodinIterationPrefix j))
          (forcingInverseCodeOrder j (woodinIterationPrefix j))
          (forcingInverseCollapseName j (woodinIterationPrefix j)
            (forcingInverseSourceCutoff j (woodinIterationPrefix j)
              (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
            (forcingInverseHartogsName j (woodinIterationPrefix j)
              (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
            (forcingInverseRestorationName j (woodinIterationPrefix j)
              (woodinLimitCardinal (woodinIterationCardinalPrefix j))))) ∅)
    (hdecideSucc : ∀ k, succ k ∈ θ → i ∈ succ k →
      ∀ (G : Set V) (hG : IsExternalForcingGeneric
          ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
          ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) G)
        (hR : IsForcingPreorder ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
          ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i))
        (ho : IsForcingTop ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
          ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
          ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)), e ∈ G →
        let A : ForcingContext V := ⟨_, _, _, G, hR, ho, hG⟩
        let μ : ForcingName A.P := ⟨woodinBoundCoordinateName θ i f (succ k),
          woodinBoundCoordinateName_isName θ i f (succ k)⟩
        ∃ X a : A.Model,
          A.ofName μ ∈ A.check ((forcingCodeP (woodinIterationPrefix θ)) ‘ (succ k)) ^ X ∧
            a ∈ X ∧ (A.ofName μ) ‘ a = A.check (d ‘ (succ k)))
    (hdecideInv : ∀ j ∈ θ, i ∈ j → j ≠ succ (⋃ˢ j) →
      ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)) →
      ∀ (G : Set V) (hG : IsExternalForcingGeneric
          ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
          ((forcingCodeR (woodinIterationPrefix θ)) ‘ i) G), e ∈ G →
        ∀ (hRi : IsForcingPreorder ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
            ((forcingCodeR (woodinIterationPrefix θ)) ‘ i))
          (hti : IsForcingTop ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
            ((forcingCodeR (woodinIterationPrefix θ)) ‘ i)
            ((forcingCodet (woodinIterationPrefix θ)) ‘ i))
          (μ : ForcingName ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)),
          μ.val = woodinBoundCoordinateName θ i f j →
          let A : ForcingContext V := ⟨_, _, _, G, hRi, hti, hG⟩
          ∃ X a : A.Model, A.ofName μ ∈
              A.check ((forcingCodeP (woodinIterationPrefix θ)) ‘ j) ^ X ∧
            a ∈ X ∧ (A.ofName μ) ‘ a = A.check (d ‘ j)) :
    ∀ r ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ),
      ⟨r, woodinQuotientBoundHistory θ i p f θ⟩ₖ ∈
        forcingInverseCodeOrder θ (woodinIterationPrefix θ) →
      ∀ b ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i,
        ⟨b, (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i) ‘ r⟩ₖ
          ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i →
        ⟨b, e⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i →
        ⟨(woodinInverseCodeLift θ (woodinIterationPrefix θ) i) ‘ ⟨r, b⟩ₖ, d⟩ₖ
          ∈ forcingInverseCodeOrder θ (woodinIterationPrefix θ) :=
  woodinInverseCodeLift_le_thread hs hi h0 hd hde hmem
    (woodinRawLiftBound_all_stages hs hi hd he hde hmem hnorm hiter hdecideSucc hdecideInv)

end ZFVP
