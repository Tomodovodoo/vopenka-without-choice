import ZFVP.ModelTheory.WoodinCanonicalBoundRawInduction
import ZFVP.ModelTheory.WoodinCanonicalBoundInverseIterand
import ZFVP.ModelTheory.WoodinCanonicalBoundDecision

/-! Discharging the iterand and decision premises of the raw lift bound.

`woodinRawLiftBound_all_stages` carries three premises that are not about the candidate `f`:
`hiter`, which asks that the packed inverse source stage at a limit coordinate is a two step
extension by an iterand, and the two decision premises `hdecideSucc` and `hdecideInv`, which ask
that the base condition `e` decides the coordinate name at a stage to be the corresponding
coordinate of the ground thread `d`.

`hiter` follows from `hs` alone by `woodinInverseStage_iterand`. The two decision premises are the
guarded per coordinate shapes of the two clauses that `woodinBound_decision_condition_uniform`
produces uniformly in the stage, so they follow from that pair by dropping the guards. This file
records both theorems with `hiter`, `hdecideSucc` and `hdecideInv` replaced by that single pair. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

section

variable {δ θ i p α : V} [IsOrdinal θ] [IsOrdinal α]

/-- The successor clause of `woodinBound_decision_condition_uniform`: at every stage `j ∈ θ` and in
every generic filter containing `e`, the coordinate name at `j` is a function on some `X` whose
value at some point of `X` is the check of `d ‘ j`. Written in the coordinate `i` spelling that
`woodinIterationRec` gives. -/
abbrev WoodinBoundDecidesDirect (θ i f d e : V) : Prop :=
  ∀ j ∈ θ, ∀ (G' : Set V) (hG' : IsExternalForcingGeneric
      ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) G')
    (hR : IsForcingPreorder ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (ho : IsForcingTop ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)), e ∈ G' →
    let A : ForcingContext V := ⟨_, _, _, G', hR, ho, hG'⟩
    let μ : ForcingName A.P := ⟨woodinBoundCoordinateName θ i f j,
      woodinBoundCoordinateName_isName θ i f j⟩
    ∃ X b : A.Model,
      A.ofName μ ∈ A.check ((forcingCodeP (woodinIterationPrefix θ)) ‘ j) ^ X ∧
        b ∈ X ∧ (A.ofName μ) ‘ b = A.check (d ‘ j)

/-- The inverse clause of `woodinBound_decision_condition_uniform`: the same decision, stated in the
prefix spelling of the coordinate `i` poset and for an arbitrary name equal to the coordinate
name. -/
abbrev WoodinBoundDecidesPrefix (θ i f d e : V) : Prop :=
  ∀ j ∈ θ, ∀ (G' : Set V) (hG' : IsExternalForcingGeneric
      ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
      ((forcingCodeR (woodinIterationPrefix θ)) ‘ i) G'), e ∈ G' →
    ∀ (hRi : IsForcingPreorder ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
        ((forcingCodeR (woodinIterationPrefix θ)) ‘ i))
      (hti : IsForcingTop ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
        ((forcingCodeR (woodinIterationPrefix θ)) ‘ i)
        ((forcingCodet (woodinIterationPrefix θ)) ‘ i))
      (μ : ForcingName ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)),
      μ.val = woodinBoundCoordinateName θ i f j →
      let A : ForcingContext V := ⟨_, _, _, G', hRi, hti, hG'⟩
      ∃ X b : A.Model, A.ofName μ ∈
          A.check ((forcingCodeP (woodinIterationPrefix θ)) ‘ j) ^ X ∧
        b ∈ X ∧ (A.ofName μ) ‘ b = A.check (d ‘ j)

/-- `hiter` of `woodinRawLiftBound_all_stages` holds for the Woodin prefix as soon as every stage
below `θ` is a valid Woodin iteration. The extra guard `i ∈ j` supplies the nonemptiness of `j`
that `woodinInverseStage_iterand` asks for. -/
theorem woodinRawLiftBound_iterand_of_stages
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k))) :
    ∀ j ∈ θ, i ∈ j → j ≠ succ (⋃ˢ j) →
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
              (woodinLimitCardinal (woodinIterationCardinalPrefix j))))) ∅ := by
  intro j hj hij hlim hinac
  exact woodinInverseStage_iterand hs hj (fun h ↦ not_mem_empty (h ▸ hij)) hlim hinac

/-- `hdecideSucc` of `woodinRawLiftBound_all_stages` is the successor clause of the decision pair,
with the stage restricted to a successor ordinal in `θ`. -/
theorem woodinRawLiftBound_decideSucc_of_decides {f d e : V}
    (h : WoodinBoundDecidesDirect θ i f d e) :
    ∀ k, succ k ∈ θ → i ∈ succ k →
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
            a ∈ X ∧ (A.ofName μ) ‘ a = A.check (d ‘ (succ k)) :=
  fun k hk _ ↦ h (succ k) hk

/-- `hdecideInv` of `woodinRawLiftBound_all_stages` is the inverse clause of the decision pair,
with the stage restricted to the non inaccessible limit coordinates above `i`. -/
theorem woodinRawLiftBound_decideInv_of_decides {f d e : V}
    (h : WoodinBoundDecidesPrefix θ i f d e) :
    ∀ j ∈ θ, i ∈ j → j ≠ succ (⋃ˢ j) →
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
            a ∈ X ∧ (A.ofName μ) ‘ a = A.check (d ‘ j) :=
  fun j hj _ _ _ ↦ h j hj

set_option maxHeartbeats 1000000 in
/-- `woodinRawLiftBound_all_stages` with the iterand premise proved from `hs` and the two decision
premises replaced by the single pair of clauses that `woodinBound_decision_condition_uniform`
delivers. What remains are the candidate side premises `hmem` and `hnorm` about the canonical
quotient bound of `f`. -/
theorem woodinRawLiftBound_all_stages_decided [Countable V]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hi : i ∈ θ) (h0 : ∅ ∈ θ)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientSequence θ i p f.val α)
    (hmem : ∀ j ∈ θ, woodinQuotientBoundRec θ i p f.val j ∈
      (forcingCodeP (woodinIterationPrefix θ)) ‘ j)
    (hnorm : ∀ j ∈ θ, IsWoodinBoundNormalizationAt θ i p f.val j)
    (d e : V) (hd : d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ))
    (he : e ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i)
    (hde : ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i)
    (hdec : WoodinBoundDecidesDirect θ i f.val d e ∧ WoodinBoundDecidesPrefix θ i f.val d e) :
    ∀ j ∈ θ, i ⊆ j → IsWoodinRawLiftBoundAt θ i p f.val d e j :=
  woodinRawLiftBound_all_stages hs hi hd he hde hmem hnorm
    (woodinRawLiftBound_iterand_of_stages hs)
    (woodinRawLiftBound_decideSucc_of_decides hdec.1)
    (woodinRawLiftBound_decideInv_of_decides hdec.2)

set_option maxHeartbeats 1000000 in
/-- The thread comparison consumed by `woodinInverse_raw_quotient_closedBelow_decided`, with the
iterand premise proved and the two decision premises replaced by the decision pair. -/
theorem woodinInverseCodeLift_le_thread_decided [Countable V]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hi : i ∈ θ) (h0 : ∅ ∈ θ)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientSequence θ i p f.val α)
    (hmem : ∀ j ∈ θ, woodinQuotientBoundRec θ i p f.val j ∈
      (forcingCodeP (woodinIterationPrefix θ)) ‘ j)
    (hnorm : ∀ j ∈ θ, IsWoodinBoundNormalizationAt θ i p f.val j)
    (d e : V) (hd : d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ))
    (he : e ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i)
    (hde : ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i)
    (hdec : WoodinBoundDecidesDirect θ i f.val d e ∧ WoodinBoundDecidesPrefix θ i f.val d e) :
    ∀ r ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ),
      ⟨r, woodinQuotientBoundHistory θ i p f.val θ⟩ₖ ∈
        forcingInverseCodeOrder θ (woodinIterationPrefix θ) →
      ∀ b ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i,
        ⟨b, (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i) ‘ r⟩ₖ
          ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i →
        ⟨b, e⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i →
        ⟨(woodinInverseCodeLift θ (woodinIterationPrefix θ) i) ‘ ⟨r, b⟩ₖ, d⟩ₖ
          ∈ forcingInverseCodeOrder θ (woodinIterationPrefix θ) :=
  woodinInverseCodeLift_le_thread_of_stages hs hi h0 hd he hde hmem hnorm
    (woodinRawLiftBound_iterand_of_stages hs)
    (woodinRawLiftBound_decideSucc_of_decides hdec.1)
    (woodinRawLiftBound_decideInv_of_decides hdec.2)

end

end ZFVP
