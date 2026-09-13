import ZFVP.ModelTheory.WoodinCanonicalBoundInduction
import ZFVP.ModelTheory.WoodinCanonicalBoundThreadAt
import ZFVP.ModelTheory.WoodinCanonicalBoundRawBounded
import ZFVP.ModelTheory.WoodinCanonicalBoundStageInduction

/-! Closing the canonical quotient bound induction.

`woodinQuotientBound_all_stages` runs the bound induction with the inverse-limit case left as the
hypothesis `hinv`. `woodinQuotientBoundAt_inverse_normalized_decided` proves that case from a raw
thread comparison, and `woodinRawLiftBound_bounded` proves the comparison from the bound at the
coordinates below. The two fit together inside a single induction: at a limit coordinate `j` the
induction hypothesis already supplies the bound below `j`, which is exactly what the comparison
needs, so `hinv` can be discharged on the spot.

Part A does that merge. Part B feeds the merged bound back into the two comparison predicates
`WoodinInverseRawComparison` and `WoodinInverseStepRawComparison`, runs the outer transfinite
induction on the ambient index with those produced at each stage rather than assumed, and reaches
the exit datum of the Woodin iteration from the supercompactness of `δ` and the failure of choice
alone. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- `woodinBoundInverseStep_raw_premise` for a single ground thread `d`: the raw lift bound at the
coordinates of `j` above `i` gives the comparison premise of the decided inverse step, rewritten
into the `woodinIterationRec i` spelling of the base coordinate. -/
private theorem woodinBoundInverseStep_raw_premise_at {δ θ i j p f d e : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hj : j ∈ θ) (hij : i ∈ j) (h0 : ∅ ∈ j)
    (hd : d ∈ forcingInverseCodePoset j (woodinIterationPrefix j))
    (hde : ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (hmem : ∀ m ∈ j, woodinQuotientBoundRec θ i p f m ∈
      (forcingCodeP (woodinIterationPrefix θ)) ‘ m)
    (hbound : ∀ m ∈ j, i ⊆ m → IsWoodinRawLiftBoundAt θ i p f d e m) :
    ∀ r ∈ forcingInverseCodePoset j (woodinIterationPrefix j),
      ⟨r, woodinQuotientBoundHistory θ i p f j⟩ₖ ∈
        forcingInverseCodeOrder j (woodinIterationPrefix j) →
      ∀ b ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i,
        ⟨b, (forcingThreadCoordinate
          (forcingInverseCodePoset j (woodinIterationPrefix j)) i) ‘ r⟩ₖ ∈
          (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i →
        ⟨b, e⟩ₖ ∈ (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i →
        ⟨(woodinInverseCodeLift j (woodinIterationPrefix j) i) ‘ ⟨r, b⟩ₖ, d⟩ₖ ∈
          forcingInverseCodeOrder j (woodinIterationPrefix j) := by
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hij
  have hsub : j ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hj
  have hiθ : i ∈ θ := hsub i hij
  have hPi : (forcingCodeP (woodinIterationPrefix θ)) ‘ i =
      (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    woodinIterationPrefix_poset_value hs hiθ (mem_succ_self i)
  have hRi : (forcingCodeR (woodinIterationPrefix θ)) ‘ i =
      (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    woodinIterationPrefix_order_value hs hiθ (mem_succ_self i)
  intro r hr hrle b hb hbr hbe
  exact woodinInverseCodeLift_le_thread_at (p := p) (f := f) hs hj hij h0 hd (hRi ▸ hde) hmem
    hbound r hr hrle b (hPi ▸ hb) (hRi ▸ hbr) (hRi ▸ hbe)

/-! ### Part A: the bound induction with the inverse case discharged -/

/-- The canonical quotient bound at every stage, with the inverse-limit case proved inside the
induction instead of assumed.

This is `woodinQuotientBound_all_stages` with `hinv` replaced by the quotient closure of the raw
inverse limits below `θ`. At a limit coordinate `j` with a non-inaccessible stage cardinal, the
induction hypothesis gives the bound below `j`; that supplies the `hmem` and `hnorm` of
`woodinRawLiftBound_bounded`, whose conclusion is the comparison premise of
`woodinQuotientBoundAt_inverse_normalized_decided`. The two decision clauses are not hypotheses
here: the decided step hands them over together with the thread `d` and the condition `e`, and
they are passed straight through. -/
theorem woodinQuotientBound_all_stages_closed [Countable V] {δ θ i p α : V}
    [IsOrdinal θ] [IsOrdinal α]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hc : ∀ k ∈ θ, HasWoodinQuotientClosure (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hi : i ∈ θ) (hα : α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientSequence θ i p f.val α)
    (hclosure : ∀ j ∈ θ, ∀ k ∈ j, IterationQuotientClosedBelow
      (forcingInverseCode j (woodinIterationPrefix j)) k j
      ((woodinIterationCardinalPrefix j) ‘ k)) :
    ∀ j ∈ θ, IsWoodinNormalizedQuotientBoundAt θ i p f.val α j := by
  let := IsOrdinal.of_mem hi
  have hall := transfinite_induction
    (fun j : V ↦ j ∈ θ → IsWoodinNormalizedQuotientBoundAt θ i p f.val α j)
    (by definability) ?_
  · intro j hj
    let := IsOrdinal.of_mem hj
    exact hall (IsOrdinal.toOrdinal j) hj
  intro j ih hj
  have hprevn : ∀ l ∈ (j : V), IsWoodinNormalizedQuotientBoundAt θ i p f.val α l := by
    intro l hl
    let := IsOrdinal.of_mem hl
    exact ih (IsOrdinal.toOrdinal l) hl (IsOrdinal.toIsTransitive.mem_trans hl hj)
  have hprev : ∀ l ∈ (j : V), IsWoodinQuotientBoundAt θ i p f.val α l :=
    fun l hl ↦ (hprevn l hl).1
  by_cases hji : (j : V) ∈ succ i
  · rcases mem_succ_iff.mp hji with hje | hji'
    · subst hje
      exact woodinQuotientBoundAt_base_normalized hs hi hp f hf
    · exact woodinQuotientBoundAt_before_base_normalized hs hi hji' hp
  have hij : i ∈ (j : V) := by
    rcases IsOrdinal.mem_trichotomy i (j : V) with hij | he | hji'
    · exact hij
    · exact False.elim (hji (he ▸ mem_succ_self i))
    · exact False.elim (hji (mem_succ_iff.mpr (Or.inr hji')))
  by_cases hsucc : (j : V) = succ (⋃ˢ (j : V))
  · have hkprev : ⋃ˢ (j : V) ∈ (j : V) :=
      (congrArg (fun x : V ↦ (⋃ˢ (j : V)) ∈ x) hsucc).mpr (mem_succ_self (⋃ˢ (j : V)))
    let := IsOrdinal.of_mem hkprev
    have hkθ : succ (⋃ˢ (j : V)) ∈ θ := by rw [← hsucc]; exact hj
    have hik : i ∈ succ (⋃ˢ (j : V)) := by rw [← hsucc]; exact hij
    have hprev' : ∀ l ∈ succ (⋃ˢ (j : V)), IsWoodinQuotientBoundAt θ i p f.val α l := by
      rw [← hsucc]; exact hprev
    have hcl := hasWoodinQuotientClosure_prefix_of_stages hs hc hkθ
    rw [hsucc]
    exact woodinQuotientBoundAt_successor_normalized hs hkθ hik hcl hα hp f hf hprev'
  · by_cases hinac :
      IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix (j : V)))
    · exact woodinQuotientBoundAt_direct_normalized hs hj hij hsucc hinac hα hp f hf hprev
    · have hjsub : (j : V) ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hj
      have h0j : (∅ : V) ∈ (j : V) :=
        empty_mem_of_ordinal_ne_empty (by rintro he; rw [he] at hij; exact not_mem_empty hij)
      have hPi : (forcingCodeP (woodinIterationPrefix θ)) ‘ i =
          (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i :=
        woodinIterationPrefix_poset_value hs hi (mem_succ_self i)
      have hRi : (forcingCodeR (woodinIterationPrefix θ)) ‘ i =
          (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i :=
        woodinIterationPrefix_order_value hs hi (mem_succ_self i)
      refine woodinQuotientBoundAt_inverse_normalized_decided hs hj hij hsucc hinac
        (hclosure (j : V) hj) hα hp f hf hprev ?_
      intro d hd e he hde hc1 hc2
      have he' : e ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i := by rw [hPi]; exact he
      have hde' : ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i := by
        rw [hRi]; exact hde
      have hbound := woodinRawLiftBound_bounded hs hj hij hd he' hde'
        (fun m hm ↦ (hprev m hm).1) (fun m hm ↦ (hprevn m hm).2)
        (fun m hm ↦ woodinRawLiftBound_iterand_of_stages (i := i) hs m (hjsub m hm))
        (fun k hk _ ↦ hc1 (succ k) hk) (fun m hm _ _ _ ↦ hc2 m hm)
      exact woodinBoundInverseStep_raw_premise_at hs hj hij h0j hd hde
        (fun m hm ↦ (hprev m hm).1) hbound

/-! ### Part B: the two comparison premises, and the closed chain -/

/-- The thread comparison at the ambient index `θ`, proved from the closed bound induction.
Its `hmem` and `hnorm` come from `woodinQuotientBound_all_stages_closed`, and the two decision
clauses are the ones the predicate itself supplies. -/
theorem woodinInverseRawComparison_of_stages [Countable V] {δ θ i : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hc : ∀ k ∈ θ, HasWoodinQuotientClosure (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hi : i ∈ θ) (h0 : ∅ ∈ θ)
    (hclosure : ∀ j ∈ θ, ∀ k ∈ j, IterationQuotientClosedBelow
      (forcingInverseCode j (woodinIterationPrefix j)) k j
      ((woodinIterationCardinalPrefix j) ‘ k)) :
    WoodinInverseRawComparison θ i := by
  intro p hp f α hα hf d hd e he hde hc1 hc2
  have hηval : (woodinIterationCardinalPrefix θ) ‘ i =
      (kpair.π₂ (woodinIterationRec i)) ‘ i := woodinIterationCardinalPrefix_value_of_stages hs hi
  have hηord : IsOrdinal ((kpair.π₂ (woodinIterationRec i)) ‘ i) :=
    hηval ▸ ((woodinIterationPrefix_of_stages hs).inaccessible i hi).1
  have hαord : IsOrdinal α := IsOrdinal.of_mem hα
  have hall := woodinQuotientBound_all_stages_closed hs hc hi hα hp f hf hclosure
  exact woodinInverseCodeLift_le_thread_decided hs hi h0 hp f hf
    (fun m hm ↦ (hall m hm).1.1) (fun m hm ↦ (hall m hm).2) d e hd he hde ⟨hc1, hc2⟩

/-- The comparison premise of the decided inverse step at a coordinate `j ∈ θ`, proved from the
closed bound induction through `woodinRawLiftBound_bounded`.

Compared with the shape named in the task this carries three extra hypotheses, `hp`, `hα` and
`hf`. They are needed: `WoodinInverseStepRawComparison θ j i p f.val` speaks about the canonical
bound history of `p` and `f`, and that history is only under control when `p` is a condition of
the base coordinate and `f` is a name forced by `p` to be a quotient sequence below `α`. All three
are available at the point where this is used. -/
theorem woodinInverseStepRawComparison_of_stages [Countable V] {δ θ j i p α : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hc : ∀ k ∈ θ, HasWoodinQuotientClosure (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hj : j ∈ θ) (hij : i ∈ j)
    (hclosure : ∀ m ∈ θ, ∀ k ∈ m, IterationQuotientClosedBelow
      (forcingInverseCode m (woodinIterationPrefix m)) k m
      ((woodinIterationCardinalPrefix m) ‘ k))
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hα : α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i)
    (hf : ForcesWoodinQuotientSequence θ i p f.val α) :
    WoodinInverseStepRawComparison θ j i p f.val := by
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hij
  have hjsub : j ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hj
  have hiθ : i ∈ θ := hjsub i hij
  have h0j : (∅ : V) ∈ j :=
    empty_mem_of_ordinal_ne_empty (by rintro he; rw [he] at hij; exact not_mem_empty hij)
  have hηval : (woodinIterationCardinalPrefix θ) ‘ i =
      (kpair.π₂ (woodinIterationRec i)) ‘ i := woodinIterationCardinalPrefix_value_of_stages hs hiθ
  have hηord : IsOrdinal ((kpair.π₂ (woodinIterationRec i)) ‘ i) :=
    hηval ▸ ((woodinIterationPrefix_of_stages hs).inaccessible i hiθ).1
  have hαord : IsOrdinal α := IsOrdinal.of_mem hα
  have hPi : (forcingCodeP (woodinIterationPrefix θ)) ‘ i =
      (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    woodinIterationPrefix_poset_value hs hiθ (mem_succ_self i)
  have hRi : (forcingCodeR (woodinIterationPrefix θ)) ‘ i =
      (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i :=
    woodinIterationPrefix_order_value hs hiθ (mem_succ_self i)
  have hall := woodinQuotientBound_all_stages_closed hs hc hiθ hα hp f hf hclosure
  intro d hd e he hde hc1 hc2
  have he' : e ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i := by rw [hPi]; exact he
  have hde' : ⟨e, d ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i := by
    rw [hRi]; exact hde
  have hbound := woodinRawLiftBound_bounded hs hj hij hd he' hde'
    (fun m hm ↦ (hall m (hjsub m hm)).1.1) (fun m hm ↦ (hall m (hjsub m hm)).2)
    (fun m hm ↦ woodinRawLiftBound_iterand_of_stages (i := i) hs m (hjsub m hm))
    (fun k hk _ ↦ hc1 (succ k) hk) (fun m hm _ _ _ ↦ hc2 m hm)
  exact woodinBoundInverseStep_raw_premise_at hs hj hij h0j hd hde
    (fun m hm ↦ (hall m (hjsub m hm)).1.1) hbound

/-- Closure of the raw inverse quotient at every coordinate of `θ`, with no comparison premise
left. This is `woodinInverse_raw_closure_of_stages` with `hraw` and `hrawStep` produced at each
stage of the outer induction by the two theorems above. -/
theorem woodinInverse_raw_closure_of_stages_closed [Countable V] {δ θ : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hc : ∀ k ∈ θ, HasWoodinQuotientClosure (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k))) :
    ∀ i ∈ θ, IterationQuotientClosedBelow (forcingInverseCode θ (woodinIterationPrefix θ)) i θ
      ((woodinIterationCardinalPrefix θ) ‘ i) := by
  have hall := transfinite_induction
    (fun ξ : V ↦ ξ ⊆ θ → ∀ i ∈ ξ, IterationQuotientClosedBelow
      (forcingInverseCode ξ (woodinIterationPrefix ξ)) i ξ ((woodinIterationCardinalPrefix ξ) ‘ i))
    (by definability) ?_
  · exact hall (IsOrdinal.toOrdinal θ) (fun _ hx ↦ hx)
  intro ξ ih hξ i hi
  have hs' : ∀ k ∈ (ξ : V), IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)) := fun k hk ↦ hs k (hξ k hk)
  have hc' : ∀ k ∈ (ξ : V), HasWoodinQuotientClosure (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)) := fun k hk ↦ hc k (hξ k hk)
  have h0' : (∅ : V) ∈ (ξ : V) :=
    empty_mem_of_ordinal_ne_empty (by rintro he; rw [he] at hi; exact not_mem_empty hi)
  have hclo : ∀ m ∈ (ξ : V), ∀ k ∈ m, IterationQuotientClosedBelow
      (forcingInverseCode m (woodinIterationPrefix m)) k m
      ((woodinIterationCardinalPrefix m) ‘ k) := by
    intro m hm k hk
    let := IsOrdinal.of_mem hm
    exact ih (IsOrdinal.toOrdinal m) hm
      (fun x hx ↦ hξ x (IsOrdinal.toIsTransitive.transitive _ hm x hx)) k hk
  refine woodinInverse_raw_quotient_closedBelow_decided hs' hc' h0' hi ?_
    (woodinInverseRawComparison_of_stages hs' hc' hi h0' hclo)
  intro p hp f α hα hf j hj hij hlim hinac hprevn
  let := IsOrdinal.of_mem hj
  have hηval : (woodinIterationCardinalPrefix (ξ : V)) ‘ i =
      (kpair.π₂ (woodinIterationRec i)) ‘ i := woodinIterationCardinalPrefix_value_of_stages hs' hi
  have hηord : IsOrdinal ((kpair.π₂ (woodinIterationRec i)) ‘ i) :=
    hηval ▸ ((woodinIterationPrefix_of_stages hs').inaccessible i hi).1
  have hαord : IsOrdinal α := IsOrdinal.of_mem hα
  exact woodinQuotientBoundAt_inverse_normalized_decided hs' hj hij hlim hinac
    (hclo j hj) hα hp f hf (fun k hk ↦ (hprevn k hk).1)
    (woodinInverseStepRawComparison_of_stages hs' hc' hj hij hclo hp f hα hf)

/-- The joint stage induction with the inverse-limit hypothesis gone. This is
`woodinIteration_stages_of_canonical_bound` with the two comparison premises discharged by
`woodinInverse_raw_closure_of_stages_closed`. -/
theorem woodinIteration_stages_of_stages_closed [Countable V] {δ : V}
    (hδ : IsWoodinSupercompact δ) :
    ∀ θ ∈ δ,
      IsWoodinIteration δ (succ θ) (kpair.π₁ (woodinIterationRec θ))
        (kpair.π₂ (woodinIterationRec θ)) ∧
      HasWoodinQuotientClosure (succ θ) (kpair.π₁ (woodinIterationRec θ))
        (kpair.π₂ (woodinIterationRec θ)) := by
  let := hδ.inaccessible.1
  have hall := transfinite_induction
    (fun ξ : V ↦ ξ ∈ δ →
      IsWoodinIteration δ (succ ξ) (kpair.π₁ (woodinIterationRec ξ))
        (kpair.π₂ (woodinIterationRec ξ)) ∧
      HasWoodinQuotientClosure (succ ξ) (kpair.π₁ (woodinIterationRec ξ))
        (kpair.π₂ (woodinIterationRec ξ)))
    (by definability) ?_
  · intro θ hθ
    let := IsOrdinal.of_mem hθ
    exact hall (IsOrdinal.toOrdinal θ) hθ
  intro θ ih hθ
  have hs : ∀ i ∈ (θ : V), IsWoodinIteration δ (succ i) (kpair.π₁ (woodinIterationRec i))
      (kpair.π₂ (woodinIterationRec i)) := by
    intro i hi
    let := IsOrdinal.of_mem hi
    exact (ih (IsOrdinal.toOrdinal i) hi (IsOrdinal.toIsTransitive.mem_trans hi hθ)).1
  have hc : ∀ i ∈ (θ : V), HasWoodinQuotientClosure (succ i) (kpair.π₁ (woodinIterationRec i))
      (kpair.π₂ (woodinIterationRec i)) := by
    intro i hi
    let := IsOrdinal.of_mem hi
    exact (ih (IsOrdinal.toOrdinal i) hi (IsOrdinal.toIsTransitive.mem_trans hi hθ)).2
  have hp := woodinIterationPrefix_of_stages hs
  have hpc := woodinIterationPrefix_quotient_closure hs hc
  have hi : (θ : V) ≠ ∅ → (∀ i ∈ (θ : V), succ i ∈ (θ : V)) →
      ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix (θ : V))) →
      ∀ i ∈ (θ : V), IterationQuotientClosedBelow
        (forcingInverseCode (θ : V) (woodinIterationPrefix (θ : V))) i (θ : V)
        ((woodinIterationCardinalPrefix (θ : V)) ‘ i) :=
    fun _ _ _ ↦ woodinInverse_raw_closure_of_stages_closed hs hc
  rw [woodinIterationRec_rule]
  exact ⟨woodinStageRule_valid hδ hθ hp hpc hi, woodinStageRule_quotient_closure hδ hθ hp hpc hi⟩

/-- The exit datum for the Woodin iteration from a supercompact `δ` and the failure of internal
choice, with no premise about the inverse-limit stages left over. -/
theorem woodinIterationExit_of_stages_closed [Countable V] {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) : WoodinIterationExit δ := by
  let := hδ.inaccessible.1
  have hs := woodinIteration_stages_of_stages_closed hδ
  exact woodinIterationExit_of_stages hAC (fun θ hθ ↦ (hs θ hθ).1) (fun θ hθ ↦ (hs θ hθ).2)

end ZFVP
