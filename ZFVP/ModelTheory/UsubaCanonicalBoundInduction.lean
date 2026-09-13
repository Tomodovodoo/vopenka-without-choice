import ZFVP.ModelTheory.UsubaBoundSuccessorStep
import ZFVP.ModelTheory.UsubaBoundLimitStep
import ZFVP.ModelTheory.UsubaClosureFromBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "T" => usubaForcingTower (V := V)

theorem usubaQuotientBoundAt_before_base_normalized {θ i p f α j : V} [IsOrdinal i]
    (hji : j ∈ i) (hp : p ∈ (T).P i) :
    IsUsubaNormalizedQuotientBoundAt θ i p f α j :=
  ⟨usubaQuotientBoundAt_before_base hji hp,
    fun hij ↦ False.elim (mem_asymm hji hij)⟩

/-- The internal induction for the canonical bound uses quotient closure only
at stages strictly below the source stage. -/
theorem usubaQuotientBound_all_stages [Countable V] {θ i p α : V}
    [IsOrdinal θ] [IsOrdinal i] [IsOrdinal α]
    (hiθ : i ⊆ θ)
    (hc : ∀ k ∈ θ, i ⊆ k → UsubaQuotientClosureAt i k)
    (hp : p ∈ (T).P i) (f : ForcingName ((T).P i))
    (hf : ForcesUsubaQuotientSequence θ i p f.val α) (hdc : ForcesUsubaDC i p α) :
    ∀ j ∈ succ θ, IsUsubaNormalizedQuotientBoundAt θ i p f.val α j := by
  have hall := transfinite_induction
    (fun j : V ↦ j ∈ succ θ → IsUsubaNormalizedQuotientBoundAt θ i p f.val α j)
    (by definability) ?_
  · intro j hj
    let := IsOrdinal.of_mem hj
    exact hall (IsOrdinal.toOrdinal j) hj
  intro j ih hj
  have hjθ : (j : V) ⊆ θ := IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hj)
  have hprevn : ∀ l ∈ (j : V), IsUsubaNormalizedQuotientBoundAt θ i p f.val α l := by
    intro l hl
    let := IsOrdinal.of_mem hl
    exact ih (IsOrdinal.toOrdinal l) hl (IsOrdinal.toIsTransitive.mem_trans hl hj)
  by_cases hji : (j : V) ∈ succ i
  · rcases mem_succ_iff.mp hji with hje | hji'
    · subst hje
      exact usubaQuotientBoundAt_base hiθ hp f hf
    · exact usubaQuotientBoundAt_before_base_normalized hji' hp
  have hij : i ∈ (j : V) := by
    rcases IsOrdinal.mem_trichotomy i (j : V) with hij | he | hji'
    · exact hij
    · exact False.elim (hji (he ▸ mem_succ_self i))
    · exact False.elim (hji (mem_succ_iff.mpr (Or.inr hji')))
  by_cases hsucc : (j : V) = succ (⋃ˢ (j : V))
  · have hkprev : ⋃ˢ (j : V) ∈ (j : V) :=
      (congrArg (fun x : V ↦ (⋃ˢ (j : V)) ∈ x) hsucc).mpr (mem_succ_self (⋃ˢ (j : V)))
    let := IsOrdinal.of_mem hkprev
    have hkθ : ⋃ˢ (j : V) ∈ θ := hjθ _ hkprev
    have hik : i ⊆ ⋃ˢ (j : V) := IsOrdinal.subset_iff.mpr (mem_succ_iff.mp (hsucc ▸ hij))
    have hprev : ∀ l ∈ succ (⋃ˢ (j : V)), IsUsubaQuotientBoundAt θ i p f.val α l := by
      rw [← hsucc]
      exact fun l hl ↦ (hprevn l hl).1
    rw [hsucc]
    exact usubaQuotientBoundAt_successor_normalized hik (hsucc ▸ hjθ) hp f hf
      (fun _ hG hpG ↦ forcesUsubaDC_semantics hdc hG hpG)
      (fun _ hG hpG ↦ usubaQuotientClosureAt_semantics hik (hc _ hkθ hik) hG
        (forcesUsubaDC_semantics hdc hG hpG)) hprev
  · exact usubaQuotientBoundAt_limit_normalized hij hjθ hsucc hp f hf hprevn

set_option maxHeartbeats 800000 in
/-- Every set-stage quotient in the actual Usuba iteration is closed through
each ordinal for which its base extension has dependent choice. -/
theorem usubaQuotientClosureAt_all [Countable V] {i j : V} [IsOrdinal i] [IsOrdinal j]
    (hij : i ⊆ j) : UsubaQuotientClosureAt i j := by
  have hall := transfinite_induction
    (fun j : V ↦ ∀ i : V, IsOrdinal i → i ⊆ j → UsubaQuotientClosureAt i j)
    (by definability) ?_
  · exact hall (IsOrdinal.toOrdinal j) i inferInstance hij
  intro j ih i hi hij
  let := hi
  apply usubaQuotientClosureAt_of_canonical_bounds hij
  intro α hα p hp f hf hdc
  let := hα
  exact (usubaQuotientBound_all_stages hij
    (fun k hk hik ↦ by
      let := IsOrdinal.of_mem hk
      exact ih (IsOrdinal.toOrdinal k) hk i hi hik)
    hp f hf hdc j (mem_succ_self (j : V))).1

theorem usubaQuotient_closedThrough [Countable V] {i j α : V}
    [IsOrdinal i] [IsOrdinal j] [IsOrdinal α] (hij : i ⊆ j)
    {G : Set V} (hG : IsExternalForcingGeneric ((T).P i) ((T).R i) G)
    (hDC : InternalDependentChoiceAt ((usubaStageContext i hG).check α)) :
    let A := usubaStageContext i hG
    IsForcingClosedThrough (A.projectionQuotient ((T).P j) ((T).projection i j))
      (forcingSeparativeOrder (A.projectionQuotient ((T).P j) ((T).projection i j))
        (A.projectionQuotientOrder ((T).P j) ((T).R j) ((T).projection i j))) (A.check α) :=
  usubaQuotientClosureAt_semantics hij (usubaQuotientClosureAt_all hij) hG hDC

end ZFVP
