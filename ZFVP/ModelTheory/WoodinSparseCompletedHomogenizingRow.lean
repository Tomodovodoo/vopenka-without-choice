import ZFVP.ModelTheory.WoodinSparseCompletedDisplacement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSparseCompletedHomogenizingMap (θ f p q : V) : V :=
  let e := woodinSparseCompletedAutomorphism θ (woodinSparsePrefixCode θ) f;
  compose e (woodinSparseCompletedDisplacement θ ((e ‘ p) ‘ θ) (q ‘ θ))

instance woodinSparseCompletedHomogenizingMap_definable :
    ℒₛₑₜ-function₄[V] woodinSparseCompletedHomogenizingMap := by
  unfold woodinSparseCompletedHomogenizingMap
  dsimp only
  apply Language.DefinableFunction₂.comp
  · apply Language.DefinableFunction₃.comp <;> definability
  · apply Language.DefinableFunction₃.comp
    · definability
    · apply Language.DefinableFunction₂.comp
      · apply Language.DefinableFunction₂.comp
        · apply Language.DefinableFunction₃.comp <;> definability
        · definability
      · definability
    · definability

variable {Ω θ f p q : V} [IsOrdinal θ]
local notation "c" => woodinSparsePrefixCode θ
local notation "P" => woodinSparseInverseBase θ c
local notation "R" => woodinSparseInverseOrder θ c
local notation "C" => (forcingCodeP (woodinSparseStageCode θ)) ‘ θ
local notation "T" => (forcingCodeR (woodinSparseStageCode θ)) ‘ θ
local notation "e" => woodinSparseCompletedAutomorphism θ c f
local notation "D" => woodinSparseCompletedDisplacement θ ((e ‘ p) ‘ θ) (q ‘ θ)

variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
variable (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
variable (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
include hΩ hAC hθ h0 hlim hn

theorem woodinSparseCompletedHomogenizingMap_action
    (hf : IsForcingAutomorphism P R f) (hft : f ‘ ∅ = ∅) (hp : p ∈ C) (hq : q ∈ C) :
    IsForcingAutomorphism C T e ∧ IsSparseTailAction θ C T D := by
  have he := woodinSparseCompletedAutomorphism_actual_stage hΩ hAC hθ h0 hlim hn hf hft
  exact ⟨he, woodinSparseCompletedDisplacement_conditions hΩ hAC hθ h0 hlim hn
    (function_value_mem he.1 hp) hq⟩

theorem woodinSparseCompletedHomogenizingMap_automorphism
    (hf : IsForcingAutomorphism P R f) (hft : f ‘ ∅ = ∅) (hp : p ∈ C) (hq : q ∈ C) :
    IsForcingAutomorphism C T (woodinSparseCompletedHomogenizingMap θ f p q) := by
  obtain ⟨he, hd⟩ := woodinSparseCompletedHomogenizingMap_action hΩ hAC hθ h0 hlim hn hf hft hp hq
  exact forcingAutomorphism_compose he hd.1

theorem woodinSparseCompletedHomogenizingMap_restrict
    (hf : IsForcingAutomorphism P R f) (hft : f ‘ ∅ = ∅)
    (hp : p ∈ C) (hq : q ∈ C) {z : V} (hz : z ∈ C) :
    ((woodinSparseCompletedHomogenizingMap θ f p q) ‘ z) ↾ θ = f ‘ (z ↾ θ) := by
  obtain ⟨he, hd⟩ := woodinSparseCompletedHomogenizingMap_action hΩ hAC hθ h0 hlim hn hf hft hp hq
  change (((compose e D) ‘ z) ↾ θ = f ‘ (z ↾ θ))
  rw [value_compose_of_mem_function he.1 hd.1.1 hz, hd.2.1 _ (function_value_mem he.1 hz)]
  rw [(woodinSparseStageCode_inverse h0 hlim hn).1] at hz
  exact woodinSparseCompletedAutomorphism_restrict hΩ hAC hθ h0 hlim hn hf hft hz

theorem woodinSparseCompletedHomogenizingMap_domain
    (hf : IsForcingAutomorphism P R f) (hft : f ‘ ∅ = ∅)
    (hp : p ∈ C) (hq : q ∈ C)
    (hdom : ∀ z ∈ P, domain (f ‘ z) = domain z) {z : V} (hz : z ∈ C) :
    domain ((woodinSparseCompletedHomogenizingMap θ f p q) ‘ z) = domain z := by
  obtain ⟨he, hd⟩ := woodinSparseCompletedHomogenizingMap_action hΩ hAC hθ h0 hlim hn hf hft hp hq
  change (domain ((compose e D) ‘ z) = domain z)
  rw [value_compose_of_mem_function he.1 hd.1.1 hz, hd.2.2.1 _ (function_value_mem he.1 hz)]
  rw [(woodinSparseStageCode_inverse h0 hlim hn).1] at hz
  obtain ⟨hR, ht, hδ, hP, hsp⟩ := woodinSparseCompletedAutomorphism_inputs hΩ hAC hθ h0 hlim hn
  exact sparseHartogsAutomorphism_domain hf hR ht hft hδ hP hsp hz hdom

theorem woodinSparseCompletedHomogenizingMap_empty_tail
    (hf : IsForcingAutomorphism P R f) (hft : f ‘ ∅ = ∅)
    (hp : p ∈ C) (hq : q ∈ C) {z : V} (hz : z ∈ C) (hz0 : z ‘ θ = ∅) :
    (woodinSparseCompletedHomogenizingMap θ f p q) ‘ z = f ‘ (z ↾ θ) := by
  obtain ⟨he, hd⟩ := woodinSparseCompletedHomogenizingMap_action hΩ hAC hθ h0 hlim hn hf hft hp hq
  obtain ⟨hR, ht, hδ, hP, hsp⟩ := woodinSparseCompletedAutomorphism_inputs hΩ hAC hθ h0 hlim hn
  have hz' := hz
  rw [(woodinSparseStageCode_inverse h0 hlim hn).1] at hz'
  have hval : e ‘ z = f ‘ (z ↾ θ) :=
    woodinSparseCompletedAutomorphism_empty_tail hΩ hAC hθ h0 hlim hn hf hft hz' hz0
  have hs := hsp _ (function_value_mem hf.1 (mem_sparsePairCarrier_iff.mp hz').2.1)
  let := hs.1
  have hzero : (e ‘ z) ‘ θ = ∅ := by
    rw [hval]
    exact value_eq_empty_of_not_mem_domain (fun hh ↦ mem_irrefl θ (hs.2.1 θ hh))
  change ((compose e D) ‘ z = f ‘ (z ↾ θ))
  rw [value_compose_of_mem_function he.1 hd.1.1 hz,
    hd.2.2.2 _ (function_value_mem he.1 hz) hzero]
  exact hval

theorem woodinSparseCompletedHomogenizingMap_top
    (hf : IsForcingAutomorphism P R f) (hft : f ‘ ∅ = ∅) (hp : p ∈ C) (hq : q ∈ C) :
    (woodinSparseCompletedHomogenizingMap θ f p q) ‘ ∅ = ∅ := by
  let := hΩ.inaccessible.1
  have ht := (woodinSparseStageCode_valid hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hθ)).system.tops.top
    θ (mem_succ_self _)
  rw [woodinSparseStageCode_top hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hθ)] at ht
  rw [woodinSparseCompletedHomogenizingMap_empty_tail hΩ hAC hθ h0 hlim hn hf hft hp hq ht.1
    (value_eq_empty_of_not_mem_domain (by rw [domain_empty]; exact not_mem_empty))]
  have hz : (∅ : V) ↾ θ = ∅ := by ext z; simp [mem_restrict_iff]
  rwa [hz]

end ZFVP

