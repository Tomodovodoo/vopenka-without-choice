import ZFVP.ModelTheory.WoodinSparseCompletedHomogenizingRow
import ZFVP.ModelTheory.WoodinCanonicalCommonNameUniform

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSparseCompletedCommonWitness (θ f p q r : V) : V :=
  let c := woodinSparsePrefixCode θ;
  let P := woodinSparseInverseBase θ c;
  let R := woodinSparseInverseOrder θ c;
  let γ := woodinLimitCardinal (woodinIterationCardinalPrefix θ);
  let δ := woodinSparseInverseCutoff θ c;
  let x := ((woodinSparseCompletedAutomorphism θ c f) ‘ p) ‘ θ;
  let y := q ‘ θ;
  let N := woodinCollapseDisplacementName P R (hartogsNumberName P R (checkName ∅ γ)) (checkName ∅ δ) x y;
  sparseAppend θ r (canonicalTailCommonName P R ∅ N x y)

attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp

instance woodinSparseCompletedCommonWitness_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (woodinSparseCompletedCommonWitness (V := V)) := by
  unfold woodinSparseCompletedCommonWitness
  dsimp only
  apply Language.DefinableFunction₃.comp
  · definability
  · definability
  · apply canonicalTailCommonName_comp
    · definability
    · definability
    · definability
    · apply woodinCollapseDisplacementName_comp <;> definability
    · definability
    · definability

variable {Ω θ f p q r : V} [IsOrdinal θ]
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

theorem woodinSparseCompletedCommonWitness_spec
    (hf : IsForcingAutomorphism P R f) (hft : f ‘ ∅ = ∅)
    (hp : p ∈ C) (hq : q ∈ C) (hr : r ∈ P)
    (hrp : ⟨r,f ‘ (p ↾ θ)⟩ₖ ∈ R) (hrq : ⟨r,q ↾ θ⟩ₖ ∈ R)
    (hdom : ∀ z ∈ P, domain (f ‘ z) = domain z) :
    let w := woodinSparseCompletedCommonWitness θ f p q r
    w ∈ C ∧ ⟨w,(woodinSparseCompletedHomogenizingMap θ f p q) ‘ p⟩ₖ ∈ T ∧
      ⟨w,q⟩ₖ ∈ T ∧ w ↾ θ = r ∧ domain w ⊆ (domain r ∪ domain p) ∪ domain q := by
  obtain ⟨he, hd⟩ := woodinSparseCompletedHomogenizingMap_action hΩ hAC hθ h0 hlim hn hf hft hp hq
  obtain ⟨hR, ht, hδ, hP, hsp⟩ := woodinSparseCompletedAutomorphism_inputs hΩ hAC hθ h0 hlim hn
  obtain ⟨hγδ, hγ⟩ := woodinSparseCompletedDisplacement_cardinal_inputs hΩ hAC hθ h0 hlim hn
  have hxp := function_value_mem he.1 hp
  have hq' := hq
  have hp' := hp
  rw [(woodinSparseStageCode_inverse h0 hlim hn).1] at hxp hq' hp'
  have hrx : ⟨r,(e ‘ p) ↾ θ⟩ₖ ∈ R := by
    rwa [woodinSparseCompletedAutomorphism_restrict hΩ hAC hθ h0 hlim hn hf hft hp']
  have hb := sparseCanonicalHartogsDisplacement_commonExtension hR ht hδ hP hγδ hγ hxp hq' hr hrx hrq hsp
  have hval : (woodinSparseCompletedHomogenizingMap θ f p q) ‘ p = D ‘ (e ‘ p) :=
    value_compose_of_mem_function he.1 hd.1.1 hp
  have hdomain : domain (e ‘ p) = domain p :=
    sparseHartogsAutomorphism_domain hf hR ht hft hδ hP hsp hp' hdom
  change woodinSparseCompletedCommonWitness θ f p q r ∈ C ∧ _
  rw [(woodinSparseStageCode_inverse h0 hlim hn).1, (woodinSparseStageCode_inverse h0 hlim hn).2, hval]
  refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, ?_⟩
  simpa only [woodinSparseCompletedCommonWitness, hdomain] using hb.2.2.2.2.2

end ZFVP
