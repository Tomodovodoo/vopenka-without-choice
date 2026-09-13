import ZFVP.ModelTheory.ForcingSelectedUnion
import ZFVP.ModelTheory.TwoStepReconstruction
import ZFVP.ModelTheory.ProjectionQuotient

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def twoStepTailSelectorFormula : SetTheorySemisentence 5 :=
  f“H P R Q t. ∀ z, z ∈ H ↔ ∃ c ∈ !twoStepConditionsFormula P R Q t,
    z = !kpair.dfn c (!kpair.π₂.dfn c)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def twoStepTailSelector (P R Q t : V) : V :=
  definableGraph (twoStepConditions P R Q t) kpair.π₂ (by definability)

instance twoStepTailSelectorFormula_defined :
    ℒₛₑₜ-function₄[V] twoStepTailSelector via twoStepTailSelectorFormula :=
  ⟨fun v ↦ by
    simp [twoStepTailSelectorFormula]
    rw [mem_ext_iff]
    simp only [twoStepTailSelector, mem_definableGraph_iff]⟩

instance twoStepTailSelector_definable : ℒₛₑₜ-function₄[V] twoStepTailSelector :=
  twoStepTailSelectorFormula_defined.to_definable

theorem twoStepTailSelector_value {P R Q t c : V} (hc : c ∈ twoStepConditions P R Q t) :
    (twoStepTailSelector P R Q t) ‘ c = kpair.π₂ c := value_definableGraph _ _ _ hc

theorem twoStepTailSelector_maps (P R Q t : V) :
    twoStepTailSelector P R Q t ∈ twoStepNames Q t ^ twoStepConditions P R Q t := by
  apply definableGraph_mem_function_of_mapsTo
  intro c hc
  obtain ⟨p, _, τ, hτ, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp hc
  simpa only [kpair.π₂_kpair] using hτ

namespace TwoStepModel
variable (A : ForcingContext V) {Q S t : V} (h : IsForcingIterand A.P A.R Q S t) {G : Set V}
  (hG : IsExternalForcingGeneric (twoStepConditions A.P A.R Q t) (twoStepOrder A.P A.R Q S t) G)
  (hA : A.G = forcingProjectionGeneric A.P A.R (twoStepProjection A.P A.R Q t) G)

theorem selected_tail_value {c : V} (hc : c ∈ twoStepConditions A.P A.R Q t)
    {f α i : A.Model} (hf : f ∈ A.check (twoStepConditions A.P A.R Q t) ^ α)
    (hi : i ∈ α) (he : f ‘ i = A.check c) :
    (compose (compose f (A.check (twoStepTailSelector A.P A.R Q t)))
      (A.evaluationGraph (twoStepNames Q t) (fun _ hτ ↦ h.name hτ))) ‘ i =
        A.ofName ⟨kpair.π₂ c, h.name (by
          obtain ⟨p, _, τ, hτ, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp hc
          simpa only [kpair.π₂_kpair] using hτ)⟩ := by
  have hv := A.selectedEvaluation_value (fun _ hτ ↦ h.name hτ)
    (twoStepTailSelector_maps A.P A.R Q t) f hf hi hc he
  simpa only [twoStepTailSelector_value hc] using hv

include hG hA in
theorem mem_of_selected_tail_bound {q : V} (ν : ForcingName A.P) (hq : ⟨q, ν.val⟩ₖ ∈ G)
    {f α : A.Model} (hf : f ∈ A.check (twoStepConditions A.P A.R Q t) ^ α)
    (hfirst : ∀ i ∈ α, ∀ c ∈ twoStepConditions A.P A.R Q t,
      f ‘ i = A.check c → kpair.π₁ c ∈ A.G)
    (hbound : ∀ i ∈ α,
      ⟨A.ofName ν, (compose (compose f (A.check (twoStepTailSelector A.P A.R Q t)))
        (A.evaluationGraph (twoStepNames Q t) (fun _ hτ ↦ h.name hτ))) ‘ i⟩ₖ ∈
        A.ofName ⟨S, h.orderName⟩) :
    ∀ i ∈ α, f ‘ i ∈ A.projectionQuotientFilter G := by
  intro i hi
  obtain ⟨c, hc, he⟩ := (A.mem_check_iff _ (f ‘ i)).mp (function_value_mem hf hi)
  obtain ⟨p, _, τ, hτ, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp hc
  let σ : ForcingName A.P := ⟨τ, h.name hτ⟩
  have hpG : p ∈ A.G := by
    simpa only [kpair.π₁_kpair] using hfirst i hi _ hc he
  have hle : ⟨A.ofName ν, A.ofName σ⟩ₖ ∈ A.ofName ⟨S, h.orderName⟩ := by
    simpa only [selected_tail_value A h hc hf hi he, kpair.π₂_kpair] using hbound i hi
  have hσQ := forcingOrder_right_mem (preorder A h) hle
  have hσSecond := (second_filter A h hG hA).2.2.1 _
    (value_in_second A h hG hA (τ := ν) hq) _ hσQ hle
  exact ⟨_, mem_of_first_second A h hG hA (τ := σ) hc hpG hσSecond, he⟩

include hG hA in
theorem mem_of_selected_collapse_union {q : V} (ν f : ForcingName A.P)
    (hq : ⟨q, ν.val⟩ₖ ∈ G) {κ δ α : A.Model}
    (hf : A.ofName f ∈ A.check (twoStepConditions A.P A.R Q t) ^ α)
    (hκ : IsRegularCardinal κ) (hα : α ∈ κ) (hDC : InternalDependentChoiceAt α)
    (hS : A.ofName ⟨S, h.orderName⟩ = woodinCollapseOrder κ δ)
    (hfirst : ∀ i ∈ α, ∀ c ∈ twoStepConditions A.P A.R Q t,
      (A.ofName f) ‘ i = A.check c → kpair.π₁ c ∈ A.G)
    (hs : IsForcingDescending (woodinCollapse κ δ)
      (forcingSeparativeOrder (woodinCollapse κ δ) (woodinCollapseOrder κ δ)) α
      (compose (compose (A.ofName f) (A.check (twoStepTailSelector A.P A.R Q t)))
        (A.evaluationGraph (twoStepNames Q t) (fun _ hτ ↦ h.name hτ))))
    (he : A.ofName ν = A.ofName
      ⟨forcingSelectedUnion A.P A.R A.one (twoStepNames Q t)
        (twoStepTailSelector A.P A.R Q t) f.val, forcingSelectedUnion_isName _ _ _ _ _ _⟩) :
    ∀ i ∈ α, (A.ofName f) ‘ i ∈ A.projectionQuotientFilter G := by
  apply mem_of_selected_tail_bound A h hG hA ν hq hf hfirst
  rw [he, hS]
  exact (A.forcingSelectedUnion_collapse_bound (fun _ hτ ↦ h.name hτ)
    (twoStepTailSelector_maps A.P A.R Q t) f hf hκ hα hDC hs).2

end TwoStepModel
end ZFVP
