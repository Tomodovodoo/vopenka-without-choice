import ZFVP.ModelTheory.TwoStepProjection

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ForcingContext.ofName_mem_of_forcedMember (A : ForcingContext V)
    (σ τ : ForcingName A.P) {p : V} (hp : p ∈ A.G) (hf : p ∈ atomicMembership A.P A.R σ.val τ.val) :
    A.ofName σ ∈ A.ofName τ := by
  have hf' : p ∈ forcingFormula A.P A.R nameMemberFormula (standardTuple ![σ.val, τ.val]) := by
    rwa [forcingFormula_nameMember]
  have he := (A.formula_truth nameMemberFormula ![σ, τ]).mpr ⟨p, hp, hf'⟩
  simpa [nameMemberFormula] using he

theorem ForcingContext.ofName_pair_mem_of_forced (A : ForcingContext V)
    (S σ τ : ForcingName A.P) {p : V} (hp : p ∈ A.G)
    (hf : p ∈ forcingFormula A.P A.R boundedPairMemberFormula (standardTuple ![S.val, σ.val, τ.val])) :
    ⟨A.ofName σ, A.ofName τ⟩ₖ ∈ A.ofName S :=
  (Defined.eval_iff _).mp ((A.formula_truth boundedPairMemberFormula ![S, σ, τ]).mpr ⟨p, hp, hf⟩)

def twoStepSecondFilter (A : ForcingContext V) (Q S : ForcingName A.P) (G : Set V) : Set A.Model :=
  {x | x ∈ A.ofName Q ∧ ∃ p : V, ∃ τ : ForcingName A.P,
    ⟨p, τ.val⟩ₖ ∈ G ∧ ⟨A.ofName τ, x⟩ₖ ∈ A.ofName S}

namespace TwoStepModel

variable (A : ForcingContext V) {Q S t : V} (h : IsForcingIterand A.P A.R Q S t) {G : Set V}
  (hG : IsExternalForcingGeneric (twoStepConditions A.P A.R Q t) (twoStepOrder A.P A.R Q S t) G)
  (hA : A.G = forcingProjectionGeneric A.P A.R (twoStepProjection A.P A.R Q t) G)

include h hG hA

theorem first_mem {p : V} {τ : ForcingName A.P} (hp : ⟨p, τ.val⟩ₖ ∈ G) : p ∈ A.G := by
  rw [hA]
  have hc := hG.1.1 _ hp
  have hh := (twoStep_projection A.order A.top h).image_mem A.order hG.1 hp
  rw [twoStepProjection_value hc, kpair.π₁_kpair] at hh
  exact hh

theorem value_mem {p : V} {τ : ForcingName A.P} (hp : ⟨p, τ.val⟩ₖ ∈ G) :
    A.ofName τ ∈ A.ofName ⟨Q, h.posetName⟩ :=
  A.ofName_mem_of_forcedMember τ ⟨Q, h.posetName⟩ (first_mem A h hG hA hp)
    (((kpair_mem_twoStepConditions _ _ _ _ _ _).mp (hG.1.1 _ hp)).2.2)

omit hG hA in
theorem preorder : IsForcingPreorder (A.ofName ⟨Q, h.posetName⟩) (A.ofName ⟨S, h.orderName⟩) := by
  obtain ⟨p, hp⟩ := A.generic.1.2.1
  exact (Defined.eval_iff _).mp ((A.formula_truth forcingPreorderFormula
    ![⟨Q, h.posetName⟩, ⟨S, h.orderName⟩]).mpr ⟨p, hp, h.preorder p (A.generic.1.1 p hp)⟩)

theorem value_le {p q : V} {τ σ : ForcingName A.P} (hp : ⟨p, τ.val⟩ₖ ∈ G)
    (hle : ⟨⟨p, τ.val⟩ₖ, ⟨q, σ.val⟩ₖ⟩ₖ ∈ twoStepOrder A.P A.R Q S t) :
    ⟨A.ofName τ, A.ofName σ⟩ₖ ∈ A.ofName ⟨S, h.orderName⟩ := by
  have hf := ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp hle).2.2.2
  simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hf
  exact A.ofName_pair_mem_of_forced ⟨S, h.orderName⟩ τ σ (first_mem A h hG hA hp) hf

theorem value_in_second {p : V} {τ : ForcingName A.P} (hp : ⟨p, τ.val⟩ₖ ∈ G) :
    A.ofName τ ∈ twoStepSecondFilter A ⟨Q, h.posetName⟩ ⟨S, h.orderName⟩ G := by
  have hx := value_mem A h hG hA hp
  exact ⟨hx, p, τ, hp, (preorder A h).2.1 _ hx⟩

theorem second_filter : IsExternalForcingFilter (A.ofName ⟨Q, h.posetName⟩) (A.ofName ⟨S, h.orderName⟩)
    (twoStepSecondFilter A ⟨Q, h.posetName⟩ ⟨S, h.orderName⟩ G) := by
  have ho := preorder A h
  refine ⟨fun x hx ↦ hx.1, ?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hG.1.2.1
    obtain ⟨p, _, τ, hτ, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp (hG.1.1 a ha)
    exact ⟨A.ofName ⟨τ, h.name hτ⟩, value_in_second A h hG hA (τ := ⟨τ, h.name hτ⟩) ha⟩
  · intro x hx y hy hxy
    obtain ⟨p, τ, hp, hτx⟩ := hx.2
    exact ⟨hy, p, τ, hp, ho.2.2 _ (value_mem A h hG hA hp) x hx.1 y hy hτx hxy⟩
  · intro x hx y hy
    obtain ⟨p, τ, hp, hτx⟩ := hx.2
    obtain ⟨q, σ, hq, hσy⟩ := hy.2
    obtain ⟨a, ha, hap, haq⟩ := hG.1.2.2.2 _ hp _ hq
    obtain ⟨r, _, ν, hν, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp (hG.1.1 a ha)
    let υ : ForcingName A.P := ⟨ν, h.name hν⟩
    have hυQ := value_mem A h hG hA (τ := υ) ha
    refine ⟨A.ofName υ, value_in_second A h hG hA (τ := υ) ha, ?_, ?_⟩
    · exact ho.2.2 _ hυQ _ (value_mem A h hG hA hp) x hx.1
        (value_le A h hG hA (τ := υ) ha hap) hτx
    · exact ho.2.2 _ hυQ _ (value_mem A h hG hA hq) y hy.1
        (value_le A h hG hA (τ := υ) ha haq) hσy

end TwoStepModel
end ZFVP
