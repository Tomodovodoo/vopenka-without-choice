import ZFVP.ModelTheory.TwoStepSelectedUnion
import ZFVP.ModelTheory.LocalSelectedUnionBound
import ZFVP.ModelTheory.SaturatedWoodinSuccessor

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem selectedUnion_empty_of_names (A : ForcingContext V) {Q t : V}
    (h : ∀ ν ∈ twoStepNames Q t, IsForcingName A.P ν) (f : ForcingName A.P) {α : A.Model}
    (hf : A.ofName f ∈ A.check (twoStepConditions A.P A.R Q t) ^ α)
    (htail : ∀ i ∈ α, ∀ c ∈ twoStepConditions A.P A.R Q t,
      (A.ofName f) ‘ i = A.check c → kpair.π₂ c = ∅) :
    A.ofName ⟨forcingSelectedUnion A.P A.R A.one (twoStepNames Q t)
      (twoStepTailSelector A.P A.R Q t) f.val, forcingSelectedUnion_isName _ _ _ _ _ _⟩ = ∅ := by
  apply A.forcingSelectedUnion_value_empty h
    (twoStepTailSelector_maps A.P A.R Q t) f hf
  intro i hi
  obtain ⟨c, hc, hci⟩ := (A.mem_check_iff _ _).mp (function_value_mem hf hi)
  rw [A.selectedEvaluation_value h (twoStepTailSelector_maps A.P A.R Q t) (A.ofName f) hf hi hc hci]
  simpa only [twoStepTailSelector_value hc, htail i hi c hc hci] using A.rawEmptyName_value

theorem selectedUnion_empty_of_tails (A : ForcingContext V) {Q S t : V}
    (h : IsForcingIterand A.P A.R Q S t) (f : ForcingName A.P) {α : A.Model}
    (hf : A.ofName f ∈ A.check (twoStepConditions A.P A.R Q t) ^ α)
    (htail : ∀ i ∈ α, ∀ c ∈ twoStepConditions A.P A.R Q t,
      (A.ofName f) ‘ i = A.check c → kpair.π₂ c = ∅) :
    A.ofName ⟨forcingSelectedUnion A.P A.R A.one (twoStepNames Q t)
      (twoStepTailSelector A.P A.R Q t) f.val, forcingSelectedUnion_isName _ _ _ _ _ _⟩ = ∅ :=
  A.selectedUnion_empty_of_names (fun _ hν ↦ h.name hν) f hf htail

end ForcingContext

theorem selectedUnion_empty_forced_of_names_countable [Countable V] {P R one p Q t : V}
    (hR : IsForcingPreorder P R) (ho : IsForcingTop P R one) (hp : p ∈ P)
    (h : ∀ ν ∈ twoStepNames Q t, IsForcingName P ν) (f : ForcingName P)
    (hf : ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G), p ∈ G →
      let A : ForcingContext V := ⟨P, R, one, G, hR, ho, hG⟩
      ∃ α : A.Model, A.ofName f ∈ A.check (twoStepConditions P R Q t) ^ α ∧
        ∀ i ∈ α, ∀ c ∈ twoStepConditions P R Q t, (A.ofName f) ‘ i = A.check c → kpair.π₂ c = ∅) :
    p ∈ atomicEquality P R
      (forcingSelectedUnion P R one (twoStepNames Q t) (twoStepTailSelector P R Q t) f.val) ∅ := by
  apply atomicEquality_of_all_generics hR ho hp
    ⟨_, forcingSelectedUnion_isName _ _ _ _ _ _⟩ ⟨∅, empty_forcingName P⟩
  intro G hG hpG
  let A : ForcingContext V := ⟨P, R, one, G, hR, ho, hG⟩
  obtain ⟨α, hα, htail⟩ := hf G hG hpG
  exact (A.selectedUnion_empty_of_names h f hα htail).trans A.rawEmptyName_value.symm

theorem selectedUnion_empty_forced_countable [Countable V] {P R one p Q S t : V}
    (hR : IsForcingPreorder P R) (ho : IsForcingTop P R one) (hp : p ∈ P)
    (h : IsForcingIterand P R Q S t) (f : ForcingName P)
    (hf : ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G), p ∈ G →
      let A : ForcingContext V := ⟨P, R, one, G, hR, ho, hG⟩
      ∃ α : A.Model, A.ofName f ∈ A.check (twoStepConditions P R Q t) ^ α ∧
        ∀ i ∈ α, ∀ c ∈ twoStepConditions P R Q t, (A.ofName f) ‘ i = A.check c → kpair.π₂ c = ∅) :
    p ∈ atomicEquality P R
      (forcingSelectedUnion P R one (twoStepNames Q t) (twoStepTailSelector P R Q t) f.val) ∅ :=
  selectedUnion_empty_forced_of_names_countable hR ho hp (fun _ hν ↦ h.name hν) f hf

theorem localSelectedUnion_empty_of_names_countable [Countable V] {P R one δ p Q t : V}
    (hR : IsForcingPreorder P R) (ho : IsForcingTop P R one) (hp : p ∈ P)
    (h : ∀ ν ∈ twoStepNames Q t, IsForcingName P ν) (f : ForcingName P)
    (hf : ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G), p ∈ G →
      let A : ForcingContext V := ⟨P, R, one, G, hR, ho, hG⟩
      ∃ α : A.Model, A.ofName f ∈ A.check (twoStepConditions P R Q t) ^ α ∧
        ∀ i ∈ α, ∀ c ∈ twoStepConditions P R Q t, (A.ofName f) ‘ i = A.check c → kpair.π₂ c = ∅) :
    forcingLocalCanonicalName P R one δ p
      (forcingSelectedUnion P R one (twoStepNames Q t) (twoStepTailSelector P R Q t) f.val) = ∅ :=
  forcingLocalCanonicalName_empty_of_forced hR (selectedUnion_empty_forced_of_names_countable hR ho hp h f hf)

theorem localSelectedUnion_empty_countable [Countable V] {P R one δ p Q S t : V}
    (hR : IsForcingPreorder P R) (ho : IsForcingTop P R one) (hp : p ∈ P)
    (h : IsForcingIterand P R Q S t) (f : ForcingName P)
    (hf : ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G), p ∈ G →
      let A : ForcingContext V := ⟨P, R, one, G, hR, ho, hG⟩
      ∃ α : A.Model, A.ofName f ∈ A.check (twoStepConditions P R Q t) ^ α ∧
        ∀ i ∈ α, ∀ c ∈ twoStepConditions P R Q t, (A.ofName f) ‘ i = A.check c → kpair.π₂ c = ∅) :
    forcingLocalCanonicalName P R one δ p
      (forcingSelectedUnion P R one (twoStepNames Q t) (twoStepTailSelector P R Q t) f.val) = ∅ :=
  forcingLocalCanonicalName_empty_of_forced hR (selectedUnion_empty_forced_countable hR ho hp h f hf)

end ZFVP
