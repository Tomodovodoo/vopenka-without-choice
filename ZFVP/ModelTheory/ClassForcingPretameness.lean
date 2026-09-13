import ZFVP.ModelTheory.ClassForcingTowerForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace DefinableForcingTower
variable (T : DefinableForcingTower V)

def ClassCompatible (p q : V) : Prop := ∃ r, T.Condition r ∧ T.LE r p ∧ T.LE r q

instance classCompatible_definable : ℒₛₑₜ-relation T.ClassCompatible := by
  unfold ClassCompatible
  definability

def ClassPredenseBelow (d p : V) : Prop :=
  (∀ s ∈ d, T.Condition s) ∧ ∀ r, T.Condition r → T.LE r p →
    ∃ s ∈ d, T.ClassCompatible r s

instance classPredenseBelow_definable : ℒₛₑₜ-relation T.ClassPredenseBelow := by
  unfold ClassPredenseBelow ClassCompatible
  definability

def ClassDenseRefinements (D : V → V → Prop) (I p F : V) : Prop :=
  IsFunction F ∧ domain F = I ∧ ∀ i ∈ I,
    (∀ s ∈ F ‘ i, D i s) ∧ T.ClassPredenseBelow (F ‘ i) p

theorem classDenseRefinements_definable (D : V → V → Prop) (hd : ℒₛₑₜ-relation D) :
    ℒₛₑₜ-relation₃ (T.ClassDenseRefinements D) := by
  unfold ClassDenseRefinements ClassPredenseBelow ClassCompatible
  definability

/-- Set-indexed definable dense classes have set-sized predense refinements
below a stronger condition. This is the preservation hypothesis to establish
for the actual class iteration, not an axiom of its extension. -/
def IsPretame : Prop := ∀ (D : V → V → Prop), (ℒₛₑₜ-relation D) → ∀ I : V,
  (∀ i ∈ I, ClassForcingDense T.Condition T.LE (D i)) →
  ∀ p, T.Condition p → ∃ q, T.Condition q ∧ T.LE q p ∧
    ∃ F, T.ClassDenseRefinements D I q F

theorem classPredense_meets {G : Set V}
    (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)
    {d p : V} (hd : T.ClassPredenseBelow d p) (hpG : p ∈ G) :
    ∃ s ∈ d, s ∈ G := by
  classical
  let E := fun r ↦ T.Condition r ∧
    (¬T.ClassCompatible r p ∨ ∃ s ∈ d, T.LE r s)
  have hE : ClassForcingDense T.Condition T.LE E := by
    refine ⟨fun _ h ↦ h.1, ?_⟩
    intro r hr
    by_cases hcomp : T.ClassCompatible r p
    · obtain ⟨t, ht, htr, htp⟩ := hcomp
      obtain ⟨s, hs, u, hu, hut, hus⟩ := hd.2 t ht htp
      exact ⟨u, ⟨hu, Or.inr ⟨s, hs, hus⟩⟩, T.le_trans hut htr⟩
    · exact ⟨r, ⟨hr, Or.inl hcomp⟩, T.le_refl hr⟩
  obtain ⟨r, hrG, _, h⟩ := hG.2 E (by unfold E ClassCompatible; definability) hE
  rcases h with h | ⟨s, hs, hrs⟩
  · obtain ⟨t, htG, htr, htp⟩ := hG.1.2.2.2 r hrG p hpG
    exact (h ⟨t, hG.1.1 t htG, htr, htp⟩).elim
  · exact ⟨s, hs, hG.1.2.2.1 r hrG s (hd.1 s hs) hrs⟩

theorem IsPretame.refinements_in_generic (hT : T.IsPretame) {G : Set V}
    (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)
    (D : V → V → Prop) (hd : ℒₛₑₜ-relation D) (I : V)
    (hD : ∀ i ∈ I, ClassForcingDense T.Condition T.LE (D i)) :
    ∃ p ∈ G, ∃ F, T.ClassDenseRefinements D I p F := by
  let E := fun p ↦ T.Condition p ∧ ∃ F, T.ClassDenseRefinements D I p F
  have hE : ClassForcingDense T.Condition T.LE E := by
    refine ⟨fun _ h ↦ h.1, ?_⟩
    intro p hp
    obtain ⟨q, hq, hqp, F, hF⟩ := hT D hd I hD p hp
    exact ⟨q, ⟨hq, F, hF⟩, hqp⟩
  have hdE : ℒₛₑₜ-predicate E := by
    have := T.classDenseRefinements_definable D hd
    unfold E
    definability
  obtain ⟨p, hpG, _, F, hF⟩ := hG.2 E hdE hE
  exact ⟨p, hpG, F, hF⟩

end DefinableForcingTower
end ZFVP
