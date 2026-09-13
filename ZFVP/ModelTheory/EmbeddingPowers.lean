import ZFVP.ModelTheory.CriticalSequence
import ZFVP.SetTheory.NaturalAddition

/-! Composition powers of an elementary graph through all internal naturals. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def embeddingPower (A f n : V) : V :=
  naturalIteration (fun g ↦ compose g f) (by definability) (SetTheory.identity A) n

instance embeddingPower_definable (A f : V) : ℒₛₑₜ-function₁ (embeddingPower A f) :=
  naturalIteration_definable _ (by definability) _

@[simp] theorem embeddingPower_zero (A f : V) : embeddingPower A f 0 = SetTheory.identity A :=
  naturalIteration_zero _ _ _

theorem embeddingPower_succ (A f : V) {n : V} (hn : n ∈ (ω : V)) :
    embeddingPower A f (succ n) = compose (embeddingPower A f n) f :=
  naturalIteration_succ _ _ _ hn

theorem IsCodedMembershipEmbedding.power {A f n : V} (h : IsCodedMembershipEmbedding A A f)
    (hn : n ∈ (ω : V)) : IsCodedMembershipEmbedding A A (embeddingPower A f n) :=
  naturalIteration_invariant _ (by definability) _ (IsCodedMembershipEmbedding A A) (by definability)
    (IsCodedMembershipEmbedding.identity h.source_nonempty) (fun _ hg ↦ hg.comp h) n hn

theorem embeddingPower_value_succ {A f n x : V} (h : IsCodedMembershipEmbedding A A f)
    (hn : n ∈ (ω : V)) (hx : x ∈ A) :
    (embeddingPower A f (succ n)) ‘ x = f ‘ ((embeddingPower A f n) ‘ x) := by
  rw [embeddingPower_succ A f hn, value_compose_of_mem_function (h.power hn).function h.function hx]

theorem embeddingPower_value_fixed {A f n x : V} (h : IsCodedMembershipEmbedding A A f)
    (hn : n ∈ (ω : V)) (hx : x ∈ A) (hfix : f ‘ x = x) :
    (embeddingPower A f n) ‘ x = x := by
  apply naturalNumber_induction (fun n ↦ (embeddingPower A f n) ‘ x = x) (by definability) ?_ ?_ n hn
  · rw [embeddingPower_zero, identity_value hx]
  · intro n hn ih
    rw [embeddingPower_value_succ h hn hx, ih, hfix]

theorem embeddingPower_value_commutes {A f n x : V} (h : IsCodedMembershipEmbedding A A f)
    (hn : n ∈ (ω : V)) (hx : x ∈ A) :
    (embeddingPower A f n) ‘ (f ‘ x) = f ‘ ((embeddingPower A f n) ‘ x) := by
  have hfx := function_value_mem h.function hx
  apply naturalNumber_induction
    (fun n ↦ (embeddingPower A f n) ‘ (f ‘ x) = f ‘ ((embeddingPower A f n) ‘ x)) (by definability) ?_ ?_ n hn
  · rw [embeddingPower_zero, identity_value hfx, identity_value hx]
  · intro n hn ih
    rw [embeddingPower_value_succ h hn hfx, embeddingPower_value_succ h hn hx, ih]

theorem embeddingPower_value_criticalIterate {A f κ i n : V}
    (h : IsCodedMembershipEmbedding A A f) (hκ : κ ∈ A)
    (hi : i ∈ (ω : V)) (hn : n ∈ (ω : V)) :
    (embeddingPower A f n) ‘ (criticalIterate f κ i) = criticalIterate f κ (ordinalAdd i n) := by
  let := IsOrdinal.of_mem hi
  have hstage : ∀ i ∈ (ω : V), criticalIterate f κ i ∈ A :=
    naturalIteration_invariant _ (by definability) κ (fun x ↦ x ∈ A) (by definability)
      hκ (fun x hx ↦ function_value_mem h.function hx)
  apply naturalNumber_induction
    (fun n ↦ (embeddingPower A f n) ‘ (criticalIterate f κ i) = criticalIterate f κ (ordinalAdd i n))
    (by definability) ?_ ?_ n hn
  · rw [embeddingPower_zero, identity_value (hstage i hi)]
    simp only [zero_def, ordinalAdd_zero]
  · intro n hn ih
    let := IsOrdinal.of_mem hn
    rw [embeddingPower_value_succ h hn (hstage i hi), ordinalAdd_succ,
      criticalIterate_succ f κ (ordinalAdd_natural hi hn), ih]

theorem embeddingPower_value_criticalPoint {A f κ n : V}
    (h : IsCodedMembershipEmbedding A A f) (hκ : κ ∈ A) (hn : n ∈ (ω : V)) :
    (embeddingPower A f n) ‘ κ = criticalIterate f κ n := by
  simpa only [criticalIterate_zero, ordinalAdd_zero_left_natural hn] using
    embeddingPower_value_criticalIterate h hκ (by simp : (0 : V) ∈ ω) hn

end ZFVP
