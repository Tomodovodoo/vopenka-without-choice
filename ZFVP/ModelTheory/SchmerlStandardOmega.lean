import ZFVP.SetTheory.StandardNaturals
import ZFVP.SetTheory.NaturalPredecessor
import ZFVP.SetTheory.ElementaryDefined
import ZFVP.SetTheory.EndExtensionCoding
import Foundation.FirstOrder.SetTheory.Universe

/-! Externally standard omega for a well-founded ambient universe, its
 elementary submodels, and their membership end extensions. -/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def HasStandardOmega (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : Prop :=
  ∀ n ∈ (ω : V), ∃ k : ℕ, n = (k : V)

theorem standardOmega_of_wellFounded (h : WellFounded (fun x y : V ↦ x ∈ y)) :
    HasStandardOmega V := by
  intro n
  induction n using h.induction with
  | h n ih =>
    intro hn
    rcases internalNatural_cases hn with rfl | ⟨k, hk, rfl⟩
    · exact ⟨0, rfl⟩
    · obtain ⟨m, rfl⟩ := ih k (mem_succ_self k) hk
      exact ⟨m + 1, (num_succ_def m).symm⟩

theorem universe_standardOmega : HasStandardOmega Universe.{u} :=
  standardOmega_of_wellFounded Universe.wellFounded

theorem standardOmega_of_elementaryMap (j : ElementaryMap V W) (hW : HasStandardOmega W) :
    HasStandardOmega V := by
  have hjω : j (ω : V) = (ω : W) :=
    (j.map_defined boundedOmegaFormula (fun v ↦ v 0 = (ω : V))
      (fun v ↦ v 0 = (ω : W)) ![ω]).mp rfl
  intro n hn
  have hn' : j n ∈ (ω : W) := by
    rw [← hjω]
    exact (j.map_mem_iff n _).mpr hn
  obtain ⟨k, hk⟩ := hW (j n) hn'
  refine ⟨k, j.injective ?_⟩
  rw [j.map_numeral, hk]

theorem standardOmega_of_endExtension (j : MembershipEndExtension V W) (hV : HasStandardOmega V) :
    HasStandardOmega W := by
  intro n hn
  rw [← j.map_omega] at hn
  obtain ⟨m, hm, rfl⟩ := j.endExtension (ω : V) n hn
  obtain ⟨k, rfl⟩ := hV m hm
  exact ⟨k, j.map_numeral k⟩

theorem HasStandardOmega.forall_iff (h : HasStandardOmega V) (P : V → Prop) :
    (∀ n ∈ (ω : V), P n) ↔ ∀ k : ℕ, P (k : V) := by
  constructor
  · intro hp k
    exact hp _ (by simp)
  · intro hp n hn
    obtain ⟨k, rfl⟩ := h n hn
    exact hp k

theorem HasStandardOmega.exists_iff (h : HasStandardOmega V) (P : V → Prop) :
    (∃ n ∈ (ω : V), P n) ↔ ∃ k : ℕ, P (k : V) := by
  constructor
  · rintro ⟨n, hn, hp⟩
    obtain ⟨k, rfl⟩ := h n hn
    exact ⟨k, hp⟩
  · rintro ⟨k, hk⟩
    exact ⟨_, by simp, hk⟩

end ZFVP.Schmerl
