import ZFVP.SetTheory.BoundedNaturals
import ZFVP.SetTheory.FiniteCodingClosure

/-! A bounded predicate for transitive sets closed under finite code constructors. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def codingSupportFormula : SetTheorySemisentence 1 :=
  “U. !IsTransitive.dfn U ∧ (∃ O ∈ U, !boundedOmegaFormula O) ∧
    ∀ x ∈ U, ∀ y ∈ U,
      (∃ p ∈ U, !boundedKpairFormula p x y) ∧
      (∃ d ∈ U, !boundedDoubletonFormula d x y) ∧ (∃ s ∈ U, !boundedSuccFormula s x)”

theorem codingSupportFormula_bounded : IsBoundedSetFormula codingSupportFormula := by
  exact .and (isTransitiveFormula_bounded.subst ![.bvar 0])
    (.and (.exs (.bvar 0) (boundedOmegaFormula_bounded.subst ![.bvar 0]))
      (.all (.bvar 0) (.all (.bvar 1) (.and
        (.exs (.bvar 2) (boundedKpairFormula_bounded.subst ![.bvar 0, .bvar 2, .bvar 1]))
        (.and (.exs (.bvar 2) (boundedDoubletonFormula_bounded.subst ![.bvar 0, .bvar 2, .bvar 1]))
          (.exs (.bvar 2) (boundedSuccFormula_bounded.subst ![.bvar 0, .bvar 2])))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

class IsCodingSupport (U : V) : Prop extends IsTransitive U where
  omega_mem : (ω : V) ∈ U
  kpair_closed : ∀ x ∈ U, ∀ y ∈ U, ⟨x, y⟩ₖ ∈ U
  doubleton_closed : ∀ x ∈ U, ∀ y ∈ U, doubleton x y ∈ U
  succ_closed : ∀ x ∈ U, succ x ∈ U

theorem isCodingSupport_iff (U : V) : IsCodingSupport U ↔ IsTransitive U ∧ (ω : V) ∈ U ∧
    (∀ x ∈ U, ∀ y ∈ U, ⟨x, y⟩ₖ ∈ U ∧ doubleton x y ∈ U ∧ succ x ∈ U) := by
  constructor
  · intro h
    exact ⟨h.toIsTransitive, h.omega_mem, fun x hx y hy ↦
      ⟨h.kpair_closed x hx y hy, h.doubleton_closed x hx y hy, h.succ_closed x hx⟩⟩
  · rintro ⟨ht, hω, hc⟩
    exact {
      toIsTransitive := ht
      omega_mem := hω
      kpair_closed := fun x hx y hy ↦ (hc x hx y hy).1
      doubleton_closed := fun x hx y hy ↦ (hc x hx y hy).2.1
      succ_closed := fun x hx ↦ (hc x hx x hx).2.2 }

instance codingSupportFormula_defined : ℒₛₑₜ-predicate[V] IsCodingSupport via codingSupportFormula :=
  ⟨fun v ↦ by simp [codingSupportFormula, isCodingSupport_iff]⟩

instance isCodingSupport_definable : ℒₛₑₜ-predicate[V] IsCodingSupport := codingSupportFormula_defined.to_definable

instance codingUniverse_isCodingSupport (X : V) : IsCodingSupport (codingUniverse X) where
  toIsTransitive := codingUniverse_transitive X
  omega_mem := omega_mem_codingUniverse X
  kpair_closed := fun _ hx _ hy ↦ codingUniverse_kpair_closed hx hy
  doubleton_closed := fun _ hx _ hy ↦ by simpa only [pair_eq_doubleton] using codingUniverse_pair_closed hx hy
  succ_closed := fun _ hx ↦ codingUniverse_insert_closed hx hx

theorem codingSupport_containing (X : V) : ∃ U : V, IsCodingSupport U ∧ X ∈ U :=
  ⟨codingUniverse X, inferInstance, self_mem_codingUniverse X⟩

namespace IsCodingSupport

variable {U : V} [hU : IsCodingSupport U]

theorem natural_mem {n : V} (hn : n ∈ (ω : V)) : n ∈ U := hU.mem_trans hn hU.omega_mem

theorem empty_mem : (∅ : V) ∈ U := natural_mem empty_mem_ω

theorem numeral_mem (n : ℕ) : (n : V) ∈ U := natural_mem (by simp)

theorem singleton_mem {x : V} (hx : x ∈ U) : ({x} : V) ∈ U := hU.doubleton_closed x hx x hx

theorem contains_members {X : V} (hX : X ∈ U) : X ⊆ U := hU.transitive X hX

end IsCodingSupport
end ZFVP
