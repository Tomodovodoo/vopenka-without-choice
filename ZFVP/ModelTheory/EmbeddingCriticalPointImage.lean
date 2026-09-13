import ZFVP.ModelTheory.CriticalPowerRestrictions

/-! Critical points of set-sized graphs transfer by a bounded formula. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedCriticalPointFormula : SetTheorySemisentence 3 :=
  “A f k. !IsOrdinal.dfn k ∧ k ∈ A ∧ ¬!boundedPairMemberFormula f k k ∧
    ∀ x ∈ k, !boundedPairMemberFormula f x x”

theorem boundedCriticalPointFormula_bounded : IsBoundedSetFormula boundedCriticalPointFormula :=
  .and (isOrdinalFormula_bounded.subst ![.bvar 2]) (.and (.rel _ _)
    (.and (.neg (boundedPairMemberFormula_bounded.subst ![.bvar 1, .bvar 2, .bvar 2]))
      (.all (.bvar 2) (boundedPairMemberFormula_bounded.subst ![.bvar 2, .bvar 0, .bvar 0]))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def CriticalPointGraphSpec (A f κ : V) : Prop :=
  IsOrdinal κ ∧ κ ∈ A ∧ ⟨κ, κ⟩ₖ ∉ f ∧ ∀ α ∈ κ, ⟨α, α⟩ₖ ∈ f

instance boundedCriticalPointFormula_defined :
    ℒₛₑₜ-relation₃[V] CriticalPointGraphSpec via boundedCriticalPointFormula :=
  ⟨fun v ↦ by simp [boundedCriticalPointFormula, CriticalPointGraphSpec]⟩

theorem criticalPoint_iff_graphSpec {A B f κ : V} [IsTransitive A] (hf : f ∈ B ^ A) :
    IsCriticalPoint A f κ ↔ CriticalPointGraphSpec A f κ := by
  let := IsFunction.of_mem hf
  constructor
  · intro hc
    refine ⟨hc.ordinal, hc.mem_domain, ?_, ?_⟩
    · intro hpair
      exact hc.moved (value_eq_of_kpair_mem hpair)
    · intro α hα
      have hαA := (inferInstance : IsTransitive A).mem_trans hα hc.mem_domain
      have hm := kpair_value_mem (domain_eq_of_mem_function hf |>.symm ▸ hαA)
      rw [hc.fixed_below hα] at hm
      exact hm
  · rintro ⟨hκ, hmem, hmoved, hfix⟩
    apply IsCriticalPoint.of_fixed_below hκ hmem
    · intro he
      have hm := kpair_value_mem (domain_eq_of_mem_function hf |>.symm ▸ hmem)
      rw [he] at hm
      exact hmoved hm
    · intro α hα
      exact value_eq_of_kpair_mem (hfix α hα)

theorem IsCodedMembershipEmbedding.value_criticalPoint {A B f X Y g κ : V}
    [IsTransitive A] [IsTransitive B] [IsTransitive X] [IsTransitive (f ‘ X)]
    (h : IsCodedMembershipEmbedding A B f) (hX : X ∈ A) (hY : Y ∈ A)
    (hg : g ∈ A) (hfunc : g ∈ Y ^ X) (hκ : IsCriticalPoint X g κ) :
    IsCriticalPoint (f ‘ X) (f ‘ g) (f ‘ κ) := by
  have hκA := (inferInstance : IsTransitive A).mem_trans hκ.mem_domain hX
  have hspec := (criticalPoint_iff_graphSpec hfunc).mp hκ
  have he := (h.bounded_defined_iff boundedCriticalPointFormula_bounded
    (fun v ↦ CriticalPointGraphSpec (v 0) (v 1) (v 2)) ![X, g, κ]
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hX, hg, hκA])).mp hspec
  exact (criticalPoint_iff_graphSpec (h.value_function hg hX hY hfunc)).mpr he

end ZFVP
