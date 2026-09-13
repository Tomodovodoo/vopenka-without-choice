import ZFVP.SetTheory.UltrapowerStage
import ZFVP.SetTheory.NormalMeasureRegressive
import ZFVP.SetTheory.MeasureSmallClosure

/-! # The seed of the ultrapower by a normal fine measure

For a normal fine measure `U` on `P_κ(lam) = smallSubsetsBelow κ lam` the identity function on the
index set is the seed of the ultrapower: after collapsing it names the pointwise image of `lam`
under the embedding. This module proves the two facts about it before any collapse, in the
vocabulary of `ZFVP.SetTheory.UltrapowerStage`.

Fineness says every constant function with value below `lam` is an a.e. member of the seed.
Normality says the converse: an a.e. member of the seed is a.e. equal to such a constant. Together
with the last theorem here, which says distinct values give distinct constants, this is the whole
description of the a.e. members of the seed.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The identity function on the index set, the seed of the ultrapower. -/
theorem identity_mem_ultraFunctions {P A : V} (hPA : P ⊆ A) :
    SetTheory.identity P ∈ A ^ P := by
  refine mem_function_of_domain_values (IsFunction.identity P)
    (domain_eq_of_mem_function (identity_mem_function P)) ?_
  intro p hp
  rw [identity_value hp]
  exact hPA p hp

/-- The set where a constant function's value lies in the value of the identity is the fine set of
that value. -/
theorem ultraMem_constantGraph_identity_eq (P ξ : V) :
    ultraMem P (constantGraph P ξ) (SetTheory.identity P) = {x ∈ P ; ξ ∈ x} := by
  apply mem_ext
  intro p
  rw [mem_ultraMem_iff, mem_sep_iff]
  constructor
  · rintro ⟨hp, hv⟩
    rw [value_constantGraph P ξ hp, identity_value hp] at hv
    exact ⟨hp, hv⟩
  · rintro ⟨hp, hv⟩
    rw [value_constantGraph P ξ hp, identity_value hp]
    exact ⟨hp, hv⟩

/-- The set where a function's value lies in the value of the identity is its regressive set. -/
theorem ultraMem_identity_eq (P f : V) :
    ultraMem P f (SetTheory.identity P) = {x ∈ P ; f ‘ x ∈ x} := by
  apply mem_ext
  intro p
  rw [mem_ultraMem_iff, mem_sep_iff]
  constructor
  · rintro ⟨hp, hv⟩
    rw [identity_value hp] at hv
    exact ⟨hp, hv⟩
  · rintro ⟨hp, hv⟩
    rw [identity_value hp]
    exact ⟨hp, hv⟩

/-- The set where a function takes the value `ξ` is where it agrees with the constant `ξ`. -/
theorem ultraAgree_constantGraph_right_eq (P f ξ : V) :
    ultraAgree P f (constantGraph P ξ) = {x ∈ P ; f ‘ x = ξ} := by
  apply mem_ext
  intro p
  rw [mem_ultraAgree_iff, mem_sep_iff]
  constructor
  · rintro ⟨hp, hv⟩
    rw [value_constantGraph P ξ hp] at hv
    exact ⟨hp, hv⟩
  · rintro ⟨hp, hv⟩
    rw [value_constantGraph P ξ hp]
    exact ⟨hp, hv⟩

/-- Fineness: the constant function at an ordinal below `lam` is an a.e. member of the seed. -/
theorem ultraMem_constantGraph_identity {κ lam U ξ : V} (hU : IsNormalFineMeasure κ lam U)
    (hξ : ξ ∈ lam) :
    UltraMem (smallSubsetsBelow κ lam) U (constantGraph (smallSubsetsBelow κ lam) ξ)
      (SetTheory.identity (smallSubsetsBelow κ lam)) := by
  unfold UltraMem
  rw [ultraMem_constantGraph_identity_eq]
  exact normalFineMeasure_fine hU hξ

/-- Normality: every a.e. member of the seed is a.e. equal to a constant with value below
`lam`. -/
theorem ultraMem_identity_eq_constant {κ lam U A f : V} (hU : IsNormalFineMeasure κ lam U)
    (h0 : (∅ : V) ∈ lam) (hf : f ∈ A ^ (smallSubsetsBelow κ lam))
    (hmem : UltraMem (smallSubsetsBelow κ lam) U f
      (SetTheory.identity (smallSubsetsBelow κ lam))) :
    ∃ ξ ∈ lam, UltraEq (smallSubsetsBelow κ lam) U f
      (constantGraph (smallSubsetsBelow κ lam) ξ) := by
  have hfun : IsFunction f := IsFunction.of_mem hf
  have hdom : domain f = smallSubsetsBelow κ lam := domain_eq_of_mem_function hf
  have hreg : {x ∈ smallSubsetsBelow κ lam ; f ‘ x ∈ x} ∈ U := by
    have := hmem
    unfold UltraMem at this
    rwa [ultraMem_identity_eq] at this
  obtain ⟨ξ, hξ, hS⟩ := normalFineMeasure_regressive_constant hU h0 hfun hdom hreg
  refine ⟨ξ, hξ, ?_⟩
  unfold UltraEq
  rw [ultraAgree_constantGraph_right_eq]
  exact hS

/-- Two constants below `lam` are a.e. equal only if equal. -/
theorem ultraEq_constant_measure_iff {κ lam U : V} (hU : IsNormalFineMeasure κ lam U) (x y : V) :
    UltraEq (smallSubsetsBelow κ lam) U (constantGraph (smallSubsetsBelow κ lam) x)
      (constantGraph (smallSubsetsBelow κ lam) y) ↔ x = y :=
  ultraEq_constantGraph_iff hU.1 x y

/-- A.e. membership between two constants below `lam` is real membership. -/
theorem ultraMem_constant_measure_iff {κ lam U : V} (hU : IsNormalFineMeasure κ lam U) (x y : V) :
    UltraMem (smallSubsetsBelow κ lam) U (constantGraph (smallSubsetsBelow κ lam) x)
      (constantGraph (smallSubsetsBelow κ lam) y) ↔ x ∈ y :=
  ultraMem_constantGraph_iff hU.1 x y

end ZFVP
