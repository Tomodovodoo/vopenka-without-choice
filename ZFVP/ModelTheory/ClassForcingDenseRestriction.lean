import ZFVP.ModelTheory.ClassForcingDenseWitnessBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace DefinableForcingTower
variable (T : DefinableForcingTower V)

theorem denseRestriction_definable (D : V → V → Prop)
    (hDdef : ℒₛₑₜ-relation D) (k : V) :
    ℒₛₑₜ-function₁ (fun a ↦ {q ∈ T.boundedConditions k ; D a q}) := by
  have h : ℒₛₑₜ-relation (fun b a : V ↦ ∀ q, q ∈ b ↔ q ∈ T.boundedConditions k ∧ D a q) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = {q ∈ T.boundedConditions k ; D (v 1) q} ↔ _
  rw [mem_ext_iff]
  simp only [mem_sep_iff]

/-- Restrict a set-indexed definable family of classes to a bounded set of
conditions. The resulting graph is a ground set usable as a check parameter. -/
noncomputable def boundedDenseFamily (D : V → V → Prop)
    (hDdef : ℒₛₑₜ-relation D) (I k : V) : V :=
  definableGraph I (fun a ↦ {q ∈ T.boundedConditions k ; D a q})
    (T.denseRestriction_definable D hDdef k)

theorem boundedDenseFamily_function (D : V → V → Prop)
    (hDdef : ℒₛₑₜ-relation D) (I k : V) :
    T.boundedDenseFamily D hDdef I k ∈ (℘ (T.boundedConditions k)) ^ I :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ _ ↦
    mem_power_iff.mpr (fun _ h ↦ (mem_sep_iff.mp h).1))

theorem mem_boundedDenseFamily (D : V → V → Prop)
    (hDdef : ℒₛₑₜ-relation D) {I k a : V} (ha : a ∈ I) (q : V) :
    q ∈ (T.boundedDenseFamily D hDdef I k) ‘ a ↔ q ∈ T.boundedConditions k ∧ D a q := by
  rw [boundedDenseFamily, value_definableGraph _ _ _ ha, mem_sep_iff]

theorem boundedDenseFamily_refinement (D : V → V → Prop)
    (hDdef : ℒₛₑₜ-relation D) {I k p : V} [IsOrdinal k]
    (hpred : ∀ a ∈ I, ∀ r, T.Condition r → T.LE r p →
      ∃ q ∈ T.boundedConditions k, D a q ∧ T.ClassCompatible r q) :
    T.ClassDenseRefinements D I p (T.boundedDenseFamily D hDdef I k) := by
  have hf := T.boundedDenseFamily_function D hDdef I k
  refine ⟨IsFunction.of_mem hf, domain_eq_of_mem_function hf, ?_⟩
  intro a ha
  refine ⟨fun q hq ↦ ((T.mem_boundedDenseFamily D hDdef ha q).mp hq).2,
    ⟨fun q hq ↦ T.boundedConditions_condition ((T.mem_boundedDenseFamily D hDdef ha q).mp hq).1, ?_⟩⟩
  intro r hr hrp
  obtain ⟨q, hq, hDq, hrq⟩ := hpred a ha r hr hrp
  exact ⟨q, (T.mem_boundedDenseFamily D hDdef ha q).mpr ⟨hq, hDq⟩, hrq⟩

end DefinableForcingTower
end ZFVP
