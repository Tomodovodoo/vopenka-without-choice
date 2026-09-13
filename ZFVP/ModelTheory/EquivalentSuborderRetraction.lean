import ZFVP.ModelTheory.ForcingProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Fix the suborder pointwise while retaining the specified equivalent
representative on conditions outside it. -/
noncomputable def equivalentSuborderFix (N f q : V) : V := by
  classical
  exact if q ∈ N then q else f ‘ q

instance equivalentSuborderFix_definable (N f : V) :
    ℒₛₑₜ-function₁[V] (equivalentSuborderFix N f) := by
  have h : ℒₛₑₜ-relation (fun y q : V ↦ (q ∈ N ∧ y = q) ∨ (q ∉ N ∧ y = f ‘ q)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = equivalentSuborderFix N f (v 1) ↔ _
  classical
  by_cases hv : v 1 ∈ N <;> simp [equivalentSuborderFix, hv]

noncomputable def equivalentSuborderRetraction (P N f : V) : V :=
  definableGraph P (equivalentSuborderFix N f) (by infer_instance)

theorem equivalentSuborderRetraction_value {P N f p : V} (hp : p ∈ P) :
    (equivalentSuborderRetraction P N f) ‘ p = equivalentSuborderFix N f p :=
  value_definableGraph _ _ _ hp

theorem equivalentSuborderRetraction_function {P N f : V} (hf : f ∈ N ^ P) :
    equivalentSuborderRetraction P N f ∈ N ^ P := by
  apply definableGraph_mem_function_of_mapsTo
  intro p hp
  classical
  by_cases hn : p ∈ N
  · simp [equivalentSuborderFix, hn]
  · simpa [equivalentSuborderFix, hn] using function_value_mem hf hp

theorem equivalentSuborderRetraction_fixes {P N f p : V} (hN : N ⊆ P) (hp : p ∈ N) :
    (equivalentSuborderRetraction P N f) ‘ p = p := by
  rw [equivalentSuborderRetraction_value (hN p hp)]
  simp [equivalentSuborderFix, hp]

theorem equivalentSuborderRetraction_equivalent {P R N f p : V}
    (hR : IsForcingPreorder P R)
    (he : ∀ q ∈ P, ⟨f ‘ q, q⟩ₖ ∈ R ∧ ⟨q, f ‘ q⟩ₖ ∈ R) (hp : p ∈ P) :
    ⟨(equivalentSuborderRetraction P N f) ‘ p, p⟩ₖ ∈ R ∧
      ⟨p, (equivalentSuborderRetraction P N f) ‘ p⟩ₖ ∈ R := by
  rw [equivalentSuborderRetraction_value hp]
  classical
  by_cases hn : p ∈ N
  · simpa [equivalentSuborderFix, hn] using And.intro (hR.2.1 p hp) (hR.2.1 p hp)
  · simpa [equivalentSuborderFix, hn] using he p hp

theorem equivalentSuborderRetraction_spec {P R N S f : V}
    (hR : IsForcingPreorder P R) (hN : N ⊆ P)
    (hrel : ∀ n ∈ N, ∀ m ∈ N, ⟨n, m⟩ₖ ∈ S ↔ ⟨n, m⟩ₖ ∈ R)
    (hf : f ∈ N ^ P) (he : ∀ q ∈ P, ⟨f ‘ q, q⟩ₖ ∈ R ∧ ⟨q, f ‘ q⟩ₖ ∈ R) :
    IsForcingRetraction N S P R (equivalentSuborderRetraction P N f) := by
  let r := equivalentSuborderRetraction P N f
  have hm := equivalentSuborderRetraction_function hf
  have hr (p : V) (hp : p ∈ P) : r ‘ p ∈ N := function_value_mem hm hp
  have heq (p : V) (hp : p ∈ P) : ⟨r ‘ p, p⟩ₖ ∈ R ∧ ⟨p, r ‘ p⟩ₖ ∈ R :=
    equivalentSuborderRetraction_equivalent hR he hp
  refine ⟨hm, hN, fun _ hp ↦ equivalentSuborderRetraction_fixes hN hp, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    apply (hrel _ (hr p hp) _ (hr q hq)).mpr
    exact hR.2.2 _ (hN _ (hr p hp)) p hp _ (hN _ (hr q hq)) (heq p hp).1
      (hR.2.2 p hp q hq _ (hN _ (hr q hq)) hpq (heq q hq).2)
  · intro p hp n hn
    rw [hrel _ (hr p hp) n hn]
    exact ⟨fun h ↦ hR.2.2 _ (hN _ (hr p hp)) p hp n (hN n hn) (heq p hp).1 h,
      fun h ↦ hR.2.2 p hp _ (hN _ (hr p hp)) n (hN n hn) (heq p hp).2 h⟩
  · intro p hp n hn hnp
    exact ⟨n, hN n hn,
      hR.2.2 n (hN n hn) _ (hN _ (hr p hp)) p hp ((hrel n hn _ (hr p hp)).mp hnp) (heq p hp).1,
      equivalentSuborderRetraction_fixes hN hn⟩

end ZFVP
