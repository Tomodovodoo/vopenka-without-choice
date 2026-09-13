import ZFVP.SetTheory.NameHierarchyTableFormula
import ZFVP.SetTheory.FunctionValue

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem nameHierarchyTable_row_eq {f a T P : V} [IsOrdinal a]
    (ht : piOneNameHierarchyTableFormula.Evalb ![f, a, T, P])
    {β X : V} (hβ : β ∈ a) (hX : ⟨β, X⟩ₖ ∈ f) :
    X = forcingNameHierarchy P β := by
  obtain ⟨hf, hr⟩ := (eval_piOneNameHierarchyTableFormula f a T P).mp ht
  have hall := transfinite_induction
    (fun β ↦ β ∈ a → ∀ X, ⟨β, X⟩ₖ ∈ f → X = forcingNameHierarchy P β)
    (by definability) ?_
  · let := IsOrdinal.of_mem hβ
    exact hall (IsOrdinal.toOrdinal β) hβ X hX
  intro β ih hb X hx
  have hXT := (mem_of_mem_functions hf hx).2
  apply mem_ext
  intro ν
  rw [hr β hb X hXT hx ν, mem_forcingNameHierarchy]
  constructor
  · rintro ⟨γ, hg, Y, _, hy, hν⟩
    let := IsOrdinal.of_mem hg
    have hga := IsOrdinal.toIsTransitive.transitive _ hb γ hg
    rw [ih (IsOrdinal.toOrdinal γ) hg hga Y hy] at hν
    exact ⟨γ, hg, hν⟩
  · rintro ⟨γ, hg, hν⟩
    let := IsOrdinal.of_mem hg
    have hga := IsOrdinal.toIsTransitive.transitive _ hb γ hg
    obtain ⟨Y, hY, hy⟩ := exists_of_mem_function hf γ hga
    refine ⟨γ, hg, Y, hY, hy, ?_⟩
    rwa [ih (IsOrdinal.toOrdinal γ) hg hga Y hy]

theorem nameHierarchyTable_exists (P a : V) [IsOrdinal a] :
    piOneNameHierarchyTableFormula.Evalb
      ![definableGraph a (forcingNameHierarchy P) (by definability), a,
        repl (forcingNameHierarchy P) (by definability) a, P] := by
  apply (eval_piOneNameHierarchyTableFormula _ _ _ _).mpr
  refine ⟨definableGraph_mem_function _ _ _, ?_⟩
  intro β hb X _ hx ν
  obtain ⟨_, rfl⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hx
  let := IsOrdinal.of_mem hb
  rw [mem_forcingNameHierarchy]
  constructor
  · rintro ⟨γ, hg, hν⟩
    have hga := IsOrdinal.toIsTransitive.transitive _ hb γ hg
    exact ⟨γ, hg, forcingNameHierarchy P γ,
      (repl_spec _).mpr ⟨γ, hga, rfl⟩,
      (pair_mem_definableGraph_iff _ _ _ _ _).mpr ⟨hga, rfl⟩, hν⟩
  · rintro ⟨γ, hg, Y, _, hy, hν⟩
    obtain ⟨_, rfl⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hy
    exact ⟨γ, hg, hν⟩

end ZFVP

