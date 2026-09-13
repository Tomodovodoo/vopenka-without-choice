import ZFVP.SetTheory.IterationLimit
import ZFVP.SetTheory.UniformRecursion
import ZFVP.SetTheory.CardinalSmallUnions

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def ordinalClosureStep (F : V → V) (a f : V) : V := F (a ∪ ⋃ˢ range f)

theorem ordinalClosureStep_definable (F : V → V) (hF : ℒₛₑₜ-function₁ F) (a : V) :
    ℒₛₑₜ-function₁ (ordinalClosureStep F a) := by
  unfold ordinalClosureStep
  definability

noncomputable def ordinalClosureSequence (F : V → V) (hF : ℒₛₑₜ-function₁ F) (a i : V) : V :=
  Replacement.transfiniteRec (ordinalClosureStep F a) (ordinalClosureStep_definable F hF a) i

instance ordinalClosureSequence_definable (F : V → V) (hF : ℒₛₑₜ-function₁ F) (a : V) :
    ℒₛₑₜ-function₁ (ordinalClosureSequence F hF a) :=
  Replacement.transfiniteRec_definable (ordinalClosureStep_definable F hF a)

theorem ordinalClosureSequence_eq (F : V → V) (hF : ℒₛₑₜ-function₁ F) (a i : V) [IsOrdinal i] :
    ordinalClosureSequence F hF a i = F (a ∪ ⋃ˢ repl (ordinalClosureSequence F hF a) (by definability) i) := by
  have hh := Replacement.transfiniteRec_spec (ordinalClosureStep F a)
    (ordinalClosureStep_definable F hF a) (IsOrdinal.toOrdinal i)
  change ordinalClosureSequence F hF a i = ordinalClosureStep F a
    (definableGraph i (ordinalClosureSequence F hF a) (by definability)) at hh
  simpa only [ordinalClosureStep, range_definableGraph] using hh

theorem ordinalClosureSequence_mem {δ a i : V} (hδ : IsRegularCardinal δ)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) (ha : a ∈ δ)
    (hstep : ∀ x ∈ δ, F x ∈ δ) (hi : i ∈ δ) : ordinalClosureSequence F hF a i ∈ δ := by
  let := hδ.1.1
  let := IsOrdinal.of_mem hi
  apply transfinite_induction (fun i ↦ i ∈ δ → ordinalClosureSequence F hF a i ∈ δ)
    (by definability) ?_ (IsOrdinal.toOrdinal i) hi
  intro j ih hj
  have hg : definableGraph j.val (ordinalClosureSequence F hF a) (by definability) ∈ δ ^ j.val :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (by
      intro k hk
      let := IsOrdinal.of_mem hk
      exact ih (IsOrdinal.toOrdinal k) hk (IsOrdinal.toIsTransitive.mem_trans hk hj))
  have hu := union_range_below_cofinality (hδ.2.2.symm ▸ hj) hg
  rw [range_definableGraph] at hu
  rw [ordinalClosureSequence_eq]
  exact hstep _ (ordinal_union_mem ha hu)

theorem ordinalClosureSequence_increasing {δ a i j : V} (hδ : IsRegularCardinal δ)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) (ha : a ∈ δ)
    (hstep : ∀ x ∈ δ, F x ∈ δ ∧ x ∈ F x) (hj : j ∈ δ) (hij : i ∈ j) :
    ordinalClosureSequence F hF a i ∈ ordinalClosureSequence F hF a j := by
  let := hδ.1.1
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hij
  have hg : definableGraph j (ordinalClosureSequence F hF a) (by definability) ∈ δ ^ j :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun k hk ↦
      ordinalClosureSequence_mem hδ F hF ha (fun x hx ↦ (hstep x hx).1)
        (IsOrdinal.toIsTransitive.mem_trans hk hj))
  have hu := union_range_below_cofinality (hδ.2.2.symm ▸ hj) hg
  rw [range_definableGraph] at hu
  have hb := ordinal_union_mem ha hu
  let := IsOrdinal.of_mem hb
  let := IsOrdinal.of_mem (hstep _ hb).1
  let := IsOrdinal.of_mem (ordinalClosureSequence_mem hδ F hF ha
    (fun x hx ↦ (hstep x hx).1) (IsOrdinal.toIsTransitive.mem_trans hij hj))
  rw [ordinalClosureSequence_eq F hF a j]
  apply ordinal_mem_of_subset_mem (subset_trans ?_ (subset_union_right _ _)) (hstep _ hb).2
  exact subset_sUnion_of_mem ((repl_spec (ordinalClosureSequence_definable F hF a)).mpr ⟨i, hij, rfl⟩)

end ZFVP
