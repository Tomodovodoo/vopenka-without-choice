import ZFVP.SetTheory.InaccessibleFunctionClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def functionRestrictionClosedFormula : SetTheorySemisentence 1 :=
  “b. ∀ D ∈ b, ∀ f ∈ b, !boundedFunctionFormula f D b →
    ∀ d ∈ b, !isSubsetOf d D → ∃ r ∈ b,
      !boundedFunctionFormula r d b ∧ !isSubsetOf r f”

theorem functionRestrictionClosedFormula_bounded : IsBoundedSetFormula functionRestrictionClosedFormula :=
  .all (.bvar 0) (.all (.bvar 1) (.or (boundedFunctionFormula_bounded.subst _).neg
    (.all (.bvar 2) (.or (isSubsetOf_bounded.subst _).neg
      (.exs (.bvar 3) (.and (boundedFunctionFormula_bounded.subst _) (isSubsetOf_bounded.subst _)))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsFunctionRestrictionClosed (b : V) : Prop :=
  ∀ D ∈ b, ∀ f ∈ b, f ∈ b ^ D → ∀ d ∈ b, d ⊆ D → ∃ r ∈ b, r ∈ b ^ d ∧ r ⊆ f

instance functionRestrictionClosedFormula_defined :
    ℒₛₑₜ-predicate[V] IsFunctionRestrictionClosed via functionRestrictionClosedFormula :=
  ⟨fun v ↦ by simp [functionRestrictionClosedFormula, IsFunctionRestrictionClosed]⟩

theorem IsChoicelessInaccessible.functionRestrictionClosed {δ : V} (hδ : IsChoicelessInaccessible δ) :
    IsFunctionRestrictionClosed (hierarchy δ) := by
  let := hδ.1
  intro D _hD f hf hfD d _hd hdD
  exact ⟨f ↾ d, subset_mem_hierarchy_limit hδ.rankCriterion.2.2.1 hf (restrict_subset _ _),
    function_restrict_mem hfD hdD, restrict_subset _ _⟩

theorem IsFunctionRestrictionClosed.function_mem {b D d f : V}
    (hb : IsFunctionRestrictionClosed b) (hclosed : b ^ D ⊆ b)
    (hD : D ∈ b) (hd : d ∈ b) (hdD : d ⊆ D) (hne : IsNonempty b) (hf : f ∈ b ^ d) : f ∈ b := by
  classical
  obtain ⟨z, hz⟩ := hne.nonempty
  let F := fun x ↦ if x ∈ d then f ‘ x else z
  have hF : ℒₛₑₜ-function₁ F := by
    have ht : ℒₛₑₜ-relation (fun y x : V ↦ (x ∈ d ∧ y = f ‘ x) ∨ (x ∉ d ∧ y = z)) := by definability
    apply Language.Definable.of_iff ht
    intro v
    change v 0 = F (v 1) ↔ _
    by_cases hv : v 1 ∈ d <;> simp [F, hv]
  let g := definableGraph D F hF
  have hg : g ∈ b ^ D := by
    apply definableGraph_mem_function_of_mapsTo
    intro x _hx
    dsimp [F]
    split_ifs with h
    · exact function_value_mem hf h
    · exact hz
  obtain ⟨r, hr, hrf, hrsub⟩ := hb D hD g (hclosed g hg) hg d hd hdD
  have he : r = f := by
    let := IsFunction.of_mem hrf
    let := IsFunction.of_mem hg
    apply function_eq_of_values hrf hf
    intro x hx
    have hgr : g ‘ x = r ‘ x := value_eq_of_kpair_mem
      (hrsub _ (kpair_value_mem ((domain_eq_of_mem_function hrf).symm ▸ hx)))
    rw [← hgr]
    have hval : g ‘ x = F x := value_definableGraph D F hF (hdD x hx)
    exact hval.trans (by simp [F, hx])
  exact he ▸ hr

end ZFVP
