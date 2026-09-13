import ZFVP.SetTheory.UniformCollapse
import ZFVP.SetTheory.MeasuredWellFounded

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem membershipRelation_predecessors {C x : V} (hC : IsTransitive C) (hx : x ∈ C) :
    predecessors (membershipRelation C) C x = x := by
  apply SetTheory.mem_ext_iff.mpr
  intro y
  simp only [mem_predecessors_iff, pair_mem_membershipRelation]
  exact ⟨fun h ↦ h.2.2.2, fun h ↦ ⟨hC.transitive x hx y h, hC.transitive x hx y h, hx, h⟩⟩

def IsMembershipRecursion (C : V) (F : V → V → V) (f : V) : Prop :=
  IsFunction f ∧ domain f = C ∧ ∀ x ∈ C, f ‘ x = F x (f ↾ x)

theorem isMembershipRecursion_definable (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) :
    ℒₛₑₜ-relation (fun C f ↦ IsMembershipRecursion C F f) := by
  unfold IsMembershipRecursion
  definability

theorem membershipRecursion_exists {C : V} (hC : IsTransitive C)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) : ∃ f, IsMembershipRecursion C F f := by
  let f := wellFoundedRecursion (membershipRelation_wellFounded C) F hF
  refine ⟨f, wellFoundedRecursion_isFunction _ _ _, domain_wellFoundedRecursion _ _ _, ?_⟩
  intro x hx
  change (wellFoundedRecursion _ _ _) ‘ x = _
  rw [wellFoundedRecursion_value _ _ _ hx, membershipRelation_predecessors hC hx]

theorem membershipRecursion_coherent {C D : V} (hC : IsTransitive C) (hD : IsTransitive D)
    {F : V → V → V} {f g : V} (hf : IsMembershipRecursion C F f)
    (hg : IsMembershipRecursion D F g) : ∀ x ∈ C, x ∈ D → f ‘ x = g ‘ x := by
  have : IsFunction f := hf.1
  have : IsFunction g := hg.1
  apply projectedRank_induction C (fun x : V ↦ x) (by definability)
    (fun x ↦ x ∈ D → f ‘ x = g ‘ x) (by definability)
  intro x hx ih hxD
  rw [hf.2.2 x hx, hg.2.2 x hxD]
  congr 1
  apply restrict_eq_of_values
  · simpa only [hf.2.1] using hC.transitive x hx
  · simpa only [hg.2.1] using hD.transitive x hxD
  · intro y hy
    exact ih y (hC.transitive x hx y hy) (rank_mem hy) (hD.transitive x hxD y hy)

theorem membershipRecursion_unique {C : V} (hC : IsTransitive C)
    {F : V → V → V} {f g : V} (hf : IsMembershipRecursion C F f)
    (hg : IsMembershipRecursion C F g) : f = g := by
  have : IsFunction f := hf.1
  have : IsFunction g := hg.1
  apply functions_eq_of_domain_values (hf.2.1.trans hg.2.1.symm)
  intro x hx
  have hxC : x ∈ C := hf.2.1 ▸ hx
  exact membershipRecursion_coherent hC hC hf hg x hxC hxC

noncomputable def membershipRecursionTable (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (x : V) : V :=
  Classical.choose (membershipRecursion_exists (transitiveClosure_transitive ({x} : V)) F hF)

theorem membershipRecursionTable_spec (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (x : V) :
    IsMembershipRecursion (transitiveClosure ({x} : V)) F (membershipRecursionTable F hF x) :=
  Classical.choose_spec (membershipRecursion_exists (transitiveClosure_transitive ({x} : V)) F hF)

theorem membershipRecursionTable_eq_iff (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (x f : V) :
    f = membershipRecursionTable F hF x ↔ IsMembershipRecursion (transitiveClosure ({x} : V)) F f := by
  constructor
  · rintro rfl
    exact membershipRecursionTable_spec F hF x
  · intro hf
    exact membershipRecursion_unique (transitiveClosure_transitive _) hf (membershipRecursionTable_spec F hF x)

instance membershipRecursionTable_definable (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) :
    ℒₛₑₜ-function₁ (membershipRecursionTable F hF) := by
  have hD := isMembershipRecursion_definable F hF
  have h : ℒₛₑₜ-relation (fun f x ↦ IsMembershipRecursion (transitiveClosure ({x} : V)) F f) := by definability
  apply Language.Definable.of_iff h
  intro v
  exact membershipRecursionTable_eq_iff F hF (v 1) (v 0)

noncomputable def membershipRecursion (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (x : V) : V :=
  (membershipRecursionTable F hF x) ‘ x

instance membershipRecursion_definable (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) :
    ℒₛₑₜ-function₁ (membershipRecursion F hF) := by
  unfold membershipRecursion
  definability

theorem membershipRecursionTable_value (F : V → V → V) (hF : ℒₛₑₜ-function₂ F)
    {x y : V} (hy : y ∈ transitiveClosure ({x} : V)) :
    (membershipRecursionTable F hF x) ‘ y = membershipRecursion F hF y :=
  membershipRecursion_coherent (transitiveClosure_transitive _) (transitiveClosure_transitive _)
    (membershipRecursionTable_spec F hF x) (membershipRecursionTable_spec F hF y)
    y hy (subset_transitiveClosure _ _ (by simp))

theorem membershipRecursion_equation (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (x : V) :
    membershipRecursion F hF x = F x (definableGraph x (membershipRecursion F hF) (by definability)) := by
  have hf := membershipRecursionTable_spec F hF x
  have : IsFunction (membershipRecursionTable F hF x) := hf.1
  have hx : x ∈ transitiveClosure ({x} : V) := subset_transitiveClosure _ _ (by simp)
  have hsub : x ⊆ transitiveClosure ({x} : V) := (transitiveClosure_transitive _).transitive x hx
  rw [membershipRecursion, hf.2.2 x hx]
  congr 1
  apply functions_eq_of_domain_values
  · rw [domain_restrict_eq, hf.2.1, domain_definableGraph]
    apply SetTheory.mem_ext_iff.mpr
    intro y
    simp only [mem_inter_iff]
    exact ⟨And.right, fun h ↦ ⟨hsub y h, h⟩⟩
  · intro y hy
    rw [domain_restrict_eq] at hy
    have hs : y ∈ x := (mem_inter_iff.mp hy).2
    rw [value_restrict (mem_inter_iff.mp hy).1 hs, value_definableGraph _ _ _ hs]
    exact membershipRecursionTable_value F hF (hsub y hs)

end ZFVP
