import ZFVP.SetTheory.ForcingNames
import ZFVP.SetTheory.WellFoundedRecursion

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def subnameRelation (C : V) : V :=
  {z ∈ C ×ˢ C ; kpair.π₁ z ∈ domain (kpair.π₂ z)}

theorem pair_mem_subnameRelation (C σ τ : V) :
    ⟨σ, τ⟩ₖ ∈ subnameRelation C ↔ σ ∈ C ∧ τ ∈ C ∧ σ ∈ domain τ := by
  simp [subnameRelation, and_assoc]

theorem subnameRelation_wellFounded (C : V) : IsInternallyWellFounded (subnameRelation C) C := by
  apply rank_decreasing_internallyWellFounded
  intro σ _ τ _ hστ
  obtain ⟨p, hp⟩ := mem_domain_iff.mp ((pair_mem_subnameRelation C σ τ).mp hστ).2.2
  exact rank_subname_lt hp

theorem subnameRelation_predecessors {C τ : V} (hC : IsSubnameClosed C) (hτ : τ ∈ C) :
    predecessors (subnameRelation C) C τ = domain τ := by
  apply SetTheory.mem_ext_iff.mpr
  intro σ
  simp only [mem_predecessors_iff, pair_mem_subnameRelation]
  exact ⟨fun h ↦ h.2.2.2, fun h ↦ ⟨hC τ hτ σ h, hC τ hτ σ h, hτ, h⟩⟩

def IsSubnameRecursion (C : V) (F : V → V → V) (f : V) : Prop :=
  IsFunction f ∧ domain f = C ∧ ∀ τ ∈ C, f ‘ τ = F τ (f ↾ (domain τ))

theorem isSubnameRecursion_definable (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) :
    ℒₛₑₜ-relation (fun C f ↦ IsSubnameRecursion C F f) := by
  unfold IsSubnameRecursion
  definability

theorem subnameRecursion_exists {C : V} (hC : IsSubnameClosed C)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) : ∃ f, IsSubnameRecursion C F f := by
  let f := wellFoundedRecursion (subnameRelation_wellFounded C) F hF
  refine ⟨f, wellFoundedRecursion_isFunction _ _ _, domain_wellFoundedRecursion _ _ _, ?_⟩
  intro τ hτ
  change (wellFoundedRecursion _ _ _) ‘ τ = _
  rw [wellFoundedRecursion_value _ _ _ hτ, subnameRelation_predecessors hC hτ]

theorem subnameRecursion_coherent {C D : V} (hC : IsSubnameClosed C) (hD : IsSubnameClosed D)
    {F : V → V → V} {f g : V} (hf : IsSubnameRecursion C F f)
    (hg : IsSubnameRecursion D F g) : ∀ τ ∈ C, τ ∈ D → f ‘ τ = g ‘ τ := by
  have : IsFunction f := hf.1
  have : IsFunction g := hg.1
  apply projectedRank_induction C (fun x : V ↦ x) (by definability)
    (fun τ ↦ τ ∈ D → f ‘ τ = g ‘ τ) (by definability)
  intro τ hτ ih hτD
  rw [hf.2.2 τ hτ, hg.2.2 τ hτD]
  congr 1
  apply restrict_eq_of_values
  · simpa only [hf.2.1] using hC τ hτ
  · simpa only [hg.2.1] using hD τ hτD
  · intro σ hσ
    obtain ⟨p, hp⟩ := mem_domain_iff.mp hσ
    exact ih σ (hC τ hτ σ hσ) (rank_subname_lt hp) (hD τ hτD σ hσ)

theorem subnameRecursion_unique {C : V} (hC : IsSubnameClosed C)
    {F : V → V → V} {f g : V} (hf : IsSubnameRecursion C F f)
    (hg : IsSubnameRecursion C F g) : f = g := by
  have : IsFunction f := hf.1
  have : IsFunction g := hg.1
  apply functions_eq_of_domain_values (hf.2.1.trans hg.2.1.symm)
  intro τ hτ
  have hτC : τ ∈ C := hf.2.1 ▸ hτ
  exact subnameRecursion_coherent hC hC hf hg τ hτC hτC

noncomputable def subnameRecursionTable (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (τ : V) : V :=
  Classical.choose (subnameRecursion_exists (nameClosure_closed τ) F hF)

theorem subnameRecursionTable_spec (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (τ : V) :
    IsSubnameRecursion (nameClosure τ) F (subnameRecursionTable F hF τ) :=
  Classical.choose_spec (subnameRecursion_exists (nameClosure_closed τ) F hF)

theorem subnameRecursionTable_eq_iff (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (τ f : V) :
    f = subnameRecursionTable F hF τ ↔ IsSubnameRecursion (nameClosure τ) F f := by
  constructor
  · rintro rfl
    exact subnameRecursionTable_spec F hF τ
  · intro hf
    exact subnameRecursion_unique (nameClosure_closed τ) hf (subnameRecursionTable_spec F hF τ)

instance subnameRecursionTable_definable (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) :
    ℒₛₑₜ-function₁ (subnameRecursionTable F hF) := by
  have hD := isSubnameRecursion_definable F hF
  have h : ℒₛₑₜ-relation (fun f τ ↦ IsSubnameRecursion (nameClosure τ) F f) := by definability
  apply Language.Definable.of_iff h
  intro v
  exact subnameRecursionTable_eq_iff F hF (v 1) (v 0)

noncomputable def subnameRecursion (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (τ : V) : V :=
  (subnameRecursionTable F hF τ) ‘ τ

instance subnameRecursion_definable (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) :
    ℒₛₑₜ-function₁ (subnameRecursion F hF) := by
  unfold subnameRecursion
  definability

theorem subnameRecursionTable_value (F : V → V → V) (hF : ℒₛₑₜ-function₂ F)
    {σ τ : V} (hσ : σ ∈ nameClosure τ) :
    (subnameRecursionTable F hF τ) ‘ σ = subnameRecursion F hF σ :=
  subnameRecursion_coherent (nameClosure_closed τ) (nameClosure_closed σ)
    (subnameRecursionTable_spec F hF τ) (subnameRecursionTable_spec F hF σ)
    σ hσ (mem_nameClosure_self σ)

theorem subnameRecursion_equation (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) (τ : V) :
    subnameRecursion F hF τ = F τ (definableGraph (domain τ) (subnameRecursion F hF) (by definability)) := by
  have hf := subnameRecursionTable_spec F hF τ
  have : IsFunction (subnameRecursionTable F hF τ) := hf.1
  rw [subnameRecursion, hf.2.2 τ (mem_nameClosure_self τ)]
  congr 1
  apply functions_eq_of_domain_values
  · rw [domain_restrict_eq, hf.2.1, domain_definableGraph]
    apply SetTheory.mem_ext_iff.mpr
    intro σ
    simp only [mem_inter_iff]
    exact ⟨And.right, fun h ↦ ⟨nameClosure_closed τ τ (mem_nameClosure_self τ) σ h, h⟩⟩
  · intro σ hσ
    rw [domain_restrict_eq] at hσ
    have hs : σ ∈ domain τ := (mem_inter_iff.mp hσ).2
    rw [value_restrict (mem_inter_iff.mp hσ).1 hs, value_definableGraph _ _ _ hs]
    exact subnameRecursionTable_value F hF (nameClosure_closed τ τ (mem_nameClosure_self τ) σ hs)

end ZFVP
