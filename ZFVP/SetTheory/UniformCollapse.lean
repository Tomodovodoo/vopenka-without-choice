import ZFVP.SetTheory.MostowskiCollapse

/-! A definable total collapse operation, with its valid-input contract explicit. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def mostowskiMap (R D : V) : V := by
  classical
  exact if hR : IsInternallyWellFounded R D then collapseGraph hR else ∅

theorem mostowskiMap_of_wellFounded {R D : V} (hR : IsInternallyWellFounded R D) :
    mostowskiMap R D = collapseGraph hR := by simp [mostowskiMap, hR]

theorem mostowskiMap_eq_iff (R D f : V) : mostowskiMap R D = f ↔
    (IsInternallyWellFounded R D ∧ IsRecursionAttempt R D (fun _ g ↦ range g) f ∧ domain f = D) ∨
    (¬IsInternallyWellFounded R D ∧ f = ∅) := by
  by_cases hR : IsInternallyWellFounded R D
  · simp only [mostowskiMap_of_wellFounded hR, hR, true_and, not_true_eq_false, false_and, or_false]
    exact wellFoundedRecursion_eq_iff hR _ _ f
  · simp [mostowskiMap, hR, eq_comm]

instance mostowskiMap_definable : ℒₛₑₜ-function₂[V] mostowskiMap := by
  have h : ℒₛₑₜ-relation₃ (fun f R D : V ↦
      (IsInternallyWellFounded R D ∧ IsRecursionAttempt R D (fun _ g ↦ range g) f ∧ domain f = D) ∨
      (¬IsInternallyWellFounded R D ∧ f = ∅)) := by
    unfold IsRecursionAttempt
    definability
  apply Language.Definable.of_iff h
  intro v
  exact eq_comm.trans (mostowskiMap_eq_iff (v 1) (v 2) (v 0))

theorem mostowskiMap_isTransitiveCollapse {R D : V} (hR : IsInternallyWellFounded R D)
    (hext : IsExtensionalOn R D) :
    IsTransitiveCollapse R D (range (mostowskiMap R D)) (mostowskiMap R D) := by
  rw [mostowskiMap_of_wellFounded hR]
  exact collapseGraph_isTransitiveCollapse hR hext

noncomputable def membershipRelation (D : V) : V :=
  {p ∈ D ×ˢ D ; kpair.π₁ p ∈ kpair.π₂ p}

instance membershipRelation_definable : ℒₛₑₜ-function₁[V] membershipRelation := by
  have h : ℒₛₑₜ-relation (fun R D : V ↦ ∀ p, p ∈ R ↔ p ∈ D ×ˢ D ∧ kpair.π₁ p ∈ kpair.π₂ p) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = membershipRelation (v 1) ↔ _
  rw [mem_ext_iff]
  simp [membershipRelation]

@[simp] theorem pair_mem_membershipRelation (D x y : V) :
    ⟨x, y⟩ₖ ∈ membershipRelation D ↔ x ∈ D ∧ y ∈ D ∧ x ∈ y := by
  simp [membershipRelation, and_assoc]

theorem membershipRelation_wellFounded (D : V) : IsInternallyWellFounded (membershipRelation D) D := by
  apply rank_decreasing_internallyWellFounded
  intro x _ y _ hxy
  exact rank_mem ((pair_mem_membershipRelation D x y).mp hxy).2.2

theorem membershipRelation_extensional (D : V) [IsTransitive D] : IsExtensionalOn (membershipRelation D) D := by
  intro x hx y hy h
  apply mem_ext
  intro z
  constructor
  · intro hz
    have hzD := (inferInstance : IsTransitive D).mem_trans hz hx
    exact ((pair_mem_membershipRelation D z y).mp ((h z hzD).mp
      ((pair_mem_membershipRelation D z x).mpr ⟨hzD, hx, hz⟩))).2.2
  · intro hz
    have hzD := (inferInstance : IsTransitive D).mem_trans hz hy
    exact ((pair_mem_membershipRelation D z x).mp ((h z hzD).mpr
      ((pair_mem_membershipRelation D z y).mpr ⟨hzD, hy, hz⟩))).2.2

theorem collapse_membership_value (D : V) [IsTransitive D] :
    ∀ x ∈ D, (mostowskiMap (membershipRelation D) D) ‘ x = x := by
  rw [mostowskiMap_of_wellFounded (membershipRelation_wellFounded D)]
  apply internalWellFounded_induction (membershipRelation_wellFounded D)
    (fun x ↦ (collapseGraph (membershipRelation_wellFounded D)) ‘ x = x) (by definability)
  intro x hx ih
  apply mem_ext
  intro z
  rw [mem_collapseGraph_value _ hx]
  constructor
  · rintro ⟨y, hy, hyx, hval⟩
    rw [ih y hy hyx] at hval
    exact hval ▸ ((pair_mem_membershipRelation D y x).mp hyx).2.2
  · intro hz
    have hzD := (inferInstance : IsTransitive D).mem_trans hz hx
    have hzx := (pair_mem_membershipRelation D z x).mpr ⟨hzD, hx, hz⟩
    exact ⟨z, hzD, hzx, ih z hzD hzx⟩

end ZFVP
