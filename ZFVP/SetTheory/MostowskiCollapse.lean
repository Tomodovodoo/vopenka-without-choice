import ZFVP.SetTheory.WellFoundedRecursion

/-! Mostowski collapse for internal extensional well-founded set relations.
Well-foundedness is tested on internal subsets; no external well-foundedness
of the ambient model is used. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsExtensionalOn (R D : V) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, (∀ z ∈ D, ⟨z, x⟩ₖ ∈ R ↔ ⟨z, y⟩ₖ ∈ R) → x = y

instance isExtensionalOn_definable : ℒₛₑₜ-relation[V] IsExtensionalOn := by
  unfold IsExtensionalOn
  definability

noncomputable def collapseGraph {R D : V} (hR : IsInternallyWellFounded R D) : V :=
  wellFoundedRecursion hR (fun _ g ↦ range g) (by definability)

instance collapseGraph_isFunction {R D : V} (hR : IsInternallyWellFounded R D) :
    IsFunction (collapseGraph hR) := wellFoundedRecursion_isFunction _ _ _

@[simp] theorem domain_collapseGraph {R D : V} (hR : IsInternallyWellFounded R D) :
    domain (collapseGraph hR) = D := domain_wellFoundedRecursion _ _ _

theorem collapseGraph_value {R D x : V} (hR : IsInternallyWellFounded R D) (hx : x ∈ D) :
    (collapseGraph hR) ‘ x = range ((collapseGraph hR) ↾ (predecessors R D x)) :=
  wellFoundedRecursion_value hR _ _ hx

theorem mem_collapseGraph_value {R D x z : V} (hR : IsInternallyWellFounded R D) (hx : x ∈ D) :
    z ∈ (collapseGraph hR) ‘ x ↔ ∃ y ∈ D, ⟨y, x⟩ₖ ∈ R ∧ (collapseGraph hR) ‘ y = z := by
  rw [collapseGraph_value hR hx, mem_range_iff]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨hyf, hyp⟩ := kpair_mem_restrict_iff.mp hy
    obtain ⟨hyD, hyx⟩ := (mem_predecessors_iff _ _ _ _).mp hyp
    exact ⟨y, hyD, hyx, value_eq_of_kpair_mem hyf⟩
  · rintro ⟨y, hyD, hyx, rfl⟩
    exact ⟨y, kpair_mem_restrict_iff.mpr ⟨kpair_value_mem (by simpa using hyD),
      (mem_predecessors_iff _ _ _ _).mpr ⟨hyD, hyx⟩⟩⟩

theorem collapseGraph_injective {R D : V} (hR : IsInternallyWellFounded R D)
    (hext : IsExtensionalOn R D) :
    ∀ x ∈ D, ∀ y ∈ D, (collapseGraph hR) ‘ x = (collapseGraph hR) ‘ y → x = y := by
  apply internalWellFounded_induction hR
    (fun x ↦ ∀ y ∈ D, (collapseGraph hR) ‘ x = (collapseGraph hR) ‘ y → x = y) (by definability)
  intro x hx ih y hy heq
  apply hext x hx y hy
  intro z hz
  constructor
  · intro hzx
    have hm : (collapseGraph hR) ‘ z ∈ (collapseGraph hR) ‘ y :=
      heq ▸ (mem_collapseGraph_value hR hx).mpr ⟨z, hz, hzx, rfl⟩
    obtain ⟨w, hw, hwy, hval⟩ := (mem_collapseGraph_value hR hy).mp hm
    have hzw := ih z hz hzx w hw hval.symm
    exact hzw.symm ▸ hwy
  · intro hzy
    have hm : (collapseGraph hR) ‘ z ∈ (collapseGraph hR) ‘ x :=
      heq.symm ▸ (mem_collapseGraph_value hR hy).mpr ⟨z, hz, hzy, rfl⟩
    obtain ⟨w, hw, hwx, hval⟩ := (mem_collapseGraph_value hR hx).mp hm
    have hwz := ih w hw hwx z hz hval
    exact hwz ▸ hwx

theorem collapseGraph_membership_iff {R D x y : V} (hR : IsInternallyWellFounded R D)
    (hext : IsExtensionalOn R D) (hx : x ∈ D) (hy : y ∈ D) :
    (collapseGraph hR) ‘ x ∈ (collapseGraph hR) ‘ y ↔ ⟨x, y⟩ₖ ∈ R := by
  rw [mem_collapseGraph_value hR hy]
  constructor
  · rintro ⟨z, hz, hzy, hval⟩
    exact collapseGraph_injective hR hext z hz x hx hval ▸ hzy
  · intro hxy
    exact ⟨x, hx, hxy, rfl⟩

theorem collapseGraph_range_transitive {R D : V} (hR : IsInternallyWellFounded R D) :
    IsTransitive (range (collapseGraph hR)) := by
  constructor
  intro x hx z hzx
  obtain ⟨y, hy⟩ := mem_range_iff.mp hx
  have hyD : y ∈ D := by simpa using mem_domain_of_kpair_mem hy
  have heq := value_eq_of_kpair_mem hy
  rw [← heq] at hzx
  obtain ⟨w, hw, _, hval⟩ := (mem_collapseGraph_value hR hyD).mp hzx
  rw [← hval]
  exact mem_range_of_kpair_mem (kpair_value_mem (by simpa using hw))

def IsTransitiveCollapse (R D C f : V) : Prop :=
  IsTransitive C ∧ f ∈ C ^ D ∧ range f = C ∧
    (∀ x ∈ D, ∀ y ∈ D, f ‘ x = f ‘ y → x = y) ∧
    ∀ x ∈ D, ∀ y ∈ D, f ‘ x ∈ f ‘ y ↔ ⟨x, y⟩ₖ ∈ R

instance isTransitiveCollapse_definable : ℒₛₑₜ-relation₄[V] IsTransitiveCollapse := by
  unfold IsTransitiveCollapse
  definability

theorem collapseGraph_isTransitiveCollapse {R D : V} (hR : IsInternallyWellFounded R D)
    (hext : IsExtensionalOn R D) : IsTransitiveCollapse R D (range (collapseGraph hR)) (collapseGraph hR) := by
  refine ⟨collapseGraph_range_transitive hR, ?_, rfl, collapseGraph_injective hR hext, ?_⟩
  · simpa only [domain_collapseGraph] using IsFunction.mem_function (collapseGraph hR)
  · intro x hx y hy
    exact collapseGraph_membership_iff hR hext hx hy

theorem transitiveCollapse_recursion {R D C f : V} (hf : IsTransitiveCollapse R D C f) :
    IsRecursionAttempt R D (fun _ g ↦ range g) f ∧ domain f = D := by
  have : IsTransitive C := hf.1
  have : IsFunction f := IsFunction.of_mem hf.2.1
  have hd := domain_eq_of_mem_function hf.2.1
  refine ⟨⟨inferInstance, ⟨?_, ?_⟩, ?_⟩, hd⟩
  · intro y hy
    exact hd ▸ hy
  · intro x _ y hy
    rw [hd]
    exact (mem_predecessors_iff _ _ _ _).mp hy |>.1
  · intro x hx
    have hxD : x ∈ D := hd ▸ hx
    apply mem_ext
    intro z
    rw [mem_range_iff]
    constructor
    · intro hz
      have hxC := function_value_mem hf.2.1 hxD
      have hzC : z ∈ C := (inferInstance : IsTransitive C).mem_trans hz hxC
      have hzr : z ∈ range f := hf.2.2.1.symm ▸ hzC
      obtain ⟨y, hyz⟩ := mem_range_iff.mp hzr
      have hyD : y ∈ D := hd ▸ mem_domain_of_kpair_mem hyz
      have hyval := value_eq_of_kpair_mem hyz
      have hyx : ⟨y, x⟩ₖ ∈ R := (hf.2.2.2.2 y hyD x hxD).mp (hyval.symm ▸ hz)
      exact ⟨y, kpair_mem_restrict_iff.mpr ⟨hyz, (mem_predecessors_iff _ _ _ _).mpr ⟨hyD, hyx⟩⟩⟩
    · rintro ⟨y, hy⟩
      obtain ⟨hyz, hyp⟩ := kpair_mem_restrict_iff.mp hy
      obtain ⟨hyD, hyx⟩ := (mem_predecessors_iff _ _ _ _).mp hyp
      exact value_eq_of_kpair_mem hyz ▸ (hf.2.2.2.2 y hyD x hxD).mpr hyx

theorem transitiveCollapse_unique {R D C f : V} (hR : IsInternallyWellFounded R D)
    (hf : IsTransitiveCollapse R D C f) : f = collapseGraph hR ∧ C = range (collapseGraph hR) := by
  have heq : collapseGraph hR = f := (wellFoundedRecursion_eq_iff hR _ _ f).mpr (transitiveCollapse_recursion hf)
  exact ⟨heq.symm, hf.2.2.1.symm.trans (congrArg range heq.symm)⟩

theorem mostowskiCollapse_existsUnique {R D : V} (hR : IsInternallyWellFounded R D)
    (hext : IsExtensionalOn R D) : ∃! f, ∃ C, IsTransitiveCollapse R D C f := by
  refine ⟨collapseGraph hR, ⟨range (collapseGraph hR), collapseGraph_isTransitiveCollapse hR hext⟩, ?_⟩
  rintro f ⟨C, hf⟩
  exact (transitiveCollapse_unique hR hf).1

theorem collapseGraph_full_relation_iff {R D : V} (hR : IsInternallyWellFounded R D)
    (hext : IsExtensionalOn R D) (hrel : R ⊆ D ×ˢ D) (x y : V) :
    ⟨x, y⟩ₖ ∈ R ↔ x ∈ D ∧ y ∈ D ∧ (collapseGraph hR) ‘ x ∈ (collapseGraph hR) ‘ y := by
  constructor
  · intro hxy
    obtain ⟨hx, hy⟩ := kpair_mem_iff.mp (hrel _ hxy)
    exact ⟨hx, hy, (collapseGraph_membership_iff hR hext hx hy).mpr hxy⟩
  · rintro ⟨hx, hy, hxy⟩
    exact (collapseGraph_membership_iff hR hext hx hy).mp hxy

end ZFVP
