import ZFVP.SetTheory.InternalWellFounded
import ZFVP.SetTheory.FunctionUnion

/-! Compatible partial solutions for internal well-founded recursion. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def predecessors (R D x : V) : V := {y ∈ D ; ⟨y, x⟩ₖ ∈ R}

@[simp] theorem mem_predecessors_iff (R D x y : V) :
    y ∈ predecessors R D x ↔ y ∈ D ∧ ⟨y, x⟩ₖ ∈ R := by simp [predecessors]

instance predecessors_definable : ℒₛₑₜ-function₃[V] predecessors := by
  have h : ℒₛₑₜ-relation₄ (fun P R D x : V ↦ ∀ y, y ∈ P ↔ y ∈ D ∧ ⟨y, x⟩ₖ ∈ R) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = predecessors (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp

def IsDownwardClosed (R D A : V) : Prop :=
  A ⊆ D ∧ ∀ x ∈ A, predecessors R D x ⊆ A

instance isDownwardClosed_definable : ℒₛₑₜ-relation₃[V] IsDownwardClosed := by
  unfold IsDownwardClosed
  definability

def IsRecursionAttempt (R D : V) (F : V → V → V) (f : V) : Prop :=
  IsFunction f ∧ IsDownwardClosed R D (domain f) ∧
    ∀ x ∈ domain f, f ‘ x = F x (f ↾ (predecessors R D x))

theorem isRecursionAttempt_definable (R D : V) (F : V → V → V) (hF : ℒₛₑₜ-function₂ F) :
    ℒₛₑₜ-predicate (IsRecursionAttempt R D F) := by
  unfold IsRecursionAttempt
  definability

theorem recursionAttempt_values_coherent {R D : V} (hR : IsInternallyWellFounded R D)
    {F : V → V → V} {f g : V} (hf : IsRecursionAttempt R D F f)
    (hg : IsRecursionAttempt R D F g) :
    ∀ x ∈ domain f, x ∈ domain g → f ‘ x = g ‘ x := by
  have : IsFunction f := hf.1
  have : IsFunction g := hg.1
  have h : ∀ x ∈ D, x ∈ domain f → x ∈ domain g → f ‘ x = g ‘ x := by
    apply internalWellFounded_induction hR
      (fun x ↦ x ∈ domain f → x ∈ domain g → f ‘ x = g ‘ x) (by definability)
    intro x _ ih hxf hxg
    have hpf := hf.2.1.2 x hxf
    have hpg := hg.2.1.2 x hxg
    have heq : f ↾ (predecessors R D x) = g ↾ (predecessors R D x) := by
      apply restrict_eq_of_values hpf hpg
      intro y hy
      obtain ⟨hyD, hyx⟩ := (mem_predecessors_iff R D x y).mp hy
      exact ih y hyD hyx (hpf y hy) (hpg y hy)
    rw [hf.2.2 x hxf, hg.2.2 x hxg, heq]
  intro x hx hxg
  exact h x (hf.2.1.1 x hx) hx hxg

theorem recursionAttempt_compatible {R D : V} (hR : IsInternallyWellFounded R D)
    {F : V → V → V} {f g x y z : V} (hf : IsRecursionAttempt R D F f)
    (hg : IsRecursionAttempt R D F g) (hxy : ⟨x, y⟩ₖ ∈ f) (hxz : ⟨x, z⟩ₖ ∈ g) : y = z := by
  have : IsFunction f := hf.1
  have : IsFunction g := hg.1
  exact (value_eq_of_kpair_mem hxy).symm.trans
    ((recursionAttempt_values_coherent hR hf hg x (mem_domain_of_kpair_mem hxy)
      (mem_domain_of_kpair_mem hxz)).trans (value_eq_of_kpair_mem hxz))

theorem recursionAttempt_family_compatible {R D B : V} (hR : IsInternallyWellFounded R D)
    {F : V → V → V} (hB : ∀ f ∈ B, IsRecursionAttempt R D F f) : CompatibleFunctionFamily B :=
  fun f hf g hg _ _ _ hxy hxz ↦ recursionAttempt_compatible hR (hB f hf) (hB g hg) hxy hxz

theorem recursionAttempt_sUnion {R D B : V} (hR : IsInternallyWellFounded R D)
    {F : V → V → V} (hB : ∀ f ∈ B, IsRecursionAttempt R D F f) :
    IsRecursionAttempt R D F (⋃ˢ B) := by
  have hF : ∀ f ∈ B, IsFunction f := fun f hf ↦ (hB f hf).1
  have hC := recursionAttempt_family_compatible hR hB
  have hU : IsFunction (⋃ˢ B) := isFunction_sUnion hF hC
  refine ⟨hU, ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨f, hf, hxf⟩ := (mem_domain_sUnion_iff B x).mp hx
    exact (hB f hf).2.1.1 x hxf
  · intro x hx y hy
    obtain ⟨f, hf, hxf⟩ := (mem_domain_sUnion_iff B x).mp hx
    exact (mem_domain_sUnion_iff B y).mpr ⟨f, hf, (hB f hf).2.1.2 x hxf y hy⟩
  · intro x hx
    obtain ⟨f, hf, hxf⟩ := (mem_domain_sUnion_iff B x).mp hx
    have : IsFunction f := hF f hf
    have hpf := (hB f hf).2.1.2 x hxf
    have hpu : predecessors R D x ⊆ domain (⋃ˢ B) := fun y hy ↦
      (mem_domain_sUnion_iff B y).mpr ⟨f, hf, hpf y hy⟩
    have heq := restrict_eq_of_values hpf hpu (fun y hy ↦
      (value_sUnion_of_mem hF hC hf (hpf y hy)).symm)
    rw [value_sUnion_of_mem hF hC hf hxf, (hB f hf).2.2 x hxf, heq]

end ZFVP

