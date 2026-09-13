import ZFVP.SetTheory.FunctionValue

/-! Definability and evaluation of internal composition (first argument first). -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem value_compose_of_mem_function {A B C f g x : V} (hf : f ∈ B ^ A)
    (hg : g ∈ C ^ B) (hx : x ∈ A) :
    (compose f g) ‘ x = g ‘ (f ‘ x) := by
  have : IsFunction f := IsFunction.of_mem hf
  have : IsFunction g := IsFunction.of_mem hg
  have : IsFunction (compose f g) := IsFunction.of_mem (compose_function hf hg)
  apply value_eq_of_kpair_mem
  exact mem_compose_iff.mpr ⟨x, f ‘ x, g ‘ (f ‘ x),
    kpair_value_mem (by simpa [domain_eq_of_mem_function hf] using hx),
    kpair_value_mem (by simpa [domain_eq_of_mem_function hg] using function_value_mem hf hx), rfl⟩

instance compose_definable : ℒₛₑₜ-function₂[V] compose := by
  have h : ℒₛₑₜ-relation₃ (fun C R S : V ↦ ∀ p, p ∈ C ↔
      ∃ x y z, ⟨x, y⟩ₖ ∈ R ∧ ⟨y, z⟩ₖ ∈ S ∧ p = ⟨x, z⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = compose (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_compose_iff]

theorem restrict_mem_function_of_values {f A B : V} [IsFunction f]
    (hA : A ⊆ domain f) (hB : ∀ x ∈ A, f ‘ x ∈ B) : f ↾ A ∈ B ^ A := by
  apply mem_function.intro
  · intro p hp
    obtain ⟨hpf, x, hx, y, rfl⟩ := mem_restrict_iff.mp hp
    have heq := value_eq_of_kpair_mem hpf
    exact kpair_mem_iff.mpr ⟨hx, heq ▸ hB x hx⟩
  · intro x hx
    refine ⟨f ‘ x, kpair_mem_restrict_iff.mpr ⟨kpair_value_mem (hA x hx), hx⟩, ?_⟩
    intro y hy
    exact (value_eq_of_kpair_mem (kpair_mem_restrict_iff.mp hy).1).symm

theorem compose_restrict_range (f g : V) : compose f (g ↾ (range f)) = compose f g := by
  apply mem_ext
  intro p
  constructor
  · intro hp
    obtain ⟨x, y, z, hxy, hyz, rfl⟩ := mem_compose_iff.mp hp
    exact mem_compose_iff.mpr ⟨x, y, z, hxy, (kpair_mem_restrict_iff.mp hyz).1, rfl⟩
  · intro hp
    obtain ⟨x, y, z, hxy, hyz, rfl⟩ := mem_compose_iff.mp hp
    exact mem_compose_iff.mpr ⟨x, y, z, hxy,
      kpair_mem_restrict_iff.mpr ⟨hyz, mem_range_of_kpair_mem hxy⟩, rfl⟩

theorem compose_mem_function_of_values {f g X Y Z : V} (hf : f ∈ Y ^ X)
    [IsFunction g] (hdom : range f ⊆ domain g)
    (hval : ∀ y ∈ range f, g ‘ y ∈ Z) : compose f g ∈ Z ^ X := by
  have : IsFunction f := IsFunction.of_mem hf
  have hf' : f ∈ range f ^ X := by
    rw [← domain_eq_of_mem_function hf]
    exact IsFunction.mem_function f
  rw [← compose_restrict_range f g]
  exact compose_function hf' (restrict_mem_function_of_values hdom hval)

end ZFVP
