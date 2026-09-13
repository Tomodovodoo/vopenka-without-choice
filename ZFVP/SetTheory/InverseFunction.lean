import ZFVP.SetTheory.FunctionValue

/-! Inverting an internal injection on its range requires no choice principle. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def converseGraph (f : V) : V :=
  {p ∈ range f ×ˢ domain f ; ⟨kpair.π₂ p, kpair.π₁ p⟩ₖ ∈ f}

@[simp] theorem pair_mem_converseGraph (f x y : V) :
    ⟨x, y⟩ₖ ∈ converseGraph f ↔ ⟨y, x⟩ₖ ∈ f := by
  simp only [converseGraph, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨⟨mem_range_of_kpair_mem h, mem_domain_of_kpair_mem h⟩, h⟩⟩

instance converseGraph_definable : ℒₛₑₜ-function₁[V] converseGraph := by
  have h : ℒₛₑₜ-relation (fun g f : V ↦ ∀ p, p ∈ g ↔
      p ∈ range f ×ˢ domain f ∧ ⟨kpair.π₂ p, kpair.π₁ p⟩ₖ ∈ f) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = converseGraph (v 1) ↔ _
  rw [mem_ext_iff]
  simp [converseGraph]

theorem converseGraph_mem_function {A B f : V} (hf : f ∈ B ^ A) (hinj : Injective f) :
    converseGraph f ∈ A ^ range f := by
  apply mem_function.intro
  · intro p hp
    have hp' := (mem_sep_iff.mp hp).1
    simpa only [domain_eq_of_mem_function hf] using hp'
  · intro y hy
    obtain ⟨x, hxy⟩ := mem_range_iff.mp hy
    refine ⟨x, (pair_mem_converseGraph _ _ _).mpr hxy, ?_⟩
    intro z hzy
    exact hinj z x y ((pair_mem_converseGraph _ _ _).mp hzy) hxy

theorem converseGraph_injective (f : V) [IsFunction f] : Injective (converseGraph f) := by
  intro x y z hx hy
  exact IsFunction.unique ((pair_mem_converseGraph _ _ _).mp hx) ((pair_mem_converseGraph _ _ _).mp hy)

theorem range_converseGraph (f : V) : range (converseGraph f) = domain f := by
  apply mem_ext
  intro x
  simp only [mem_range_iff, pair_mem_converseGraph, mem_domain_iff]

theorem injective_value_eq {A B f x y : V} (hf : f ∈ B ^ A) (hinj : Injective f)
    (hx : x ∈ A) (hy : y ∈ A) (heq : f ‘ x = f ‘ y) : x = y := by
  have : IsFunction f := IsFunction.of_mem hf
  exact hinj x y (f ‘ x) (kpair_value_mem (by simpa only [domain_eq_of_mem_function hf] using hx))
    (heq.symm ▸ kpair_value_mem (by simpa only [domain_eq_of_mem_function hf] using hy))

theorem converseGraph_value_value {A B f x : V} (hf : f ∈ B ^ A) (hinj : Injective f) (hx : x ∈ A) :
    (converseGraph f) ‘ (f ‘ x) = x := by
  have : IsFunction f := IsFunction.of_mem hf
  have : IsFunction (converseGraph f) := IsFunction.of_mem (converseGraph_mem_function hf hinj)
  exact value_eq_of_kpair_mem ((pair_mem_converseGraph _ _ _).mpr
    (kpair_value_mem (by simpa only [domain_eq_of_mem_function hf] using hx)))

theorem value_converseGraph_value {A B f y : V} (hf : f ∈ B ^ A) (hinj : Injective f)
    (hy : y ∈ range f) : f ‘ ((converseGraph f) ‘ y) = y := by
  have : IsFunction f := IsFunction.of_mem hf
  have hconv := converseGraph_mem_function hf hinj
  have : IsFunction (converseGraph f) := IsFunction.of_mem hconv
  exact value_eq_of_kpair_mem ((pair_mem_converseGraph _ _ _).mp
    (kpair_value_mem (by simpa only [domain_eq_of_mem_function hconv] using hy)))

end ZFVP
