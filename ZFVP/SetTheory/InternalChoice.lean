import ZFVP.SetTheory.FunctionComposition

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def InternalChoice (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : Prop :=
  ∀ A : V, (∀ X ∈ A, IsNonempty X) → ∃ f ∈ (⋃ˢ A) ^ A, ∀ X ∈ A, f ‘ X ∈ X

omit [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem disjoint_choice_of_models_ac [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] :
    ∀ A : V, (∀ X ∈ A, IsNonempty X) →
      (∀ X ∈ A, ∀ Y ∈ A, (∃ z ∈ X, z ∈ Y) → X = Y) →
      ∃ C : V, ∀ X ∈ A, ∃! x, x ∈ C ∧ x ∈ X := by
  simpa [models_iff, Axiom.choice] using
    (Theory.models V 𝗔𝗖 (show Axiom.choice ∈ 𝗔𝗖 from by simp [AxiomOfChoice]))

theorem internalChoice_of_models_ac [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] : InternalChoice V := by
  intro A hA
  let D := repl (fun X : V ↦ ({X} : V) ×ˢ X) (by definability) A
  have hD (B : V) : B ∈ D ↔ ∃ X ∈ A, B = ({X} : V) ×ˢ X := repl_spec (by definability)
  have hnD : ∀ B ∈ D, IsNonempty B := by
    intro B hB
    obtain ⟨X, hX, rfl⟩ := (hD B).mp hB
    obtain ⟨x, hx⟩ := (hA X hX).nonempty
    exact ⟨⟨X, x⟩ₖ, kpair_mem_iff.mpr ⟨by simp, hx⟩⟩
  have hdisj : ∀ B ∈ D, ∀ E ∈ D, (∃ z ∈ B, z ∈ E) → B = E := by
    intro B hB E hE hz
    obtain ⟨X, _, rfl⟩ := (hD B).mp hB
    obtain ⟨Y, _, rfl⟩ := (hD E).mp hE
    obtain ⟨z, hzX, hzY⟩ := hz
    obtain ⟨a, ha, b, _, rfl⟩ := mem_prod_iff.mp hzX
    have haX : a = X := mem_singleton_iff.mp ha
    have haY : a = Y := mem_singleton_iff.mp (kpair_mem_iff.mp hzY).1
    rw [← haX, ← haY]
  obtain ⟨C, hC⟩ := disjoint_choice_of_models_ac D hnD hdisj
  let f : V := {p ∈ A ×ˢ (⋃ˢ A) ; p ∈ C ∧ kpair.π₂ p ∈ kpair.π₁ p}
  have hp (X x : V) : ⟨X, x⟩ₖ ∈ f ↔ X ∈ A ∧ x ∈ X ∧ ⟨X, x⟩ₖ ∈ C := by
    simp only [f, mem_sep_iff, kpair_mem_iff, kpair.π₂_kpair, kpair.π₁_kpair]
    constructor
    · rintro ⟨⟨hX, _⟩, hXC, hx⟩
      exact ⟨hX, hx, hXC⟩
    · rintro ⟨hX, hx, hXC⟩
      exact ⟨⟨hX, mem_sUnion_iff.mpr ⟨X, hX, hx⟩⟩, hXC, hx⟩
  have hunique (X : V) (hX : X ∈ A) : ∃! x, ⟨X, x⟩ₖ ∈ f := by
    obtain ⟨z, hz, huniq⟩ := hC (({X} : V) ×ˢ X) ((hD _).mpr ⟨X, hX, rfl⟩)
    obtain ⟨a, ha, x, hx, heq⟩ := mem_prod_iff.mp hz.2
    have haX := mem_singleton_iff.mp ha
    subst a
    subst z
    refine ⟨x, (hp X x).mpr ⟨hX, hx, hz.1⟩, ?_⟩
    intro y hy
    have hy' := (hp X y).mp hy
    have hpair := huniq ⟨X, y⟩ₖ ⟨hy'.2.2, kpair_mem_iff.mpr ⟨by simp, hy'.2.1⟩⟩
    exact (kpair_iff.mp hpair).2
  have hf : f ∈ (⋃ˢ A) ^ A := mem_function.intro
    (fun _ h ↦ (mem_sep_iff.mp h).1) hunique
  have : IsFunction f := IsFunction.of_mem hf
  refine ⟨f, hf, ?_⟩
  intro X hX
  have hv := kpair_value_mem (f := f) (by simpa only [domain_eq_of_mem_function hf] using hX)
  exact ((hp X (f ‘ X)).mp hv).2.1

theorem disjoint_choice_of_internalChoice (hAC : InternalChoice V) :
    ∀ A : V, (∀ X ∈ A, IsNonempty X) →
      (∀ X ∈ A, ∀ Y ∈ A, (∃ z ∈ X, z ∈ Y) → X = Y) →
      ∃ C : V, ∀ X ∈ A, ∃! x, x ∈ C ∧ x ∈ X := by
  intro A hA hdisj
  obtain ⟨f, hf, hval⟩ := hAC A hA
  have : IsFunction f := IsFunction.of_mem hf
  refine ⟨range f, ?_⟩
  intro X hX
  have hgraph : ⟨X, f ‘ X⟩ₖ ∈ f := kpair_value_mem (by simpa only [domain_eq_of_mem_function hf] using hX)
  refine ⟨f ‘ X, ⟨mem_range_of_kpair_mem hgraph, hval X hX⟩, ?_⟩
  rintro x ⟨hxf, hxX⟩
  obtain ⟨Y, hYx⟩ := mem_range_iff.mp hxf
  have hY : Y ∈ A := domain_eq_of_mem_function hf ▸ mem_domain_of_kpair_mem hYx
  have hxY : x ∈ Y := value_eq_of_kpair_mem hYx ▸ hval Y hY
  have heq := hdisj X hX Y hY ⟨x, hxX, hxY⟩
  subst Y
  exact (value_eq_of_kpair_mem hYx).symm

theorem models_ac_of_internalChoice (hAC : InternalChoice V) : V↓[ℒₛₑₜ] ⊧* 𝗔𝗖 := by
  refine ⟨?_⟩
  intro φ hφ
  have heq : φ = Axiom.choice := Set.mem_singleton_iff.mp hφ
  subst φ
  simpa [models_iff, Axiom.choice] using disjoint_choice_of_internalChoice hAC

theorem internalChoice_iff_models_ac : InternalChoice V ↔ V↓[ℒₛₑₜ] ⊧* 𝗔𝗖 := by
  constructor
  · exact models_ac_of_internalChoice
  · intro h
    have : V↓[ℒₛₑₜ] ⊧* 𝗔𝗖 := h
    exact internalChoice_of_models_ac

theorem choice_for_definable_family (hAC : InternalChoice V) (I : V) (F : V → V)
    (hF : ℒₛₑₜ-function₁ F) (hn : ∀ i ∈ I, IsNonempty (F i)) :
    ∃ g, IsFunction g ∧ domain g = I ∧ ∀ i ∈ I, g ‘ i ∈ F i := by
  let A := repl F hF I
  have hA : ∀ X ∈ A, IsNonempty X := by
    intro X hX
    obtain ⟨i, hi, rfl⟩ := (repl_spec hF).mp hX
    exact hn i hi
  obtain ⟨c, hc, hval⟩ := hAC A hA
  let g := definableGraph I (fun i ↦ c ‘ (F i)) (by definability)
  refine ⟨g, definableGraph_isFunction _ _ _, domain_definableGraph _ _ _, ?_⟩
  intro i hi
  rw [show g ‘ i = c ‘ (F i) from value_definableGraph _ _ _ hi]
  exact hval (F i) ((repl_spec hF).mpr ⟨i, hi, rfl⟩)

end ZFVP
