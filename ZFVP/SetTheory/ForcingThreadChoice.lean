import ZFVP.SetTheory.ForcingInverseLimit
import ZFVP.SetTheory.OrdinalDependentChoice

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingInverseLimit_of_local_steps {θ P π U f : V} [IsOrdinal θ]
    (hf : f ∈ U ^ θ)
    (hstep : ∀ j ∈ θ, f ↾ j ∈ forcingInverseLimit j P π U →
      f ‘ j ∈ P ‘ j ∧ ∀ i ∈ j, (π ‘ ⟨i, j⟩ₖ) ‘ (f ‘ j) = (f ↾ j) ‘ i) :
    f ∈ forcingInverseLimit θ P π U := by
  let := IsFunction.of_mem hf
  have hpoint : ∀ j, j ∈ θ → f ‘ j ∈ P ‘ j ∧
      ∀ i ∈ j, (π ‘ ⟨i, j⟩ₖ) ‘ (f ‘ j) = f ‘ i := by
    apply set_induction (fun j ↦ j ∈ θ → f ‘ j ∈ P ‘ j ∧
      ∀ i ∈ j, (π ‘ ⟨i, j⟩ₖ) ‘ (f ‘ j) = f ‘ i) (by definability)
    intro j ih hj
    let := IsOrdinal.of_mem hj
    have hjθ : j ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hj
    have hrest := function_restrict_mem hf hjθ
    have hv : ∀ i ∈ j, (f ↾ j) ‘ i = f ‘ i := fun i hi ↦
      value_restrict ((domain_eq_of_mem_function hf).symm ▸ hjθ i hi) hi
    have hgood : f ↾ j ∈ forcingInverseLimit j P π U := by
      apply (mem_forcingInverseLimit_iff _ _ _ _ _).mpr
      refine ⟨hrest, ?_, ?_⟩
      · intro i hi
        rw [hv i hi]
        exact (ih i hi (hjθ i hi)).1
      · intro k hk i hik hi
        rw [hv k hk, hv i hi]
        exact (ih k hk (hjθ k hk)).2 i hik
    obtain ⟨hval, hcoh⟩ := hstep j hj hgood
    exact ⟨hval, fun i hi ↦ (hcoh i hi).trans (hv i hi)⟩
  apply (mem_forcingInverseLimit_iff _ _ _ _ _).mpr
  refine ⟨hf, ?_, ?_⟩
  · exact fun i hi ↦ (hpoint i hi).1
  · exact fun j hj i hij _hi ↦ (hpoint j hj).2 i hij


/-- Dependent choice assembles a thread when every shorter coherent thread can be extended. -/
theorem forcingInverseLimit_nonempty_of_dependentChoice {θ P π U : V} [IsOrdinal θ]
    (hDC : InternalDependentChoiceAt θ) (hU : IsNonempty U)
    (hnext : ∀ β ∈ θ, ∀ s ∈ forcingInverseLimit β P π U,
      ∃ x ∈ U, x ∈ P ‘ β ∧ ∀ i ∈ β, (π ‘ ⟨i, β⟩ₖ) ‘ x = s ‘ i) :
    IsNonempty (forcingInverseLimit θ P π U) := by
  classical
  have hlim : ℒₛₑₜ-function₁[V] (fun z ↦ forcingInverseLimit (domain (kpair.π₁ z)) P π U) := by
    apply Language.DefinableFunction₄.comp <;> definability
  let S : V := {z ∈ shorterSequences θ U ×ˢ U ;
    kpair.π₁ z ∈ forcingInverseLimit (domain (kpair.π₁ z)) P π U →
      kpair.π₂ z ∈ P ‘ (domain (kpair.π₁ z)) ∧
        ∀ i ∈ domain (kpair.π₁ z),
          (π ‘ ⟨i, domain (kpair.π₁ z)⟩ₖ) ‘ (kpair.π₂ z) = (kpair.π₁ z) ‘ i}
  have hS (s x : V) : ⟨s, x⟩ₖ ∈ S ↔ s ∈ shorterSequences θ U ∧ x ∈ U ∧
      (s ∈ forcingInverseLimit (domain s) P π U →
        x ∈ P ‘ (domain s) ∧ ∀ i ∈ domain s, (π ‘ ⟨i, domain s⟩ₖ) ‘ x = s ‘ i) := by
    simp only [S, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
    tauto
  have hserial : ∀ s ∈ shorterSequences θ U, ∃ x ∈ U, ⟨s, x⟩ₖ ∈ S := by
    intro s hs
    by_cases hgood : s ∈ forcingInverseLimit (domain s) P π U
    · obtain ⟨x, hx, hval, hcoh⟩ := hnext (domain s)
        ((mem_shorterSequences_domain _ _ _).mp hs).1 s hgood
      exact ⟨x, hx, (hS s x).mpr ⟨hs, hx, fun _ ↦ ⟨hval, hcoh⟩⟩⟩
    · obtain ⟨x, hx⟩ := hU
      exact ⟨x, hx, (hS s x).mpr ⟨hs, hx, fun h ↦ False.elim (hgood h)⟩⟩
  obtain ⟨f, hf, hstep⟩ := hDC U S hU hserial
  refine ⟨f, forcingInverseLimit_of_local_steps hf ?_⟩
  intro j hj hgood
  have hrest := function_restrict_mem hf (IsOrdinal.toIsTransitive.transitive _ hj)
  have hs := ((hS _ _).mp (hstep j hj)).2.2
  rw [domain_eq_of_mem_function hrest] at hs
  exact hs hgood

end ZFVP
