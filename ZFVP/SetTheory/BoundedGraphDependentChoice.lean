import ZFVP.SetTheory.BoundedElementaryGraph
import ZFVP.SetTheory.WellOrderedDependentChoice

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedNextExistsFormula : SetTheorySemisentence 3 :=
  “X R s. ∃ x ∈ X, !boundedPairMemberFormula R s x”

theorem boundedNextExistsFormula_bounded : IsBoundedSetFormula boundedNextExistsFormula :=
  .exs (.bvar 0) (boundedPairMemberFormula_bounded.subst _)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance boundedNextExistsFormula_defined :
    Defined (fun v : Fin 3 → V ↦ ∃ x ∈ v 0, ⟨v 2, x⟩ₖ ∈ v 1) boundedNextExistsFormula :=
  ⟨fun v ↦ by simp [boundedNextExistsFormula]⟩

theorem IsBoundedElementaryGraph.dependentChoicePath {j X R γ : V} [IsOrdinal γ]
    (hj : IsBoundedElementaryGraph j) (hX : X ∈ domain j) (hR : R ∈ domain j)
    (hγ : γ ∈ domain j) (hfix : ∀ α ∈ γ, j ‘ α = α)
    (hclosed : ∀ α ∈ γ, ∀ s ∈ X ^ α, s ∈ domain j)
    (hw : IsWellOrderable X)
    (hserial : ∀ s ∈ shorterSequences γ (j ‘ X), ∃ x ∈ j ‘ X, ⟨s, x⟩ₖ ∈ j ‘ R) :
    ∃ f, IsDependentChoicePath (j ‘ X) (j ‘ R) γ f := by
  have hsource : ∀ s ∈ shorterSequences γ X, ∃ x ∈ X, ⟨s, x⟩ₖ ∈ R := by
    intro s hs
    obtain ⟨α, hα, hsf⟩ := (mem_shorterSequences _ _ _).mp hs
    have hsd := hclosed α hα s hsf
    have hαd := hj.transitive.mem_trans hα hγ
    have hjsf := (hj.function_iff hsd hX hαd).mp hsf
    rw [hfix α hα] at hjsf
    have hnext := hserial (j ‘ s) ((mem_shorterSequences _ _ _).mpr ⟨α, hα, hjsf⟩)
    exact (hj.defined_iff boundedNextExistsFormula_bounded
      (fun v ↦ ∃ x ∈ v 0, ⟨v 2, x⟩ₖ ∈ v 1) ![X, R, s]
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hX, hR, hsd])).mpr hnext
  obtain ⟨f, hf, hstep⟩ := dependentChoicePath_of_wellOrderable hw hsource
  let := IsFunction.of_mem hf
  let F := functionMap (fun x ↦ j ‘ x) (by definability) f
  have hF : F ∈ (j ‘ X) ^ γ := functionMap_mem_function _ _ hf
    (fun x hx ↦ (hj.mem_iff (hj.transitive.mem_trans hx hX) hX).mp hx)
  refine ⟨F, hF, ?_⟩
  intro i hi
  let := IsOrdinal.of_mem hi
  have hisub : i ⊆ γ := IsOrdinal.toIsTransitive.transitive _ hi
  have hprefix := function_restrict_mem hf hisub
  have hpd := hclosed i hi (f ↾ i) hprefix
  have hval := function_value_mem hf hi
  have himage := (hj.pair_mem_iff hR hpd (hj.transitive.mem_trans hval hX)).mp (hstep i hi)
  have he : j ‘ (f ↾ i) = F ↾ i := by
    rw [← hj.functionMap_eq_value hpd hX (hj.transitive.mem_trans hi hγ) hprefix
      (hfix i hi) (fun a ha ↦ hfix a (hisub a ha))]
    exact functionMap_restrict _ _ (by rw [domain_eq_of_mem_function hf]; exact hisub)
  have hv : F ‘ i = j ‘ (f ‘ i) := functionMap_value _ _ ((domain_eq_of_mem_function hf).symm ▸ hi)
  simpa only [he, ← hv] using himage

end ZFVP
