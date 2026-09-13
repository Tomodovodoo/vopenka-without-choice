import ZFVP.SetTheory.WoodinSeedSupport
import ZFVP.SetTheory.ForcingIsomorphism

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance woodinInsertSeed_definable : ℒₛₑₜ-function₃[V] woodinInsertSeed := by
  have hd : ℒₛₑₜ-relation₄ (fun g θ f a : V ↦ ∀ p, p ∈ g ↔
    ∃ β ∈ woodinSourceIndex θ, p = ⟨β, woodinInsertSeedValue f a β⟩ₖ) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = woodinInsertSeed (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [woodinInsertSeed, mem_definableGraph_iff]

theorem forcingIsomorphism_of_inverse {P R Q S : V} (F G : V → V)
    (hF : ℒₛₑₜ-function₁ F) (hFP : ∀ p ∈ P, F p ∈ Q) (hGQ : ∀ q ∈ Q, G q ∈ P)
    (hGF : ∀ p ∈ P, G (F p) = p) (hFG : ∀ q ∈ Q, F (G q) = q)
    (horder : ∀ p ∈ P, ∀ q ∈ P, ⟨p, q⟩ₖ ∈ R ↔ ⟨F p, F q⟩ₖ ∈ S) :
    IsForcingIsomorphism P R Q S (definableGraph P F hF) := by
  have hf := definableGraph_mem_function_of_mapsTo _ _ _ hF hFP
  refine ⟨hf, ?_, ?_, ?_⟩
  · intro p q z hp hq
    obtain ⟨hpP, hzp⟩ := (pair_mem_definableGraph_iff _ F hF p z).mp hp
    obtain ⟨hqP, hzq⟩ := (pair_mem_definableGraph_iff _ F hF q z).mp hq
    have he := congrArg G (hzp.symm.trans hzq)
    simpa only [hGF p hpP, hGF q hqP] using he
  · apply SetTheory.subset_antisymm (range_subset_of_mem_function hf)
    intro q hq
    have hv := (value_definableGraph P F hF (hGQ q hq)).trans (hFG q hq)
    exact hv ▸ value_mem_range hf (hGQ q hq)
  · intro p hp q hq
    rw [value_definableGraph _ _ _ hp, value_definableGraph _ _ _ hq]
    exact horder p hp q hq

theorem woodinSeed_coordinateOrder_iff {θ R f g : V} [IsOrdinal θ] :
    (∀ i ∈ woodinSourceIndex θ,
      ⟨(woodinInsertSeed θ f ∅) ‘ i, (woodinInsertSeed θ g ∅) ‘ i⟩ₖ ∈
        (woodinInsertSeed θ R (({∅} : V) ×ˢ {∅})) ‘ i) ↔
    ∀ i ∈ θ, ⟨f ‘ i, g ‘ i⟩ₖ ∈ R ‘ i := by
  constructor
  · intro h i hi
    let := IsOrdinal.of_mem hi
    have hh := h (woodinSourceIndex i) (woodinSourceIndex_mem_iff.mpr hi)
    simpa only [woodinInsertSeed_at_sourceIndex hi] using hh
  · intro h i hi
    by_cases hz : i = ∅
    · subst i
      rw [woodinInsertSeed_zero, woodinInsertSeed_zero, woodinInsertSeed_zero]
      simp
    · let := IsOrdinal.of_mem hi
      rw [woodinInsertSeed_nonzero hi hz, woodinInsertSeed_nonzero hi hz,
        woodinInsertSeed_nonzero hi hz]
      exact h _ ((woodinRecursiveIndex_mem_iff hz).mpr hi)

noncomputable def woodinSeedThreadMap (θ K : V) : V :=
  definableGraph K (fun f ↦ woodinInsertSeed θ f ∅) (by definability)

theorem woodinSeed_inverseLimit_isomorphism {θ P R π U : V} [IsOrdinal θ]
    (hU : (∅ : V) ∈ U) :
    IsForcingIsomorphism (forcingInverseLimit θ P π U)
      (forcingThreadOrder θ R (forcingInverseLimit θ P π U))
      (forcingInverseLimit (woodinSourceIndex θ) (woodinInsertSeed θ P {∅})
        (woodinSeedProjections θ P π) U)
      (forcingThreadOrder (woodinSourceIndex θ) (woodinInsertSeed θ R (({∅} : V) ×ˢ {∅}))
        (forcingInverseLimit (woodinSourceIndex θ) (woodinInsertSeed θ P {∅})
          (woodinSeedProjections θ P π) U))
      (woodinSeedThreadMap θ (forcingInverseLimit θ P π U)) := by
  apply forcingIsomorphism_of_inverse (fun f ↦ woodinInsertSeed θ f ∅) (woodinRemoveSeed θ)
  · exact fun _ hf ↦ woodinInsertSeed_mem_inverseLimit hf hU
  · exact fun _ hg ↦ woodinRemoveSeed_mem_inverseLimit hg
  · intro f hf
    have hfun := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).1
    let := IsFunction.of_mem hfun
    exact woodinRemoveSeed_insert (domain_eq_of_mem_function hfun)
  · intro g hg
    have hfun := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hg).1
    let := IsFunction.of_mem hfun
    exact woodinInsertSeed_remove (domain_eq_of_mem_function hfun) (woodinSeed_inverseLimit_zero hg)
  · intro f hf g hg
    rw [mem_forcingThreadOrder_iff, mem_forcingThreadOrder_iff]
    simp only [hf, hg, woodinInsertSeed_mem_inverseLimit hf hU,
      woodinInsertSeed_mem_inverseLimit hg hU, true_and]
    exact woodinSeed_coordinateOrder_iff.symm

theorem woodinSeed_directLimit_isomorphism {θ P R π E t U : V} [IsOrdinal θ]
    (hU : (∅ : V) ∈ U) (hzero : (∅ : V) ∈ θ)
    (ht : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → (E ‘ ⟨i, j⟩ₖ) ‘ (t ‘ i) = t ‘ j) :
    IsForcingIsomorphism (forcingDirectLimit θ P π E U)
      (forcingThreadOrder θ R (forcingDirectLimit θ P π E U))
      (forcingDirectLimit (woodinSourceIndex θ) (woodinInsertSeed θ P {∅})
        (woodinSeedProjections θ P π) (woodinSeedSections θ E t) U)
      (forcingThreadOrder (woodinSourceIndex θ) (woodinInsertSeed θ R (({∅} : V) ×ˢ {∅}))
        (forcingDirectLimit (woodinSourceIndex θ) (woodinInsertSeed θ P {∅})
          (woodinSeedProjections θ P π) (woodinSeedSections θ E t) U))
      (woodinSeedThreadMap θ (forcingDirectLimit θ P π E U)) := by
  apply forcingIsomorphism_of_inverse (fun f ↦ woodinInsertSeed θ f ∅) (woodinRemoveSeed θ)
  · exact fun _ hf ↦ woodinInsertSeed_mem_directLimit hf hU
  · exact fun _ hg ↦ woodinRemoveSeed_mem_directLimit hzero ht hg
  · intro f hf
    have hi := (mem_forcingDirectLimit_iff _ _ _ _ _ _).mp hf |>.1
    have hfun := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hi).1
    let := IsFunction.of_mem hfun
    exact woodinRemoveSeed_insert (domain_eq_of_mem_function hfun)
  · intro g hg
    have hi := (mem_forcingDirectLimit_iff _ _ _ _ _ _).mp hg |>.1
    have hfun := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hi).1
    let := IsFunction.of_mem hfun
    exact woodinInsertSeed_remove (domain_eq_of_mem_function hfun) (woodinSeed_inverseLimit_zero hi)
  · intro f hf g hg
    rw [mem_forcingThreadOrder_iff, mem_forcingThreadOrder_iff]
    simp only [hf, hg, woodinInsertSeed_mem_directLimit hf hU,
      woodinInsertSeed_mem_directLimit hg hU, true_and]
    exact woodinSeed_coordinateOrder_iff.symm

end ZFVP
