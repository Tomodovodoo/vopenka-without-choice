import ZFVP.SetTheory.ForcingDirectLimit

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Apply a specified internal family of maps to all coordinates of a thread. -/
noncomputable def forcingThreadAction (θ m f : V) : V :=
  definableGraph θ (fun i ↦ (m ‘ i) ‘ (f ‘ i)) (by definability)

instance forcingThreadAction_definable : ℒₛₑₜ-function₃[V] forcingThreadAction := by
  have h : ℒₛₑₜ-relation₄[V] (fun g θ m f ↦
      ∀ z, z ∈ g ↔ ∃ i ∈ θ, z = ⟨i, (m ‘ i) ‘ (f ‘ i)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingThreadAction (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [forcingThreadAction, mem_definableGraph_iff]

theorem forcingThreadAction_value {θ m f i : V} (hi : i ∈ θ) :
    (forcingThreadAction θ m f) ‘ i = (m ‘ i) ‘ (f ‘ i) :=
  value_definableGraph _ _ _ hi

theorem forcingThreadAction_mem_inverse {θ P Q π ρ U W m f : V}
    (hm : ∀ i ∈ θ, m ‘ i ∈ (Q ‘ i) ^ (P ‘ i))
    (hQ : ∀ i ∈ θ, Q ‘ i ⊆ W)
    (hc : ∀ j ∈ θ, ∀ i ∈ j, i ∈ θ → ∀ p ∈ P ‘ j,
      (ρ ‘ ⟨i, j⟩ₖ) ‘ ((m ‘ j) ‘ p) = (m ‘ i) ‘ ((π ‘ ⟨i, j⟩ₖ) ‘ p))
    (hf : f ∈ forcingInverseLimit θ P π U) :
    forcingThreadAction θ m f ∈ forcingInverseLimit θ Q ρ W := by
  obtain ⟨_, hv, hfcoh⟩ := (mem_forcingInverseLimit_iff _ _ _ _ _).mp hf
  apply (mem_forcingInverseLimit_iff _ _ _ _ _).mpr
  refine ⟨definableGraph_mem_function_of_mapsTo _ _ _ _ (fun i hi ↦
    hQ i hi _ (function_value_mem (hm i hi) (hv i hi))), ?_, ?_⟩
  · intro i hi
    rw [forcingThreadAction_value hi]
    exact function_value_mem (hm i hi) (hv i hi)
  · intro j hj i hij hi
    rw [forcingThreadAction_value hj, forcingThreadAction_value hi,
      hc j hj i hij hi _ (hv j hj), hfcoh j hj i hij hi]

theorem forcingThreadAction_restrict {θ η U m f : V}
    (hη : η ⊆ θ) (hf : f ∈ U ^ θ) :
    (forcingThreadAction θ m f) ↾ η = forcingThreadAction η m (f ↾ η) := by
  let := IsFunction.of_mem hf
  unfold forcingThreadAction
  apply functions_eq_of_domain_values
  · rw [domain_restrict_eq, domain_definableGraph, domain_definableGraph]
    apply mem_ext
    intro i
    simp only [mem_inter_iff]
    exact ⟨fun hi ↦ hi.2, fun hi ↦ ⟨hη i hi, hi⟩⟩
  · intro i hi
    have hiη : i ∈ η := by
      have hh := hi
      simp only [domain_restrict_eq, domain_definableGraph, mem_inter_iff] at hh
      exact hh.2
    rw [value_restrict (by simpa only [domain_definableGraph] using hη i hiη) hiη,
      value_definableGraph _ _ _ (hη i hiη), value_definableGraph _ _ _ hiη,
      value_restrict ((domain_eq_of_mem_function hf).symm ▸ hη i hiη) hiη]

theorem forcingThreadAction_fixes {θ P U m f : V}
    (hf : f ∈ U ^ θ) (hv : ∀ i ∈ θ, f ‘ i ∈ P ‘ i)
    (hm : ∀ i ∈ θ, ∀ p ∈ P ‘ i, (m ‘ i) ‘ p = p) :
    forcingThreadAction θ m f = f := by
  let := IsFunction.of_mem hf
  unfold forcingThreadAction
  apply functions_eq_of_domain_values
  · rw [domain_definableGraph, domain_eq_of_mem_function hf]
  · intro i hi
    rw [domain_definableGraph] at hi
    rw [value_definableGraph _ _ _ hi, hm i hi _ (hv i hi)]

theorem forcingThreadAction_cancel {θ P U m n f : V}
    (hf : f ∈ U ^ θ) (hv : ∀ i ∈ θ, f ‘ i ∈ P ‘ i)
    (hn : ∀ i ∈ θ, ∀ p ∈ P ‘ i, (n ‘ i) ‘ ((m ‘ i) ‘ p) = p) :
    forcingThreadAction θ n (forcingThreadAction θ m f) = f := by
  let := IsFunction.of_mem hf
  unfold forcingThreadAction
  apply functions_eq_of_domain_values
  · rw [domain_definableGraph, domain_eq_of_mem_function hf]
  · intro i hi
    rw [domain_definableGraph] at hi
    rw [value_definableGraph _ _ _ hi, value_definableGraph _ _ _ hi, hn i hi _ (hv i hi)]

theorem forcingThreadAction_support {θ P E F m f k : V}
    (hv : ∀ i ∈ θ, f ‘ i ∈ P ‘ i)
    (hE : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ P ‘ i,
      (m ‘ j) ‘ ((E ‘ ⟨i, j⟩ₖ) ‘ p) = (F ‘ ⟨i, j⟩ₖ) ‘ ((m ‘ i) ‘ p))
    (hk : IsThreadSupport θ E f k) :
    IsThreadSupport θ F (forcingThreadAction θ m f) k := by
  refine ⟨hk.1, ?_⟩
  intro j hj hkj
  rw [forcingThreadAction_value hj, forcingThreadAction_value hk.1,
    hk.2 j hj hkj, hE k hk.1 j hj hkj _ (hv k hk.1)]

theorem forcingThreadAction_mem_direct {θ P Q π ρ E F U W m f : V}
    (hm : ∀ i ∈ θ, m ‘ i ∈ (Q ‘ i) ^ (P ‘ i))
    (hQ : ∀ i ∈ θ, Q ‘ i ⊆ W)
    (hc : ∀ j ∈ θ, ∀ i ∈ j, i ∈ θ → ∀ p ∈ P ‘ j,
      (ρ ‘ ⟨i, j⟩ₖ) ‘ ((m ‘ j) ‘ p) = (m ‘ i) ‘ ((π ‘ ⟨i, j⟩ₖ) ‘ p))
    (hE : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ P ‘ i,
      (m ‘ j) ‘ ((E ‘ ⟨i, j⟩ₖ) ‘ p) = (F ‘ ⟨i, j⟩ₖ) ‘ ((m ‘ i) ‘ p))
    (hf : f ∈ forcingDirectLimit θ P π E U) :
    forcingThreadAction θ m f ∈ forcingDirectLimit θ Q ρ F W := by
  obtain ⟨hf, k, hk⟩ := (mem_forcingDirectLimit_iff _ _ _ _ _ _).mp hf
  exact (mem_forcingDirectLimit_iff _ _ _ _ _ _).mpr
    ⟨forcingThreadAction_mem_inverse hm hQ hc hf, k,
      forcingThreadAction_support ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).2.1 hE hk⟩

theorem forcingThreadAction_support_iff {θ P Q E F U m n f k : V}
    (hf : f ∈ U ^ θ) (hv : ∀ i ∈ θ, f ‘ i ∈ P ‘ i)
    (hm : ∀ i ∈ θ, m ‘ i ∈ (Q ‘ i) ^ (P ‘ i))
    (hn : ∀ i ∈ θ, ∀ p ∈ P ‘ i, (n ‘ i) ‘ ((m ‘ i) ‘ p) = p)
    (hE : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ P ‘ i,
      (m ‘ j) ‘ ((E ‘ ⟨i, j⟩ₖ) ‘ p) = (F ‘ ⟨i, j⟩ₖ) ‘ ((m ‘ i) ‘ p))
    (hF : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ Q ‘ i,
      (n ‘ j) ‘ ((F ‘ ⟨i, j⟩ₖ) ‘ p) = (E ‘ ⟨i, j⟩ₖ) ‘ ((n ‘ i) ‘ p)) :
    IsThreadSupport θ F (forcingThreadAction θ m f) k ↔ IsThreadSupport θ E f k := by
  constructor
  · intro hk
    have hv' : ∀ i ∈ θ, (forcingThreadAction θ m f) ‘ i ∈ Q ‘ i := by
      intro i hi
      rw [forcingThreadAction_value hi]
      exact function_value_mem (hm i hi) (hv i hi)
    have hh := forcingThreadAction_support hv' hF hk
    rwa [forcingThreadAction_cancel hf hv hn] at hh
  · exact forcingThreadAction_support hv hE

/-- Support at an old direct cut is transported by the same coordinate family. -/
theorem forcingThreadAction_inherited_support {θ η P E F U m f k : V}
    (hη : η ⊆ θ) (hf : f ∈ U ^ θ) (hv : ∀ i ∈ θ, f ‘ i ∈ P ‘ i)
    (hE : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ P ‘ i,
      (m ‘ j) ‘ ((E ‘ ⟨i, j⟩ₖ) ‘ p) = (F ‘ ⟨i, j⟩ₖ) ‘ ((m ‘ i) ‘ p))
    (hk : IsThreadSupport η E (f ↾ η) k) :
    IsThreadSupport η F ((forcingThreadAction θ m f) ↾ η) k := by
  let := IsFunction.of_mem hf
  rw [forcingThreadAction_restrict hη hf]
  apply forcingThreadAction_support (P := P) ?_ ?_ hk
  · intro i hi
    rw [value_restrict ((domain_eq_of_mem_function hf).symm ▸ hη i hi) hi]
    exact hv i (hη i hi)
  · intro i hi j hj hij p hp
    exact hE i (hη i hi) j (hη j hj) hij p hp

noncomputable def forcingThreadActionMap (θ m C : V) : V :=
  definableGraph C (forcingThreadAction θ m) (by definability)

theorem forcingThreadActionMap_value {θ m C f : V} (hf : f ∈ C) :
    (forcingThreadActionMap θ m C) ‘ f = forcingThreadAction θ m f :=
  value_definableGraph _ _ _ hf

theorem forcingInverseLimit_mono_coordinates {θ P Q π U : V}
    (hQ : ∀ i ∈ θ, Q ‘ i ⊆ P ‘ i) :
    forcingInverseLimit θ Q π U ⊆ forcingInverseLimit θ P π U := by
  intro f hf
  obtain ⟨hfun, hv, hc⟩ := (mem_forcingInverseLimit_iff _ _ _ _ _).mp hf
  exact (mem_forcingInverseLimit_iff _ _ _ _ _).mpr
    ⟨hfun, fun i hi ↦ hQ i hi _ (hv i hi), hc⟩

theorem forcingDirectLimit_mono_coordinates {θ P Q π E U : V}
    (hQ : ∀ i ∈ θ, Q ‘ i ⊆ P ‘ i) :
    forcingDirectLimit θ Q π E U ⊆ forcingDirectLimit θ P π E U := by
  intro f hf
  obtain ⟨hf, hk⟩ := (mem_forcingDirectLimit_iff _ _ _ _ _ _).mp hf
  exact (mem_forcingDirectLimit_iff _ _ _ _ _ _).mpr
    ⟨forcingInverseLimit_mono_coordinates hQ _ hf, hk⟩

end ZFVP
