import ZFVP.SetTheory.WoodinSourceIndex
import ZFVP.SetTheory.FunctionUnion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSparseBounds (θ : V) : V :=
  definableGraph θ (fun i ↦ succ (woodinSourceIndex i)) (by definability)

instance woodinSparseBounds_definable : ℒₛₑₜ-function₁[V] woodinSparseBounds := by
  have h : ℒₛₑₜ-relation[V] (fun b θ ↦ ∀ z, z ∈ b ↔
      ∃ i ∈ θ, z = ⟨i, succ (woodinSourceIndex i)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = woodinSparseBounds (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [woodinSparseBounds, mem_definableGraph_iff]

instance woodinSparseBounds_isFunction (θ : V) : IsFunction (woodinSparseBounds θ) := by
  unfold woodinSparseBounds
  infer_instance

theorem woodinSparseBounds_domain (θ : V) : domain (woodinSparseBounds θ) = θ := domain_definableGraph _ _ _

theorem woodinSparseBounds_value {θ i : V} (hi : i ∈ θ) :
    (woodinSparseBounds θ) ‘ i = succ (woodinSourceIndex i) := value_definableGraph _ _ _ hi

theorem woodinSparseBounds_mono {θ i j : V} [IsOrdinal θ] (hij : i ∈ j) (hj : j ∈ θ) :
    (woodinSparseBounds θ) ‘ i ⊆ (woodinSparseBounds θ) ‘ j := by
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hij
  have hi := IsOrdinal.toIsTransitive.mem_trans hij hj
  rw [woodinSparseBounds_value hi, woodinSparseBounds_value hj]
  have hs : woodinSourceIndex i ∈ woodinSourceIndex j := woodinSourceIndex_mem_iff.mpr hij
  intro x hx
  apply mem_succ_iff.mpr
  apply Or.inr
  rcases mem_succ_iff.mp hx with rfl | hx
  · exact hs
  · exact IsOrdinal.toIsTransitive.mem_trans hx hs

theorem woodinSparseBounds_limit_mem {θ i : V} [IsOrdinal θ]
    (h0 : ∅ ∈ θ) (hlim : ∀ j ∈ θ, succ j ∈ θ) (hi : i ∈ θ) :
    (woodinSparseBounds θ) ‘ i ∈ θ := by
  let := IsOrdinal.of_mem hi
  rw [woodinSparseBounds_value hi]
  apply hlim
  rw [← woodinSourceIndex_limit θ h0 hlim]
  exact woodinSourceIndex_mem_iff.mpr hi

theorem woodinSparseBounds_limit_subset {θ i : V} [IsOrdinal θ]
    (h0 : ∅ ∈ θ) (hlim : ∀ j ∈ θ, succ j ∈ θ) (hi : i ∈ θ) :
    (woodinSparseBounds θ) ‘ i ⊆ θ :=
  IsOrdinal.toIsTransitive.transitive _ (woodinSparseBounds_limit_mem h0 hlim hi)

theorem woodinSparseBounds_self_mem {θ i : V} [IsOrdinal θ] (hi : i ∈ θ) :
    i ∈ (woodinSparseBounds θ) ‘ i := by
  let := IsOrdinal.of_mem hi
  let : IsOrdinal (1 : V) := IsOrdinal.of_mem (show (1 : V) ∈ (ω : V) by simp)
  rw [woodinSparseBounds_value hi]
  exact mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (ordinal_subset_add_right (1 : V) i))

theorem woodinSparseBounds_cover {θ x : V} [IsOrdinal θ] (hx : x ∈ θ) :
    ∃ i ∈ θ, x ∈ (woodinSparseBounds θ) ‘ i := ⟨x, hx, woodinSparseBounds_self_mem hx⟩

theorem woodinSparseBounds_agrees {θ η i : V} (hθη : θ ⊆ η) (hi : i ∈ θ) :
    (woodinSparseBounds η) ‘ i = (woodinSparseBounds θ) ‘ i := by
  rw [woodinSparseBounds_value (hθη i hi), woodinSparseBounds_value hi]

theorem woodinSparseBounds_restrict {θ η : V} (hθη : θ ⊆ η) :
    (woodinSparseBounds η) ↾ θ = woodinSparseBounds θ := by
  apply functions_eq_of_domain_values
  · rw [domain_restrict_eq, woodinSparseBounds_domain, woodinSparseBounds_domain,
      inter_eq_right_of_subset hθη]
  · intro i hi
    have hiθ : i ∈ θ := by
      rw [domain_restrict_eq, woodinSparseBounds_domain] at hi
      exact (mem_inter_iff.mp hi).2
    rw [value_restrict (by rw [woodinSparseBounds_domain]; exact hθη i hiθ) hiθ]
    exact woodinSparseBounds_agrees hθη hiθ

end ZFVP
