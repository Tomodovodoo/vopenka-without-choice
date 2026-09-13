import ZFVP.ModelTheory.ElementaryInclusion
import ZFVP.SetTheory.MostowskiCollapse

/-! The weakly LS and LS definitions in V13, including the collapse and
function-closure clauses, and their preservation at nonzero limits. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def HasSmallTransitiveCollapse (κ X : V) : Prop :=
  ∃ C ∈ hierarchy κ, ∃ f, IsTransitiveCollapse (membershipRelation X) X C f

instance hasSmallTransitiveCollapse_definable : ℒₛₑₜ-relation[V] HasSmallTransitiveCollapse := by
  unfold HasSmallTransitiveCollapse
  definability

def IsWeaklyLSCardinal (κ : V) : Prop :=
  IsInitialOrdinal κ ∧ (ω : V) ∈ κ ∧
    ∀ γ ∈ κ, ∀ α, IsOrdinal α → κ ⊆ α → ∀ x ∈ hierarchy α,
      ∃ X, IsElementaryInclusion X (hierarchy α) ∧ hierarchy γ ⊆ X ∧
        x ∈ X ∧ HasSmallTransitiveCollapse κ X

def IsLSCardinal (κ : V) : Prop :=
  IsInitialOrdinal κ ∧ (ω : V) ∈ κ ∧
    ∀ γ ∈ κ, ∀ α, IsOrdinal α → κ ⊆ α → ∀ x ∈ hierarchy α,
      ∃ β X, IsOrdinal β ∧ α ⊆ β ∧ IsElementaryInclusion X (hierarchy β) ∧
        hierarchy γ ⊆ X ∧ x ∈ X ∧ HasSmallTransitiveCollapse κ X ∧
        (X ∩ hierarchy α) ^ (hierarchy γ) ⊆ X

instance isWeaklyLSCardinal_definable : ℒₛₑₜ-predicate[V] IsWeaklyLSCardinal := by
  unfold IsWeaklyLSCardinal
  definability

instance isLSCardinal_definable : ℒₛₑₜ-predicate[V] IsLSCardinal := by
  unfold IsLSCardinal
  definability

theorem HasSmallTransitiveCollapse.mono {κ μ X : V} [IsOrdinal κ] [IsOrdinal μ]
    (h : HasSmallTransitiveCollapse μ X) (hμκ : μ ⊆ κ) : HasSmallTransitiveCollapse κ X := by
  obtain ⟨C, hC, f, hf⟩ := h
  exact ⟨C, hierarchy_mono hμκ C hC, f, hf⟩

theorem initialOrdinal_of_cofinally_initial {κ : V} [IsOrdinal κ]
    (h : ∀ α ∈ κ, ∃ μ ∈ κ, α ∈ μ ∧ IsInitialOrdinal μ) : IsInitialOrdinal κ := by
  refine ⟨inferInstance, ?_⟩
  intro α hα hinj
  obtain ⟨μ, hμ, hαμ, hi⟩ := h α hα
  exact hi.2 α hαμ ((cardLE_of_subset (IsOrdinal.toIsTransitive.transitive _ hμ)).trans hinj)

theorem lsCardinal_of_cofinally_ls {κ : V} [IsOrdinal κ] (hne : IsNonempty κ)
    (h : ∀ α ∈ κ, ∃ μ ∈ κ, α ∈ μ ∧ IsLSCardinal μ) : IsLSCardinal κ := by
  have hi := initialOrdinal_of_cofinally_initial (fun α hα ↦ by
    obtain ⟨μ, hμ, hαμ, hLS⟩ := h α hα
    exact ⟨μ, hμ, hαμ, hLS.1⟩)
  have hω : (ω : V) ∈ κ := by
    obtain ⟨α, hα⟩ := hne
    obtain ⟨μ, hμ, _, hLS⟩ := h α hα
    exact IsOrdinal.toIsTransitive.mem_trans hLS.2.1 hμ
  refine ⟨hi, hω, ?_⟩
  intro γ hγ α hα hκα x hx
  obtain ⟨μ, hμ, hγμ, hLS⟩ := h γ hγ
  let := hLS.1.1
  have hμκ : μ ⊆ κ := IsOrdinal.toIsTransitive.transitive _ hμ
  obtain ⟨β, X, hβ, hαβ, he, hγX, hxX, hc, hf⟩ :=
    hLS.2.2 γ hγμ α hα (subset_trans hμκ hκα) x hx
  exact ⟨β, X, hβ, hαβ, he, hγX, hxX, hc.mono hμκ, hf⟩

theorem weaklyLSCardinal_of_cofinally_weaklyLS {κ : V} [IsOrdinal κ] (hne : IsNonempty κ)
    (h : ∀ α ∈ κ, ∃ μ ∈ κ, α ∈ μ ∧ IsWeaklyLSCardinal μ) : IsWeaklyLSCardinal κ := by
  have hi := initialOrdinal_of_cofinally_initial (fun α hα ↦ by
    obtain ⟨μ, hμ, hαμ, hLS⟩ := h α hα
    exact ⟨μ, hμ, hαμ, hLS.1⟩)
  have hω : (ω : V) ∈ κ := by
    obtain ⟨α, hα⟩ := hne
    obtain ⟨μ, hμ, _, hLS⟩ := h α hα
    exact IsOrdinal.toIsTransitive.mem_trans hLS.2.1 hμ
  refine ⟨hi, hω, ?_⟩
  intro γ hγ α hα hκα x hx
  obtain ⟨μ, hμ, hγμ, hLS⟩ := h γ hγ
  let := hLS.1.1
  have hμκ : μ ⊆ κ := IsOrdinal.toIsTransitive.transitive _ hμ
  obtain ⟨X, he, hγX, hxX, hc⟩ := hLS.2.2 γ hγμ α hα (subset_trans hμκ hκα) x hx
  exact ⟨X, he, hγX, hxX, hc.mono hμκ⟩

end ZFVP
