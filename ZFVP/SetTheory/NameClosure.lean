import ZFVP.SetTheory.InternalWellFounded
import ZFVP.SetTheory.DefinableGraph

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsSubnameClosed (X : V) : Prop := ∀ τ ∈ X, domain τ ⊆ X

instance isSubnameClosed_definable : ℒₛₑₜ-predicate[V] IsSubnameClosed := by
  unfold IsSubnameClosed
  definability

theorem transitive_subnameClosed {X : V} (hX : IsTransitive X) : IsSubnameClosed X := by
  intro τ hτ σ hσ
  obtain ⟨p, hσp⟩ := mem_domain_iff.mp hσ
  have hpX := hX.transitive τ hτ ⟨σ, p⟩ₖ hσp
  have hsX := hX.transitive ⟨σ, p⟩ₖ hpX ({σ} : V) (by simp [kpair])
  exact hX.transitive ({σ} : V) hsX σ (by simp)

/-- The least internal set containing `τ` and all iterated subnames. -/
noncomputable def nameClosure (τ : V) : V :=
  {σ ∈ transitiveClosure ({τ} : V) ; ∀ X : V, IsSubnameClosed X → τ ∈ X → σ ∈ X}

instance nameClosure_definable : ℒₛₑₜ-function₁[V] nameClosure := by
  have h : ℒₛₑₜ-relation[V] (fun C τ ↦ ∀ σ, σ ∈ C ↔
      σ ∈ transitiveClosure ({τ} : V) ∧ ∀ X : V, IsSubnameClosed X → τ ∈ X → σ ∈ X) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = nameClosure (v 1) ↔ _
  rw [mem_ext_iff]
  simp [nameClosure]

theorem mem_nameClosure_self (τ : V) : τ ∈ nameClosure τ := by
  exact mem_sep_iff.mpr ⟨subset_transitiveClosure _ _ (by simp), fun _ _ h ↦ h⟩

theorem nameClosure_subset_tc (τ : V) : nameClosure τ ⊆ transitiveClosure ({τ} : V) :=
  fun _ h ↦ (mem_sep_iff.mp h).1

theorem nameClosure_minimal {τ X : V} (hX : IsSubnameClosed X) (hτ : τ ∈ X) :
    nameClosure τ ⊆ X := fun _ h ↦ (mem_sep_iff.mp h).2 X hX hτ

theorem nameClosure_closed (τ : V) : IsSubnameClosed (nameClosure τ) := by
  intro σ hσ υ hυ
  have hs := mem_sep_iff.mp hσ
  refine mem_sep_iff.mpr ⟨?_, ?_⟩
  · exact transitive_subnameClosed (transitiveClosure_transitive _) σ hs.1 υ hυ
  · intro X hX hτ
    exact hX σ (hs.2 X hX hτ) υ hυ

theorem nameClosure_characterization (τ C : V) :
    C = nameClosure τ ↔ τ ∈ C ∧ IsSubnameClosed C ∧
      ∀ X : V, IsSubnameClosed X → τ ∈ X → C ⊆ X := by
  constructor
  · rintro rfl
    exact ⟨mem_nameClosure_self τ, nameClosure_closed τ, fun _ ↦ nameClosure_minimal⟩
  · rintro ⟨hτ, hC, hm⟩
    exact SetTheory.subset_antisymm (hm _ (nameClosure_closed τ) (mem_nameClosure_self τ))
      (nameClosure_minimal hC hτ)

theorem nameClosure_mem_mono {σ τ : V} (hσ : σ ∈ nameClosure τ) :
    nameClosure σ ⊆ nameClosure τ := nameClosure_minimal (nameClosure_closed τ) hσ

theorem subname_mem_nameClosure {σ p τ : V} (h : ⟨σ, p⟩ₖ ∈ τ) : σ ∈ nameClosure τ :=
  nameClosure_closed τ τ (mem_nameClosure_self τ) σ (mem_domain_of_kpair_mem h)

theorem rank_subname_lt {σ p τ : V} (h : ⟨σ, p⟩ₖ ∈ τ) : rank σ ∈ rank τ :=
  IsOrdinal.toIsTransitive.mem_trans (rank_kpair_left_lt σ p) (rank_mem h)

end ZFVP
