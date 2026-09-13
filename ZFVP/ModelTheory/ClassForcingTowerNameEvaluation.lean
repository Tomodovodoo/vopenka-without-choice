import ZFVP.ModelTheory.ClassForcingTowerModel

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace DefinableForcingTower
variable (T : DefinableForcingTower V)

theorem IsName.pair_subname {τ σ p : V} (hτ : T.IsName τ) (hσ : ⟨σ, p⟩ₖ ∈ τ) :
    T.IsName σ := hτ.subname T (subname_mem_nameClosure hσ)

theorem IsName.pair_condition {τ σ p : V} (hτ : T.IsName τ) (hσ : ⟨σ, p⟩ₖ ∈ τ) :
    T.Condition p := by
  obtain ⟨υ, q, hq, he⟩ := hτ τ (mem_nameClosure_self τ) _ hσ
  exact (kpair_iff.mp he).2 ▸ hq

theorem isName_iff_local (τ : V) : T.IsName τ ↔
    ∀ z ∈ τ, ∃ σ p : V, T.Condition p ∧ z = ⟨σ, p⟩ₖ ∧ T.IsName σ := by
  constructor
  · intro h z hz
    obtain ⟨σ, p, hp, he⟩ := h τ (mem_nameClosure_self τ) z hz
    exact ⟨σ, p, hp, he, h.pair_subname T (he ▸ hz)⟩
  · intro h
    let X : V := {σ ∈ nameClosure τ ; σ = τ ∨ T.IsName σ}
    have hτX : τ ∈ X := mem_sep_iff.mpr ⟨mem_nameClosure_self τ, Or.inl rfl⟩
    have hXC : IsSubnameClosed X := by
      intro σ hσ υ hυ
      obtain ⟨hσC, hσN⟩ := mem_sep_iff.mp hσ
      obtain ⟨p, hυp⟩ := mem_domain_iff.mp hυ
      refine mem_sep_iff.mpr ⟨nameClosure_closed τ σ hσC υ (mem_domain_of_kpair_mem hυp), Or.inr ?_⟩
      rcases hσN with rfl | hσN
      · obtain ⟨ν, q, _, he, hν⟩ := h _ hυp
        exact (kpair_iff.mp he).1 ▸ hν
      · exact hσN.pair_subname T hυp
    have hCX := nameClosure_minimal hXC hτX
    intro σ hσ z hz
    rcases (mem_sep_iff.mp (hCX σ hσ)).2 with rfl | hσN
    · obtain ⟨υ, p, hp, he, _⟩ := h z hz
      exact ⟨υ, p, hp, he⟩
    · exact hσN σ (mem_nameClosure_self σ) z hz

variable {G : Set V} (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)

theorem mem_ofClassName_iff (τ : T.Name) (x : T.ClassModel hG) :
    x ∈ T.ofClassName hG τ ↔ ∃ σ : T.Name, ∃ p ∈ G,
      ⟨σ.val, p⟩ₖ ∈ τ.val ∧ x = T.ofClassName hG σ := by
  let i := taggedNameStageBound τ.val
  have : IsOrdinal i := τ.property.bound_ordinal T
  have hτ := τ.property.bounded T
  constructor
  · intro hx
    rw [T.ofClassName_at hG τ hτ] at hx
    obtain ⟨y, hy, rfl⟩ := (T.fromBoundedStage hG i).endExtension _ x hx
    obtain ⟨ν, p, hpG, hνp, rfl⟩ := ((T.boundedContext hG i).mem_ofName_iff ⟨τ.val, hτ⟩ y).mp hy
    let σ : T.Name := ⟨ν.val, T.isName_of_bounded ν.property⟩
    exact ⟨σ, p, hpG.2, hνp, (T.ofClassName_at hG σ ν.property).symm⟩
  · rintro ⟨σ, p, hpG, hσp, rfl⟩
    have hσ := forcingName_subname hτ hσp
    rw [T.ofClassName_at hG τ hτ, T.ofClassName_at hG σ hσ]
    apply ((T.fromBoundedStage hG i).mem_iff _ _).mpr
    exact ((T.boundedContext hG i).mem_ofName_iff ⟨τ.val, hτ⟩ _).mpr
      ⟨⟨σ.val, hσ⟩, p, ⟨forcingName_condition hτ hσp, hpG⟩, hσp, rfl⟩

end DefinableForcingTower
end ZFVP
