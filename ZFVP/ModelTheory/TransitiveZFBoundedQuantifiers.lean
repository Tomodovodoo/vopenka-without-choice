import ZFVP.ModelTheory.TransitiveZFNames

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem kpair_mem_val_iff (x y A : SetDomain U) :
    (⟨x, y⟩ₖ : SetDomain U) ∈ A ↔ (⟨x.val, y.val⟩ₖ : V) ∈ A.val := by
  change (⟨x, y⟩ₖ : SetDomain U).val ∈ A.val ↔ _
  rw [kpair_val U]

theorem forall_mem_val_iff (A : SetDomain U) (Φ : SetDomain U → Prop) (Ψ : V → Prop)
    (h : ∀ x : SetDomain U, Φ x ↔ Ψ x.val) :
    (∀ x ∈ A, Φ x) ↔ ∀ x ∈ A.val, Ψ x := by
  constructor
  · intro hf x hx
    let x' : SetDomain U := ⟨x, (inferInstance : IsTransitive U).mem_trans hx A.property⟩
    exact (h x').mp (hf x' hx)
  · intro hf x hx
    exact (h x).mpr (hf x.val hx)

theorem exists_mem_val_iff (A : SetDomain U) (Φ : SetDomain U → Prop) (Ψ : V → Prop)
    (h : ∀ x : SetDomain U, Φ x ↔ Ψ x.val) :
    (∃ x ∈ A, Φ x) ↔ ∃ x ∈ A.val, Ψ x := by
  constructor
  · rintro ⟨x, hx, hΦ⟩
    exact ⟨x.val, hx, (h x).mp hΦ⟩
  · rintro ⟨x, hx, hΨ⟩
    let x' : SetDomain U := ⟨x, (inferInstance : IsTransitive U).mem_trans hx A.property⟩
    exact ⟨x', hx, (h x').mpr hΨ⟩

theorem forall_pair_mem_val_iff (A : SetDomain U) (Φ : SetDomain U → SetDomain U → Prop)
    (Ψ : V → V → Prop) (h : ∀ x y : SetDomain U, Φ x y ↔ Ψ x.val y.val) :
    (∀ x y, (⟨x, y⟩ₖ : SetDomain U) ∈ A → Φ x y) ↔
      ∀ x y, (⟨x, y⟩ₖ : V) ∈ A.val → Ψ x y := by
  constructor
  · intro hf x y hxy
    have hc := kpair_components_mem_transitive ((inferInstance : IsTransitive U).mem_trans hxy A.property)
    let x' : SetDomain U := ⟨x, hc.1⟩
    let y' : SetDomain U := ⟨y, hc.2⟩
    exact (h x' y').mp (hf x' y' ((kpair_mem_val_iff U x' y' A).mpr hxy))
  · intro hf x y hxy
    exact (h x y).mpr (hf x.val y.val ((kpair_mem_val_iff U x y A).mp hxy))

theorem exists_pair_mem_val_iff (A : SetDomain U) (Φ : SetDomain U → SetDomain U → Prop)
    (Ψ : V → V → Prop) (h : ∀ x y : SetDomain U, Φ x y ↔ Ψ x.val y.val) :
    (∃ x y, (⟨x, y⟩ₖ : SetDomain U) ∈ A ∧ Φ x y) ↔
      ∃ x y, (⟨x, y⟩ₖ : V) ∈ A.val ∧ Ψ x y := by
  constructor
  · rintro ⟨x, y, hxy, hΦ⟩
    exact ⟨x.val, y.val, (kpair_mem_val_iff U x y A).mp hxy, (h x y).mp hΦ⟩
  · rintro ⟨x, y, hxy, hΨ⟩
    have hc := kpair_components_mem_transitive ((inferInstance : IsTransitive U).mem_trans hxy A.property)
    let x' : SetDomain U := ⟨x, hc.1⟩
    let y' : SetDomain U := ⟨y, hc.2⟩
    exact ⟨x', y', (kpair_mem_val_iff U x' y' A).mpr hxy, (h x' y').mpr hΨ⟩

end TransitiveZF
end ZFVP
