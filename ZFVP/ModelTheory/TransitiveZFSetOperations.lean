import ZFVP.ModelTheory.TransitiveZFCoding
import ZFVP.SetTheory.ForcingNames

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem domain_val (R : SetDomain U) : (domain R).val = domain R.val := by
  apply SetTheory.mem_ext_iff.mpr
  intro x
  constructor
  · intro hx
    let x' : SetDomain U := ⟨x, (inferInstance : IsTransitive U).mem_trans hx (domain R).property⟩
    obtain ⟨y, hy⟩ := mem_domain_iff.mp (show x' ∈ domain R from hx)
    exact mem_domain_iff.mpr ⟨y.val, by
      change (⟨x', y⟩ₖ : SetDomain U).val ∈ R.val at hy
      simpa only [kpair_val U] using hy⟩
  · intro hx
    obtain ⟨y, hy⟩ := mem_domain_iff.mp hx
    have hxyU := kpair_components_mem_transitive ((inferInstance : IsTransitive U).mem_trans hy R.property)
    let x' : SetDomain U := ⟨x, hxyU.1⟩
    let y' : SetDomain U := ⟨y, hxyU.2⟩
    have hp : (⟨x', y'⟩ₖ : SetDomain U) ∈ R := by
      change (⟨x', y'⟩ₖ : SetDomain U).val ∈ R.val
      simpa only [kpair_val U] using hy
    exact show x' ∈ domain R from mem_domain_of_kpair_mem hp

theorem range_val (R : SetDomain U) : (range R).val = range R.val := by
  apply SetTheory.mem_ext_iff.mpr
  intro y
  constructor
  · intro hy
    let y' : SetDomain U := ⟨y, (inferInstance : IsTransitive U).mem_trans hy (range R).property⟩
    obtain ⟨x, hx⟩ := mem_range_iff.mp (show y' ∈ range R from hy)
    exact mem_range_iff.mpr ⟨x.val, by
      change (⟨x, y'⟩ₖ : SetDomain U).val ∈ R.val at hx
      simpa only [kpair_val U] using hx⟩
  · intro hy
    obtain ⟨x, hx⟩ := mem_range_iff.mp hy
    have hxyU := kpair_components_mem_transitive ((inferInstance : IsTransitive U).mem_trans hx R.property)
    let x' : SetDomain U := ⟨x, hxyU.1⟩
    let y' : SetDomain U := ⟨y, hxyU.2⟩
    have hp : (⟨x', y'⟩ₖ : SetDomain U) ∈ R := by
      change (⟨x', y'⟩ₖ : SetDomain U).val ∈ R.val
      simpa only [kpair_val U] using hx
    exact show y' ∈ range R from mem_range_of_kpair_mem hp

theorem restrict_val (R A : SetDomain U) : (R ↾ A).val = R.val ↾ A.val := by
  apply SetTheory.mem_ext_iff.mpr
  intro p
  constructor
  · intro hp
    let p' : SetDomain U := ⟨p, (inferInstance : IsTransitive U).mem_trans hp (R ↾ A).property⟩
    obtain ⟨hpR, x, hx, y, he⟩ := mem_restrict_iff.mp (show p' ∈ R ↾ A from hp)
    exact mem_restrict_iff.mpr ⟨hpR, x.val, hx, y.val, by
      have hv := congrArg Subtype.val he
      simpa only [kpair_val U] using hv⟩
  · intro hp
    obtain ⟨hpR, x, hx, y, rfl⟩ := mem_restrict_iff.mp hp
    have hxyU := kpair_components_mem_transitive ((inferInstance : IsTransitive U).mem_trans hpR R.property)
    let x' : SetDomain U := ⟨x, hxyU.1⟩
    let y' : SetDomain U := ⟨y, hxyU.2⟩
    have hpair : (⟨x', y'⟩ₖ : SetDomain U) ∈ R := by
      change (⟨x', y'⟩ₖ : SetDomain U).val ∈ R.val
      simpa only [kpair_val U] using hpR
    have hm := kpair_mem_restrict_iff.mpr ⟨hpair, show x' ∈ A from hx⟩
    change (⟨x', y'⟩ₖ : SetDomain U).val ∈ (R ↾ A).val at hm
    simpa only [kpair_val U] using hm

theorem sUnion_val (A : SetDomain U) : (⋃ˢ A).val = ⋃ˢ A.val := by
  apply SetTheory.mem_ext_iff.mpr
  intro x
  constructor
  · intro hx
    let x' : SetDomain U := ⟨x, (inferInstance : IsTransitive U).mem_trans hx (⋃ˢ A).property⟩
    obtain ⟨y, hy, hxy⟩ := mem_sUnion_iff.mp (show x' ∈ ⋃ˢ A from hx)
    exact mem_sUnion_iff.mpr ⟨y.val, hy, hxy⟩
  · intro hx
    obtain ⟨y, hy, hxy⟩ := mem_sUnion_iff.mp hx
    have hyU := (inferInstance : IsTransitive U).mem_trans hy A.property
    let y' : SetDomain U := ⟨y, hyU⟩
    let x' : SetDomain U := ⟨x, (inferInstance : IsTransitive U).mem_trans hxy hyU⟩
    exact show x' ∈ ⋃ˢ A from mem_sUnion_iff.mpr ⟨y', hy, hxy⟩

theorem repl_val (A : SetDomain U) (F : SetDomain U → SetDomain U) (hF : ℒₛₑₜ-function₁ F)
    (G : V → V) (hG : ℒₛₑₜ-function₁ G) (hval : ∀ x ∈ A, (F x).val = G x.val) :
    (repl F hF A).val = repl G hG A.val := by
  apply SetTheory.mem_ext_iff.mpr
  intro z
  constructor
  · intro hz
    let z' : SetDomain U := ⟨z, (inferInstance : IsTransitive U).mem_trans hz (repl F hF A).property⟩
    obtain ⟨x, hx, he⟩ := (repl_spec hF).mp (show z' ∈ repl F hF A from hz)
    exact (repl_spec hG).mpr ⟨x.val, hx, (congrArg Subtype.val he).trans (hval x hx)⟩
  · intro hz
    obtain ⟨x, hx, rfl⟩ := (repl_spec hG).mp hz
    let x' : SetDomain U := ⟨x, (inferInstance : IsTransitive U).mem_trans hx A.property⟩
    have hm : (F x') ∈ repl F hF A := (repl_spec hF).mpr ⟨x', hx, rfl⟩
    change (F x').val ∈ (repl F hF A).val at hm
    simpa only [hval x' hx] using hm

theorem subnameClosed_val (C : SetDomain U) (hC : IsSubnameClosed C) : IsSubnameClosed C.val := by
  intro τ hτ σ hσ
  let τ' : SetDomain U := ⟨τ, (inferInstance : IsTransitive U).mem_trans hτ C.property⟩
  have hσ' : σ ∈ (domain τ').val := domain_val U τ' ▸ hσ
  let σ' : SetDomain U := ⟨σ, (inferInstance : IsTransitive U).mem_trans hσ' (domain τ').property⟩
  exact show σ' ∈ C from hC τ' hτ σ' hσ'

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem transitive_val (C : SetDomain U) (hC : IsTransitive C) : IsTransitive C.val := by
  constructor
  intro x hx y hy
  let x' : SetDomain U := ⟨x, (inferInstance : IsTransitive U).mem_trans hx C.property⟩
  let y' : SetDomain U := ⟨y, (inferInstance : IsTransitive U).mem_trans hy x'.property⟩
  exact show y' ∈ C from hC.transitive x' hx y' hy

end TransitiveZF
end ZFVP
