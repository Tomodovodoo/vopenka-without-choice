import ZFVP.ModelTheory.TransitiveZFSetOperations

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem singleton_val (x : SetDomain U) : ({x} : SetDomain U).val = ({x.val} : V) := by
  have h₁ : ({x} : SetDomain U) = doubleton x x := by ext z; simp
  have h₂ : doubleton x.val x.val = ({x.val} : V) := by ext z; simp
  rw [h₁, doubleton_val U, h₂]

theorem insert_val (x A : SetDomain U) : (insert x A).val = insert x.val A.val := by
  rw [insert_def, union_val U, singleton_val U, ← insert_def]

/-- Total relational evaluation is absolute, including off-domain inputs. -/
theorem value_val_total (f x : SetDomain U) : (f ‘ x).val = f.val ‘ x.val := by
  apply SetTheory.mem_ext_iff.mpr
  intro z
  constructor
  · intro hz
    let z' : SetDomain U := ⟨z, (inferInstance : IsTransitive U).mem_trans hz (f ‘ x).property⟩
    have h : z' ∈ f ‘ x := hz
    change z' ∈ {t ∈ ⋃ˢ range f ; ∃ y, t ∈ y ∧ ⟨x, y⟩ₖ ∈ f} at h
    obtain ⟨hb, y, hzy, hxy⟩ := mem_sep_iff.mp h
    have hb' : z ∈ ⋃ˢ range f.val := by
      change z ∈ (⋃ˢ range f).val at hb
      simpa only [sUnion_val U, range_val U] using hb
    have hp : ⟨x.val, y.val⟩ₖ ∈ f.val := by
      change (⟨x, y⟩ₖ : SetDomain U).val ∈ f.val at hxy
      simpa only [kpair_val U] using hxy
    exact mem_sep_iff.mpr ⟨hb', y.val, hzy, hp⟩
  · intro hz
    change z ∈ {t ∈ ⋃ˢ range f.val ; ∃ y, t ∈ y ∧ ⟨x.val, y⟩ₖ ∈ f.val} at hz
    obtain ⟨hb, y, hzy, hxy⟩ := mem_sep_iff.mp hz
    have hyU := (kpair_components_mem_transitive ((inferInstance : IsTransitive U).mem_trans hxy f.property)).2
    let y' : SetDomain U := ⟨y, hyU⟩
    let z' : SetDomain U := ⟨z, (inferInstance : IsTransitive U).mem_trans hzy hyU⟩
    have hb' : z' ∈ ⋃ˢ range f := by
      change z ∈ (⋃ˢ range f).val
      simpa only [sUnion_val U, range_val U] using hb
    have hp : (⟨x, y'⟩ₖ : SetDomain U) ∈ f := by
      change (⟨x, y'⟩ₖ : SetDomain U).val ∈ f.val
      simpa only [kpair_val U] using hxy
    exact show z' ∈ f ‘ x from mem_sep_iff.mpr ⟨hb', y', hzy, hp⟩

theorem sep_val (A : SetDomain U) (P : SetDomain U → Prop) (hP : ℒₛₑₜ-predicate P)
    (Q : V → Prop) (hQ : ℒₛₑₜ-predicate Q) (hiff : ∀ x ∈ A, P x ↔ Q x.val) :
    (sep A P hP).val = sep A.val Q hQ := by
  apply SetTheory.mem_ext_iff.mpr
  intro x
  constructor
  · intro hx
    let x' : SetDomain U := ⟨x, (inferInstance : IsTransitive U).mem_trans hx (sep A P hP).property⟩
    obtain ⟨hxA, hxP⟩ := mem_sep_iff.mp (show x' ∈ sep A P hP from hx)
    exact mem_sep_iff.mpr ⟨hxA, (hiff x' hxA).mp hxP⟩
  · intro hx
    obtain ⟨hxA, hxQ⟩ := mem_sep_iff.mp hx
    let x' : SetDomain U := ⟨x, (inferInstance : IsTransitive U).mem_trans hxA A.property⟩
    exact show x' ∈ sep A P hP from mem_sep_iff.mpr ⟨hxA, (hiff x' hxA).mpr hxQ⟩

end TransitiveZF
end ZFVP
