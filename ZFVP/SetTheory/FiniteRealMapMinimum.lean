import ZFVP.SetTheory.RealMapOrder
import ZFVP.SetTheory.FiniteSets

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A definable strict transitive relation has a minimal point in each nonempty
internally finite set. The induction also covers nonstandard finite sets. -/
theorem internallyFinite_minimal (R : V → V → Prop) (hR : ℒₛₑₜ-relation R)
    (hirr : ∀ a, ¬R a a) (htrans : ∀ a b c, R a b → R b c → R a c)
    {C : V} (hC : IsInternallyFinite C) (hne : IsNonempty C) :
    ∃ a ∈ C, ∀ b ∈ C, ¬R b a := by
  classical
  have hall : ∀ A : V, IsInternallyFinite A →
      IsNonempty A → ∃ a ∈ A, ∀ b ∈ A, ¬R b a := by
    apply internallyFinite_induction
      (fun A ↦ IsNonempty A → ∃ a ∈ A, ∀ b ∈ A, ¬R b a) (by definability)
    · intro h
      obtain ⟨a, ha⟩ := isNonempty_def.mp h
      exact (not_mem_empty ha).elim
    · intro A a ih _
      by_cases hA : IsNonempty A
      · obtain ⟨b, hb, hmin⟩ := ih hA
        by_cases hab : R a b
        · refine ⟨a, by simp, ?_⟩
          intro c hc hca
          rcases mem_insert.mp hc with rfl | hc
          · exact hirr _ hca
          · exact hmin c hc (htrans c a b hca hab)
        · refine ⟨b, mem_insert.mpr (Or.inr hb), ?_⟩
          intro c hc hcb
          rcases mem_insert.mp hc with rfl | hc
          · exact hab hcb
          · exact hmin c hc hcb
      · refine ⟨a, by simp, ?_⟩
        intro b hb hba
        rcases mem_insert.mp hb with rfl | hb
        · exact hirr _ hba
        · exact hA (isNonempty_def.mpr ⟨b, hb⟩)
  exact hall C hC hne

/-- A least map in the lexicographic order for the fixed domain `B`. -/
def IsRealMapMinimum (B C a : V) : Prop :=
  a ∈ C ∧ ∀ b ∈ C, ¬RealMapLexLt B b a

instance isRealMapMinimum_definable : ℒₛₑₜ-relation₃[V] IsRealMapMinimum := by
  unfold IsRealMapMinimum
  definability

theorem realMapMinimum_unique {B C a b : V} (hB : B ⊆ (ω : V))
    (hfun : C ⊆ (℘ (ω : V)) ^ B)
    (ha : IsRealMapMinimum B C a) (hb : IsRealMapMinimum B C b) : a = b := by
  rcases realMapLexLt_trichotomy hB (hfun a ha.1) (hfun b hb.1) with hab | he | hba
  · exact (hb.2 a ha.1 hab).elim
  · exact he
  · exact (ha.2 b hb.1 hba).elim

theorem finiteRealMapMinimum_existsUnique {B C : V} (hB : B ⊆ (ω : V))
    (hC : IsInternallyFinite C) (hne : IsNonempty C)
    (hfun : C ⊆ (℘ (ω : V)) ^ B) : ∃! a, IsRealMapMinimum B C a := by
  obtain ⟨a, ha, hmin⟩ := internallyFinite_minimal (RealMapLexLt B) (by definability)
    (realMapLexLt_irrefl B) (fun _ _ _ ↦ realMapLexLt_trans hB) hC hne
  exact ⟨a, ⟨ha, hmin⟩, fun b hb ↦ realMapMinimum_unique hB hfun hb ⟨ha, hmin⟩⟩

/-- Union of the singleton of least maps. Its value is the least map whenever
`C` is a nonempty internally finite family of real-valued maps on `B ⊆ ω`. -/
noncomputable def finiteRealMapMinimum (B C : V) : V :=
  ⋃ˢ {a ∈ C ; ∀ b ∈ C, ¬RealMapLexLt B b a}

instance finiteRealMapMinimum_definable : ℒₛₑₜ-function₂[V] finiteRealMapMinimum := by
  have h : ℒₛₑₜ-relation₃[V] (fun x B C ↦ ∀ y, y ∈ x ↔
      ∃ a ∈ C, (∀ b ∈ C, ¬RealMapLexLt B b a) ∧ y ∈ a) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = finiteRealMapMinimum (v 1) (v 2) ↔ _
  simp only [finiteRealMapMinimum, mem_ext_iff, mem_sUnion_iff, mem_sep_iff, and_assoc]

theorem finiteRealMapMinimum_eq_of_minimum {B C a : V} (hB : B ⊆ (ω : V))
    (hfun : C ⊆ (℘ (ω : V)) ^ B) (ha : IsRealMapMinimum B C a) :
    finiteRealMapMinimum B C = a := by
  have he : {b ∈ C ; ∀ c ∈ C, ¬RealMapLexLt B c b} = ({a} : V) := by
    apply mem_ext
    intro b
    rw [mem_sep_iff, mem_singleton_iff]
    constructor
    · intro hb
      exact realMapMinimum_unique hB hfun hb ha
    · rintro rfl
      exact ha
  unfold finiteRealMapMinimum
  rw [he]
  simp

theorem finiteRealMapMinimum_spec {B C : V} (hB : B ⊆ (ω : V))
    (hC : IsInternallyFinite C) (hne : IsNonempty C)
    (hfun : C ⊆ (℘ (ω : V)) ^ B) :
    IsRealMapMinimum B C (finiteRealMapMinimum B C) := by
  obtain ⟨a, ha, _⟩ := finiteRealMapMinimum_existsUnique hB hC hne hfun
  rwa [finiteRealMapMinimum_eq_of_minimum hB hfun ha]

theorem finiteRealMapMinimum_mem {B C : V} (hB : B ⊆ (ω : V))
    (hC : IsInternallyFinite C) (hne : IsNonempty C)
    (hfun : C ⊆ (℘ (ω : V)) ^ B) : finiteRealMapMinimum B C ∈ C :=
  (finiteRealMapMinimum_spec hB hC hne hfun).1

end ZFVP
