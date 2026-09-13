import ZFVP.SetTheory.RankCollection
import ZFVP.SetTheory.FiniteCodingClosure
import ZFVP.SetTheory.Relativization

/-! Every limit rank above omega is a model of Zermelo set theory. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem relativizedEvaluation_definable {ξ : Type*} {n : ℕ} (A : V)
    (φ : SetTheorySemiformula ξ n) (e : ξ → SetDomain A) :
    Language.Definable ℒₛₑₜ (fun v : Fin n → V ↦
      (relativize φ).Eval v (fun i ↦ i.elim A (fun j ↦ (e j).val))) :=
  ⟨(Rew.rewriteMap (fun i ↦ i.elim A (fun j ↦ (e j).val))) ▹ relativize φ,
    fun v ↦ by simp [Semiformula.eval_rewriteMap]⟩

variable {θ : V} [IsOrdinal θ] (hω : (ω : V) ∈ θ) (hs : ∀ β ∈ θ, succ β ∈ θ)

include hω in
theorem rankDomain_nonempty : Nonempty (SetDomain (hierarchy θ)) :=
  ⟨⟨ω, ordinal_subset_hierarchy θ _ hω⟩⟩

include hω hs in
theorem rankDomain_models_zermelo [Nonempty (SetDomain (hierarchy θ))] :
    (SetDomain (hierarchy θ))↓[ℒₛₑₜ] ⊧* 𝗭 := by
  let A := hierarchy θ
  let : Nonempty (SetDomain A) := rankDomain_nonempty hω
  have htrans := hierarchy_transitive θ
  have homega : (ω : V) ∈ A := ordinal_subset_hierarchy θ _ hω
  have hzero : (∅ : V) ∈ A := htrans.mem_trans empty_mem_ω homega
  refine ⟨?_⟩
  intro φ hφ
  cases hφ with
  | axiom_of_equality φ hφ => exact Theory.models (SetDomain A) (𝗘𝗤 ℒₛₑₜ) hφ
  | axiom_of_empty_set =>
    simp [models_iff, Axiom.empty]
    exact ⟨⟨∅, hzero⟩, fun y ↦ not_mem_empty (x := y.val)⟩
  | axiom_of_extentionality =>
    simp [models_iff, Axiom.extentionality]
    intro x y
    constructor
    · rintro rfl
      intro z
      rfl
    intro he
    apply Subtype.ext
    apply mem_ext
    intro z
    constructor
    · intro hz
      exact (he ⟨z, htrans.mem_trans hz x.property⟩).mp hz
    · intro hz
      exact (he ⟨z, htrans.mem_trans hz y.property⟩).mpr hz
  | axiom_of_pairing =>
    simp [models_iff, Axiom.pairing]
    intro x y
    refine ⟨⟨({x.val, y.val} : V), pair_mem_hierarchy_limit hs x.property y.property⟩, ?_⟩
    intro z
    change z.val ∈ ({x.val, y.val} : V) ↔ z = x ∨ z = y
    have he : (z.val = x.val ∨ z.val = y.val) ↔ (z = x ∨ z = y) :=
      or_congr Subtype.ext_iff.symm Subtype.ext_iff.symm
    simpa using he
  | axiom_of_union =>
    simp [models_iff, Axiom.union]
    intro x
    refine ⟨⟨⋃ˢ x.val, sUnion_mem_hierarchy_limit hs x.property⟩, ?_⟩
    intro z
    change z.val ∈ ⋃ˢ x.val ↔ ∃ w : SetDomain A, w.val ∈ x.val ∧ z.val ∈ w.val
    rw [mem_sUnion_iff]
    exact ⟨fun ⟨w, hw, hz⟩ ↦ ⟨⟨w, htrans.mem_trans hw x.property⟩, hw, hz⟩,
      fun ⟨w, hw, hz⟩ ↦ ⟨w.val, hw, hz⟩⟩
  | axiom_of_power_set =>
    simp [models_iff, Axiom.power]
    intro x
    refine ⟨⟨℘ x.val, power_mem_hierarchy_limit hs x.property⟩, ?_⟩
    intro z
    change z.val ∈ ℘ x.val ↔ z ⊆ x
    rw [mem_power_iff]
    constructor
    · intro h y hy
      exact h y.val hy
    · intro h y hy
      exact h ⟨y, htrans.mem_trans hy z.property⟩ hy
  | axiom_of_infinity =>
    simp [models_iff, Axiom.infinity, isEmpty, isSucc]
    refine ⟨⟨ω, homega⟩, ?_, ?_⟩
    · intro e he
      have he0 : e.val = (∅ : V) := by
        apply isEmpty_iff_eq_empty.mp
        intro y hy
        exact he ⟨y, htrans.mem_trans hy e.property⟩ hy
      change e.val ∈ (ω : V)
      rw [he0]
      exact empty_mem_ω
    · intro x hx y hy
      have hyS : y.val = succ x.val := by
        apply mem_ext
        intro z
        rw [mem_succ_iff]
        constructor
        · intro hz
          rcases (hy ⟨z, htrans.mem_trans hz y.property⟩).mp hz with he | hz
          · exact Or.inl (congrArg Subtype.val he)
          · exact Or.inr hz
        · intro hz
          have hzA : z ∈ A := hz.elim (fun he ↦ he.symm ▸ x.property)
            (fun hzx ↦ htrans.mem_trans hzx x.property)
          exact (hy ⟨z, hzA⟩).mpr (hz.elim (fun he ↦ Or.inl (Subtype.ext he)) Or.inr)
      change y.val ∈ (ω : V)
      rw [hyS]
      exact ω_succ_closed hx
  | axiom_of_foundation =>
    simp [models_iff, Axiom.foundation]
    intro x hx
    have : IsNonempty x.val := ⟨by obtain ⟨y, hy⟩ := hx.nonempty; exact ⟨y.val, hy⟩⟩
    obtain ⟨y, hy, hmin⟩ := foundation x.val
    exact ⟨⟨y, htrans.mem_trans hy x.property⟩, hy, fun z hz ↦ hmin z.val hz⟩
  | axiom_of_separation ψ =>
    simp [models_iff, Axiom.separationSchema, Semiformula.eval_univCl]
    intro e x
    let P := fun z : V ↦ (relativize ψ).Eval ![z] (fun i ↦ i.elim A (fun j ↦ (e j).val))
    have hP : ℒₛₑₜ-predicate P := by
      apply Language.Definable.of_iff (relativizedEvaluation_definable A ψ e)
      intro v
      have hv : ![v 0] = v := by funext i; exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
      change (relativize ψ).Eval ![v 0] _ ↔ (relativize ψ).Eval v _
      rw [hv]
    let b := sep x.val P hP
    have hb : b ⊆ x.val := sep_subset
    refine ⟨⟨b, subset_mem_hierarchy_limit hs x.property hb⟩, ?_⟩
    intro z
    change z.val ∈ b ↔ z.val ∈ x.val ∧ ψ.Eval ![z] e
    rw [mem_sep_iff]
    apply and_congr_right
    intro _
    have he := eval_relativize A ψ ![z] e
    have hv : (fun i ↦ ((![z] : Fin 1 → SetDomain A) i).val) = ![z.val] := by
      funext i; exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
    rw [hv] at he
    exact he

end ZFVP
