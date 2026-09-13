import ZFVP.SetTheory.ClassRelativization
import ZFVP.SetTheory.RankZF

/-! A definable class which is transitive, contains `ω` and is closed under pairs, unions, relative
power sets, relativized separation and relativized replacement is a model of the external ZF
axioms. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The class defined by the two-variable formula `H` with the parameter `a`. -/
abbrev classOf (H : SetTheorySemisentence 2) (a : V) (x : V) : Prop := H.Evalb ![x, a]

theorem relativizedClassEvaluation_definable {ξ : Type*} {n : ℕ} (H : SetTheorySemisentence 2) (a : V)
    (φ : SetTheorySemiformula ξ n) (e : ξ → ClassDomain (classOf H a)) :
    Language.Definable ℒₛₑₜ (fun v : Fin n → V ↦
      (relativizeClass H φ).Eval v (fun i ↦ i.elim a (fun j ↦ (e j).val))) :=
  ⟨(Rew.rewriteMap (fun i ↦ i.elim a (fun j ↦ (e j).val))) ▹ relativizeClass H φ,
    fun v ↦ by simp [Semiformula.eval_rewriteMap]⟩

section

variable (H : SetTheorySemisentence 2) (a : V)
  (htrans : ∀ x, classOf H a x → ∀ y ∈ x, classOf H a y)
  (homega : classOf H a (ω : V))
  (hpair : ∀ x y, classOf H a x → classOf H a y → classOf H a ({x, y} : V))
  (hunion : ∀ x, classOf H a x → classOf H a (⋃ˢ x))
  (hpower : ∀ x, classOf H a x → ∃ p, classOf H a p ∧ ∀ y, y ∈ p ↔ classOf H a y ∧ y ⊆ x)
  (hsep : ∀ (ψ : SetTheorySemiformula ℕ 1) (e : ℕ → ClassDomain (classOf H a)) (x : V),
    classOf H a x → ∃ s, classOf H a s ∧ ∀ y, y ∈ s ↔ y ∈ x ∧
      (relativizeClass H ψ).Eval ![y] (fun i ↦ i.elim a (fun j ↦ (e j).val)))
  (hrepl : ∀ (ψ : SetTheorySemiformula ℕ 2) (e : ℕ → ClassDomain (classOf H a)) (x : V),
    classOf H a x →
    (∀ z, classOf H a z → ∃! w, classOf H a w ∧
      (relativizeClass H ψ).Eval ![z, w] (fun i ↦ i.elim a (fun j ↦ (e j).val))) →
    ∃ b, classOf H a b ∧ ∀ y, y ∈ b ↔ classOf H a y ∧ ∃ z ∈ x,
      (relativizeClass H ψ).Eval ![z, y] (fun i ↦ i.elim a (fun j ↦ (e j).val)))

include homega in
theorem classDomain_nonempty : Nonempty (ClassDomain (classOf H a)) := ⟨⟨ω, homega⟩⟩

include htrans homega hpair hunion hpower hsep hrepl in
/-- The external ZF axioms hold in a transitive class closed under the ZF operations. -/
theorem classDomain_models_zf [Nonempty (ClassDomain (classOf H a))] :
    (ClassDomain (classOf H a))↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  have hzero : classOf H a (∅ : V) := htrans _ homega _ empty_mem_ω
  refine ⟨?_⟩
  intro φ hφ
  cases hφ with
  | axiom_of_equality φ hφ => exact Theory.models (ClassDomain (classOf H a)) (𝗘𝗤 ℒₛₑₜ) hφ
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
      exact (he ⟨z, htrans _ x.property z hz⟩).mp hz
    · intro hz
      exact (he ⟨z, htrans _ y.property z hz⟩).mpr hz
  | axiom_of_pairing =>
    simp [models_iff, Axiom.pairing]
    intro x y
    refine ⟨⟨({x.val, y.val} : V), hpair _ _ x.property y.property⟩, ?_⟩
    intro z
    change z.val ∈ ({x.val, y.val} : V) ↔ z = x ∨ z = y
    have he : (z.val = x.val ∨ z.val = y.val) ↔ (z = x ∨ z = y) :=
      or_congr Subtype.ext_iff.symm Subtype.ext_iff.symm
    simpa using he
  | axiom_of_union =>
    simp [models_iff, Axiom.union]
    intro x
    refine ⟨⟨⋃ˢ x.val, hunion _ x.property⟩, ?_⟩
    intro z
    change z.val ∈ ⋃ˢ x.val ↔ ∃ w : ClassDomain (classOf H a), w.val ∈ x.val ∧ z.val ∈ w.val
    rw [mem_sUnion_iff]
    exact ⟨fun ⟨w, hw, hz⟩ ↦ ⟨⟨w, htrans _ x.property w hw⟩, hw, hz⟩,
      fun ⟨w, hw, hz⟩ ↦ ⟨w.val, hw, hz⟩⟩
  | axiom_of_power_set =>
    simp [models_iff, Axiom.power]
    intro x
    obtain ⟨p, hp, hmem⟩ := hpower x.val x.property
    refine ⟨⟨p, hp⟩, ?_⟩
    intro z
    change z.val ∈ p ↔ z ⊆ x
    rw [hmem]
    constructor
    · rintro ⟨-, h⟩ y hy
      exact h y.val hy
    · intro h
      exact ⟨z.property, fun y hy ↦ h ⟨y, htrans _ z.property y hy⟩ hy⟩
  | axiom_of_infinity =>
    simp [models_iff, Axiom.infinity, isEmpty, isSucc]
    refine ⟨⟨ω, homega⟩, ?_, ?_⟩
    · intro e he
      have he0 : e.val = (∅ : V) := by
        apply isEmpty_iff_eq_empty.mp
        intro y hy
        exact he ⟨y, htrans _ e.property y hy⟩ hy
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
          rcases (hy ⟨z, htrans _ y.property z hz⟩).mp hz with he | hz
          · exact Or.inl (congrArg Subtype.val he)
          · exact Or.inr hz
        · intro hz
          have hzA : classOf H a z := hz.elim (fun he ↦ he.symm ▸ x.property)
            (fun hzx ↦ htrans _ x.property z hzx)
          exact (hy ⟨z, hzA⟩).mpr (hz.elim (fun he ↦ Or.inl (Subtype.ext he)) Or.inr)
      change y.val ∈ (ω : V)
      rw [hyS]
      exact ω_succ_closed hx
  | axiom_of_foundation =>
    simp [models_iff, Axiom.foundation]
    intro x hx
    have : IsNonempty x.val := ⟨by obtain ⟨y, hy⟩ := hx.nonempty; exact ⟨y.val, hy⟩⟩
    obtain ⟨y, hy, hmin⟩ := foundation x.val
    exact ⟨⟨y, htrans _ x.property y hy⟩, hy, fun z hz ↦ hmin z.val hz⟩
  | axiom_of_separation ψ =>
    simp [models_iff, Axiom.separationSchema, Semiformula.eval_univCl]
    intro e x
    obtain ⟨s, hs, hmem⟩ := hsep ψ e x.val x.property
    refine ⟨⟨s, hs⟩, ?_⟩
    intro z
    change z.val ∈ s ↔ z.val ∈ x.val ∧ ψ.Eval ![z] e
    rw [hmem]
    apply and_congr_right
    intro _
    have he := eval_relativizeClass H a ψ ![z] e
    have hv : (fun i ↦ ((![z] : Fin 1 → ClassDomain (classOf H a)) i).val) = ![z.val] := by
      funext i; exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
    rw [hv] at he
    exact he
  | axiom_of_replacement ψ =>
    simp [models_iff, Axiom.replacementSchema, Semiformula.eval_univCl]
    intro e hf X
    let R := fun x y : V ↦ (relativizeClass H ψ).Eval ![x, y] (fun i ↦ i.elim a (fun j ↦ (e j).val))
    have hRiff (x y : ClassDomain (classOf H a)) : R x.val y.val ↔ ψ.Eval ![x, y] e := by
      have he := eval_relativizeClass H a ψ ![x, y] e
      have hv : (fun i ↦ ((![x, y] : Fin 2 → ClassDomain (classOf H a)) i).val) = ![x.val, y.val] := by
        funext i
        exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
      rw [hv] at he
      exact he
    have hfun : ∀ z, classOf H a z → ∃! w, classOf H a w ∧ R z w := by
      intro z hz
      obtain ⟨w, hw, huw⟩ := hf ⟨z, hz⟩
      refine ⟨w.val, ⟨w.property, (hRiff ⟨z, hz⟩ w).mpr hw⟩, ?_⟩
      intro v hv
      exact congrArg Subtype.val (huw ⟨v, hv.1⟩ ((hRiff ⟨z, hz⟩ ⟨v, hv.1⟩).mp hv.2))
    obtain ⟨b, hb, hmem⟩ := hrepl ψ e X.val X.property hfun
    refine ⟨⟨b, hb⟩, ?_⟩
    intro y
    change y.val ∈ b ↔ ∃ x : ClassDomain (classOf H a), x.val ∈ X.val ∧ ψ.Eval ![x, y] e
    rw [hmem y.val]
    constructor
    · rintro ⟨-, x, hx, hxy⟩
      let u : ClassDomain (classOf H a) := ⟨x, htrans _ X.property x hx⟩
      exact ⟨u, hx, (hRiff u y).mp hxy⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨y.property, x.val, hx, (hRiff x y).mpr hxy⟩

end

end ZFVP
