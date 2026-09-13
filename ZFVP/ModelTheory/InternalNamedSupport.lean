import ZFVP.ModelTheory.InternalNamedFiniteRealization
import ZFVP.SetTheory.FiniteSetUnions
import ZFVP.Syntax.MembershipSwap

/-! Actual finite name supports and replacement of an unused name's value. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

noncomputable def namedFormulaSupport (p : V) : V := range (kpair.π₂ p)

instance namedFormulaSupport_definable : ℒₛₑₜ-function₁[V] namedFormulaSupport := by
  unfold namedFormulaSupport
  definability

noncomputable def namedTheorySupport (B : V) : V := ⋃ˢ repl namedFormulaSupport (by definability) B

theorem mem_namedTheorySupport (B x : V) : x ∈ namedTheorySupport B ↔ ∃ p ∈ B, x ∈ namedFormulaSupport p := by
  simp only [namedTheorySupport, mem_sUnion_iff, repl_spec]
  constructor
  · rintro ⟨S, ⟨p, hp, rfl⟩, hx⟩
    exact ⟨p, hp, hx⟩
  · rintro ⟨p, hp, hx⟩
    exact ⟨namedFormulaSupport p, ⟨p, hp, rfl⟩, hx⟩

instance namedTheorySupport_definable : ℒₛₑₜ-function₁[V] namedTheorySupport := by
  have h : ℒₛₑₜ-relation[V] (fun S B ↦ ∀ x, x ∈ S ↔ ∃ p ∈ B, x ∈ namedFormulaSupport p) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [mem_namedTheorySupport]
  rfl

theorem namedFormulaSupport_subset {L A p : V} (hL : IsLanguageCode L) (hp : p ∈ namedFormulaSet L A) :
    namedFormulaSupport p ⊆ A := by
  obtain ⟨n, _, φ, _, b, hb, rfl⟩ := namedFormulaSet_cases hL hp
  simpa only [namedFormulaSupport, kpair.π₂_kpair] using range_subset_of_mem_function hb

theorem namedFormulaSupport_finite {L A p : V} (hL : IsLanguageCode L) (hp : p ∈ namedFormulaSet L A) :
    IsInternallyFinite (namedFormulaSupport p) := by
  obtain ⟨n, hn, φ, _, b, hb, rfl⟩ := namedFormulaSet_cases hL hp
  have : IsFunction b := IsFunction.of_mem hb
  have hfin : IsInternallyFinite (domain b) := by
    rw [domain_eq_of_mem_function hb]
    exact ⟨n, hn, CardEQ.refl n⟩
  simpa only [namedFormulaSupport, kpair.π₂_kpair] using internallyFinite_range (internallyFinite_function hfin)

theorem namedTheorySupport_finite {L A B : V} (hL : IsLanguageCode L)
    (hB : B ⊆ namedFormulaSet L A) (hfin : IsInternallyFinite B) :
    IsInternallyFinite (namedTheorySupport B) := by
  apply internallyFinite_sUnion (internallyFinite_repl _ _ hfin)
  intro S hS
  obtain ⟨p, hp, rfl⟩ := (repl_spec _).mp hS
  exact namedFormulaSupport_finite hL (hB p hp)

theorem namedTheorySupport_subset {L A B : V} (hL : IsLanguageCode L) (hB : B ⊆ namedFormulaSet L A) :
    namedTheorySupport B ⊆ A := by
  intro x hx
  obtain ⟨p, hp, hx⟩ := (mem_namedTheorySupport B x).mp hx
  exact namedFormulaSupport_subset hL (hB p hp) x hx

theorem namedHolds_of_agree_on_support {L M A f g p : V} (hL : IsLanguageCode L)
    (hf : f ∈ structureDomain M ^ A) (hg : g ∈ structureDomain M ^ A)
    (hp : p ∈ namedFormulaSet L A) (he : ∀ x ∈ namedFormulaSupport p, f ‘ x = g ‘ x) :
    NamedHolds L M f p ↔ NamedHolds L M g p := by
  obtain ⟨n, _, φ, _, b, hb, rfl⟩ := namedFormulaSet_cases hL hp
  have hc : compose b f = compose b g := by
    apply function_eq_of_values (compose_function hb hf) (compose_function hb hg)
    intro i hi
    rw [value_compose_of_mem_function hb hf hi, value_compose_of_mem_function hb hg hi]
    apply he
    simpa only [namedFormulaSupport, kpair.π₂_kpair] using value_mem_range hb hi
  simp only [namedHolds_pair, hc]

noncomputable def nameAssignmentUpdateValue (f k x i : V) : V := by
  classical
  exact if i = k then x else f ‘ i

instance nameAssignmentUpdateValue_definable : ℒₛₑₜ-function₄[V] nameAssignmentUpdateValue := by
  have h : Language.Definable ℒₛₑₜ (fun v : Fin 5 → V ↦
      (v 4 = v 2 ∧ v 0 = v 3) ∨ (v 4 ≠ v 2 ∧ v 0 = (v 1) ‘ (v 4))) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = nameAssignmentUpdateValue (v 1) (v 2) (v 3) (v 4) ↔ _
  unfold nameAssignmentUpdateValue
  split <;> simp_all

noncomputable def nameAssignmentUpdate (f k x : V) : V :=
  definableGraph (ω : V) (nameAssignmentUpdateValue f k x) (by definability)

instance nameAssignmentUpdate_definable : ℒₛₑₜ-function₃[V] nameAssignmentUpdate := by
  have h : ℒₛₑₜ-relation₄[V] (fun g f k x ↦ ∀ p, p ∈ g ↔
      ∃ i ∈ (ω : V), p = ⟨i, nameAssignmentUpdateValue f k x i⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [nameAssignmentUpdate, mem_definableGraph_iff]
  rfl

theorem nameAssignmentUpdate_value (f k x : V) {i : V} (hi : i ∈ (ω : V)) :
    (nameAssignmentUpdate f k x) ‘ i = nameAssignmentUpdateValue f k x i := value_definableGraph _ _ _ hi

theorem nameAssignmentUpdate_at (f x : V) {k : V} (hk : k ∈ (ω : V)) :
    (nameAssignmentUpdate f k x) ‘ k = x := by
  rw [nameAssignmentUpdate_value _ _ _ hk]
  simp only [nameAssignmentUpdateValue, ite_true]

theorem nameAssignmentUpdate_other (f k x : V) {i : V} (hi : i ∈ (ω : V)) (hik : i ≠ k) :
    (nameAssignmentUpdate f k x) ‘ i = f ‘ i := by
  rw [nameAssignmentUpdate_value _ _ _ hi]
  simp only [nameAssignmentUpdateValue, ite_eq_right_iff, hik, false_implies]

theorem nameAssignmentUpdate_mem {D f k x : V} (hf : f ∈ D ^ (ω : V)) (hx : x ∈ D) :
    nameAssignmentUpdate f k x ∈ D ^ (ω : V) := by
  apply definableGraph_mem_function_of_mapsTo
  intro i hi
  unfold nameAssignmentUpdateValue
  split
  · exact hx
  · exact function_value_mem hf hi

theorem SourceNaming.update {M j f k x : V} (hf : SourceNaming M j f)
    (hj : j ∈ (ω : V) ^ structureDomain M) (hk : k ∉ range j) (hx : x ∈ structureDomain M) :
    SourceNaming M j (nameAssignmentUpdate f k x) := by
  refine ⟨nameAssignmentUpdate_mem hf.1 hx, fun a ha ↦ ?_⟩
  have hne : j ‘ a ≠ k := fun he ↦ hk (he ▸ value_mem_range hj ha)
  rw [nameAssignmentUpdate_other f k x (function_value_mem hj ha) hne]
  exact hf.2 a ha

theorem compose_nameAssignmentUpdate_fresh {D f n b k x : V}
    (hf : f ∈ D ^ (ω : V)) (hb : b ∈ (ω : V) ^ n) (hx : x ∈ D) (hk : k ∉ range b) :
    compose b (nameAssignmentUpdate f k x) = compose b f := by
  have hg := nameAssignmentUpdate_mem (k := k) hf hx
  apply function_eq_of_values (compose_function hb hg) (compose_function hb hf)
  intro i hi
  rw [value_compose_of_mem_function hb hg hi, value_compose_of_mem_function hb hf hi]
  exact nameAssignmentUpdate_other _ _ _ (function_value_mem hb hi)
    (fun he ↦ hk (he ▸ value_mem_range hb hi))

theorem namedHolds_update_fresh {L M f p k x : V} (hL : IsLanguageCode L)
    (hf : f ∈ structureDomain M ^ (ω : V)) (hp : p ∈ namedFormulaSet L (ω : V))
    (hx : x ∈ structureDomain M) (hk : k ∉ namedFormulaSupport p) :
    NamedHolds L M (nameAssignmentUpdate f k x) p ↔ NamedHolds L M f p := by
  obtain ⟨n, _, φ, _, b, hb, rfl⟩ := namedFormulaSet_cases hL hp
  have hk' : k ∉ range b := by simpa only [namedFormulaSupport, kpair.π₂_kpair] using hk
  simp only [namedHolds_pair, compose_nameAssignmentUpdate_fresh hf hb hx hk']

end ZFVP
