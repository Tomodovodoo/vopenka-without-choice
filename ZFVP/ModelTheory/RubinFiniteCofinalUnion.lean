import ZFVP.SetTheory.FiniteSets

/-! Internal finite cofinal unions for the finite-preserving Rubin successor.
The finite index set may have nonstandard size. -/
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (P : V → Prop) (L R : V → V → Prop)
    (hP : ℒₛₑₜ-predicate P) (hL : ℒₛₑₜ-relation L) (hR : ℒₛₑₜ-relation R)
    (hne : ∃ d, P d)
    (hdir : ∀ x y, P x → P y → ∃ z, P z ∧ L x z ∧ L y z)
    (htrans : ∀ x y z, P x → P y → P z → L x y → L y z → L x z)

include hP hL hR hne hdir htrans

/-- Finitely many eventual bounds can be combined inside ZF without Choice. -/
theorem internallyFinite_common_eventual_bound {a : V} (ha : IsInternallyFinite a)
    (hb : ∀ m ∈ a, ∃ d, P d ∧ ∀ e, P e → L d e → ¬R m e) :
    ∃ d, P d ∧ ∀ m ∈ a, ∀ e, P e → L d e → ¬R m e := by
  apply internallyFinite_induction
    (fun a ↦ (∀ m ∈ a, ∃ d, P d ∧ ∀ e, P e → L d e → ¬R m e) →
      ∃ d, P d ∧ ∀ m ∈ a, ∀ e, P e → L d e → ¬R m e)
    (by definability) ?_ ?_ a ha hb
  · intro _
    obtain ⟨d, hd⟩ := hne
    exact ⟨d, hd, fun m hm ↦ False.elim (not_mem_empty hm)⟩
  · intro b m ih hbounds
    obtain ⟨d, hd, hdb⟩ := ih (fun x hx ↦ hbounds x (mem_insert.mpr (Or.inr hx)))
    obtain ⟨c, hc, hcm⟩ := hbounds m (mem_insert.mpr (Or.inl rfl))
    obtain ⟨z, hz, hdz, hcz⟩ := hdir d c hd hc
    refine ⟨z, hz, ?_⟩
    intro x hx e he hze
    rcases mem_insert.mp hx with rfl | hx
    · exact hcm e he (htrans c z e hc hz he hcz hze)
    · exact hdb x hx e he (htrans d z e hd hz he hdz hze)

/-- A cofinal union indexed by an internally finite set has a cofinal fiber. -/
theorem internallyFinite_cofinal_union {a : V} (ha : IsInternallyFinite a)
    (hcof : ∀ d, P d → ∃ e, P e ∧ L d e ∧ ∃ m ∈ a, R m e) :
    ∃ m ∈ a, ∀ d, P d → ∃ e, P e ∧ L d e ∧ R m e := by
  classical
  by_contra hn
  have hb : ∀ m ∈ a, ∃ d, P d ∧ ∀ e, P e → L d e → ¬R m e := by
    intro m hm
    have hh : ¬∀ d, P d → ∃ e, P e ∧ L d e ∧ R m e :=
      fun h ↦ hn ⟨m, hm, h⟩
    push Not at hh
    obtain ⟨d, hd, h⟩ := hh
    exact ⟨d, hd, h⟩
  obtain ⟨d, hd, hbound⟩ := internallyFinite_common_eventual_bound P L R hP hL hR hne hdir htrans ha hb
  obtain ⟨e, he, hde, m, hm, hRme⟩ := hcof d hd
  exact hbound m hm e he hde hRme

end ZFVP
