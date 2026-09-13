import ZFVP.ModelTheory.ForcingNameNormalization

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def forcingConditionalNameFormula : SetTheorySemisentence 6 :=
  f“N P R o W t. ∀ z, z ∈ N ↔ z ∈ !prod.dfn (!domain.dfn (!sUnion.dfn W)) P ∧
    ∃ s ∈ W, ∃ p ∈ P, !kpair.dfn (!kpair.π₁.dfn z) p ∈ s ∧
      !kpair.dfn (!kpair.π₂.dfn z) p ∈ R ∧
        !kpair.π₂.dfn z ∈ !atomicEqualityFormula P R t (!checkNameFormula o s)”

/-- Evaluate the ground name selected by another name. Conditions are refined
both below the selected subname condition and into the selection decision. -/
noncomputable def forcingConditionalName (P R one W τ : V) : V :=
  {z ∈ domain (⋃ˢ W) ×ˢ P ; ∃ σ ∈ W, ∃ p ∈ P,
    ⟨kpair.π₁ z, p⟩ₖ ∈ σ ∧ ⟨kpair.π₂ z, p⟩ₖ ∈ R ∧
      kpair.π₂ z ∈ atomicEquality P R τ (checkName one σ)}

instance forcingConditionalNameFormula_defined :
    Defined (fun v : Fin 6 → V ↦ v 0 = forcingConditionalName (v 1) (v 2) (v 3) (v 4) (v 5))
      forcingConditionalNameFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [forcingConditionalNameFormula, forcingConditionalName]⟩

instance forcingConditionalName_definable : Language.DefinableFunction₅ ℒₛₑₜ (forcingConditionalName (V := V)) :=
  forcingConditionalNameFormula_defined.to_definable

theorem pair_mem_forcingConditionalName (P R one W τ ν r : V) :
    ⟨ν, r⟩ₖ ∈ forcingConditionalName P R one W τ ↔
      r ∈ P ∧ ∃ σ ∈ W, ∃ p ∈ P, ⟨ν, p⟩ₖ ∈ σ ∧ ⟨r, p⟩ₖ ∈ R ∧
        r ∈ atomicEquality P R τ (checkName one σ) := by
  simp only [forcingConditionalName, mem_sep_iff, kpair_mem_iff,
    kpair.π₁_kpair, kpair.π₂_kpair]
  constructor
  · exact fun h ↦ ⟨h.1.2, h.2⟩
  · rintro ⟨hr, σ, hσ, p, hp, hpair, hle, he⟩
    exact ⟨⟨mem_domain_of_kpair_mem (mem_sUnion_iff.mpr ⟨σ, hσ, hpair⟩), hr⟩,
      σ, hσ, p, hp, hpair, hle, he⟩

theorem forcingConditionalName_isName {P R one W τ : V}
    (hW : ∀ σ ∈ W, IsForcingName P σ) :
    IsForcingName P (forcingConditionalName P R one W τ) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨ν, _, r, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  obtain ⟨hr, σ, hσ, p, _, hp, _, _⟩ := (pair_mem_forcingConditionalName _ _ _ _ _ _ _).mp hz
  exact ⟨ν, r, hr, rfl, forcingName_subname (hW σ hσ) hp⟩

theorem forcingConditionalName_empty {P R one W τ : V}
    (hW : ∀ σ ∈ W, σ = ∅) : forcingConditionalName P R one W τ = ∅ := by
  apply subset_empty_iff_eq_empty.mp
  intro z hz
  obtain ⟨ν, _, r, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  obtain ⟨_, σ, hσ, p, _, hp, _, _⟩ := (pair_mem_forcingConditionalName _ _ _ _ _ _ _).mp hz
  exact False.elim (not_mem_empty (hW σ hσ ▸ hp))

namespace ForcingContext

theorem conditionalName_value (A : ForcingContext V) (W : V)
    (hW : ∀ σ ∈ W, IsForcingName A.P σ) (τ : ForcingName A.P)
    {σ : ForcingName A.P} (hσ : σ.val ∈ W) (hsel : A.ofName τ = A.check σ.val) :
    A.ofName ⟨forcingConditionalName A.P A.R A.one W τ.val,
      forcingConditionalName_isName hW⟩ = A.ofName σ := by
  apply mem_ext
  intro x
  rw [A.mem_ofName_iff, A.mem_ofName_iff]
  constructor
  · rintro ⟨ν, r, hrG, hpair, he⟩
    obtain ⟨_, υ, hυ, p, hp, hνp, hrp, hdec⟩ :=
      (pair_mem_forcingConditionalName _ _ _ _ _ _ _).mp hpair
    have heυ : A.ofName τ = A.check υ :=
      (forcingQuotientMk_eq_iff A.P A.R A.G A.order A.generic.1
        τ ⟨checkName A.one υ, checkName_isName A.top.1 υ⟩).mpr ⟨r, hrG, hdec⟩
    have hυσ : υ = σ.val := (A.check_eq_iff _ _).mp (heυ.symm.trans hsel)
    exact ⟨ν, p, A.generic.1.2.2.1 r hrG p hp hrp, hυσ ▸ hνp, he⟩
  · rintro ⟨ν, p, hpG, hνp, he⟩
    obtain ⟨q, hqG, hdec⟩ := (forcingQuotientMk_eq_iff A.P A.R A.G A.order A.generic.1
      τ ⟨checkName A.one σ.val, checkName_isName A.top.1 σ.val⟩).mp hsel
    obtain ⟨r, hrG, hrp, hrq⟩ := A.generic.1.2.2.2 p hpG q hqG
    exact ⟨ν, r, hrG, (pair_mem_forcingConditionalName _ _ _ _ _ _ _).mpr
      ⟨A.generic.1.1 r hrG, σ.val, hσ, p, A.generic.1.1 p hpG, hνp, hrp,
        atomicEquality_mono A.order hdec (A.generic.1.1 r hrG) hrq⟩, he⟩

end ForcingContext

/-- A conditional evaluation can be replaced by one bounded name, uniformly
over all selections whose evaluated result lies below the cutoff. -/
theorem small_forcing_conditionalName_normalization {P R one δ W : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (hW : ∀ σ ∈ W, IsForcingName P σ) (τ : ForcingName P) :
    ∃ ν ∈ forcingNameHierarchy P δ, ∃ hν : IsForcingName P ν,
      ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G),
        let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
        ∀ σ : ForcingName P, σ.val ∈ W → A.ofName τ = A.check σ.val →
          A.ofName σ ∈ hierarchy (A.check δ) → A.ofName ⟨ν, hν⟩ = A.ofName σ := by
  let μ : ForcingName P := ⟨forcingConditionalName P R one W τ.val,
    forcingConditionalName_isName hW⟩
  obtain ⟨ν, hνδ, hν, hv⟩ := small_forcing_name_normalization hR ht hδ hP μ
  refine ⟨ν, hνδ, hν, ?_⟩
  intro G hG A σ hσ hs hr
  have he : A.ofName μ = A.ofName σ := A.conditionalName_value W hW τ hσ hs
  exact (hv G hG (he.symm ▸ hr)).trans he

end ZFVP
