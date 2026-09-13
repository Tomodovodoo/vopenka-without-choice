import ZFVP.ModelTheory.ForcingSmallNameValues
import ZFVP.ModelTheory.ForcingSaturatedName
import ZFVP.ModelTheory.ForcingFormulaName
import ZFVP.SetTheory.DeltaOneRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingRankName (P R τ : V) : V :=
  formulaUniqueName P R sigmaOneRankFormula (standardTuple ![τ])

theorem forcingRankName_isName (P R τ : V) : IsForcingName P (forcingRankName P R τ) :=
  formulaUniqueName_isName _ _ _ _

namespace ForcingContext

theorem forcingRankName_value (A : ForcingContext V) (τ : ForcingName A.P) :
    A.ofName ⟨forcingRankName A.P A.R τ.val, forcingRankName_isName _ _ _⟩ =
      rank (A.ofName τ) := by
  have ht (x : A.Model) : sigmaOneRankFormula.Evalb
      (x :> (fun i ↦ A.ofName ((![τ] : Fin 1 → ForcingName A.P) i))) ↔
        x = rank (A.ofName τ) := sigmaOneRankFormula_defined.iff _
  exact A.formulaName_value sigmaOneRankFormula ![τ]
    (fun x y hx hy ↦ ((ht x).mp hx).trans ((ht y).mp hy).symm) ((ht _).mpr rfl)

theorem checked_name_value_bounded (A : ForcingContext V) {δ β : V}
    (τ : ForcingName A.P)
    (hb : ∀ p ∈ A.P, ∀ α ∈ δ,
      p ∈ atomicEquality A.P A.R τ.val (checkName A.one α) → α ∈ β)
    (hτ : A.ofName τ ∈ A.check δ) : A.ofName τ ∈ A.check β := by
  obtain ⟨α, hα, he⟩ := (A.mem_check_iff δ _).mp hτ
  obtain ⟨p, hpG, hp⟩ := (forcingQuotientMk_eq_iff A.P A.R A.G A.order A.generic.1
    τ ⟨checkName A.one α, checkName_isName A.top.1 α⟩).mp he
  rw [he, A.check_mem_iff]
  exact hb p (A.generic.1.1 p hpG) α hα hp

end ForcingContext

/-- One bounded name works in every generic extension in which the original
name has rank below the inaccessible. The bound is chosen in the ground model. -/
theorem small_forcing_name_normalization {P R one δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (τ : ForcingName P) :
    ∃ ν ∈ forcingNameHierarchy P δ, ∃ hν : IsForcingName P ν,
      ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G),
        let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
        A.ofName τ ∈ hierarchy (A.check δ) → A.ofName ⟨ν, hν⟩ = A.ofName τ := by
  let := hδ.1
  obtain ⟨β, hβ, hb⟩ := small_forcing_checked_name_values_bounded hR ht hδ hP
    (forcingRankName P R τ.val)
  let := IsOrdinal.of_mem hβ
  let ν := forcingSaturatedName P R (forcingNameHierarchy P β) τ.val
  have hν : IsForcingName P ν := forcingSaturatedName_isName _ _ _ _
  refine ⟨ν, (mem_forcingNameHierarchy P δ ν).mpr
    ⟨β, hβ, forcingSaturatedName_subset _ _ _ _⟩, hν, ?_⟩
  intro G hG A hτ
  have hr : rank (A.ofName τ) ∈ A.check β := by
    rw [← A.forcingRankName_value τ]
    apply A.checked_name_value_bounded (δ := δ)
      ⟨forcingRankName P R τ.val, forcingRankName_isName _ _ _⟩ hb
    rw [A.forcingRankName_value τ]
    exact (mem_hierarchy_iff_rank_mem _ _).mp hτ
  apply A.saturatedName_value_of_hierarchy β τ
  exact subset_trans (subset_hierarchy_rank _) (hierarchy_mono
    (IsOrdinal.toIsTransitive.transitive _ hr))

end ZFVP
