import ZFVP.ModelTheory.SingletonForcingTruth
import ZFVP.ModelTheory.NormalizedPoolRank
import ZFVP.ModelTheory.SaturatedWoodinPrefix
import Mathlib.Tactic.FinCases

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def singletonForcingRealization (u : V) : ForcingRealization (singletonForcingContext u) V where
  ground := ⟨id, Function.injective_id, fun _ _ ↦ Iff.rfl, fun _ y hy ↦ ⟨y, hy, rfl⟩⟩
  genericSet := {u}
  generic_subset := subset_refl _
  generic_mem := fun _ ↦ mem_singleton_iff

theorem singleton_nameValue_mem_iff (u σ τ : V) :
    nameValue {u} σ ∈ nameValue {u} τ ↔
      u ∈ atomicMembership ({u} : V) (({u} : V) ×ˢ {u}) σ τ := by
  have h := (singletonForcingRealization u).nameValue_mem_iff σ τ
  change _ ↔ ∃ p, p = u ∧ p ∈ atomicMembership _ _ σ τ at h
  simpa only [exists_eq_left, singletonForcingRealization, singletonForcingContext, id_eq] using h

theorem singleton_nameValue_eq_iff (u σ τ : V) :
    nameValue {u} σ = nameValue {u} τ ↔
      u ∈ atomicEquality ({u} : V) (({u} : V) ×ˢ {u}) σ τ := by
  have h := (singletonForcingRealization u).nameValue_eq_iff σ τ
  change _ ↔ ∃ p, p = u ∧ p ∈ atomicEquality _ _ σ τ at h
  simpa only [exists_eq_left, singletonForcingRealization, singletonForcingContext, id_eq] using h

theorem singleton_normalizedNamePool_image {u δ U : V}
    (hδ : IsChoicelessInaccessible δ) (hP : ({u} : V) ∈ hierarchy δ)
    (hU : nameValue {u} U ⊆ hierarchy δ) :
    repl (nameValue {u}) (by definability) (normalizedNamePool {u} (({u} : V) ×ˢ {u}) u δ U) =
      nameValue {u} U := by
  apply mem_ext
  intro x
  rw [repl_spec]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact (singleton_nameValue_mem_iff u τ U).mpr (mem_sep_iff.mp hτ).2.2.2
  · intro hx
    have hm : u ∈ atomicMembership ({u} : V) (({u} : V) ×ˢ {u}) (checkName u x) U := by
      apply (singleton_nameValue_mem_iff u _ U).mp
      rwa [nameValue_checkName (mem_singleton_iff.mpr rfl)]
    obtain ⟨τ, hτ, he, _⟩ := normalizedNamePool_check_representative
      (singletonForcing_preorder u) (singletonForcing_top u) hδ hP (hU x hx) hm
    refine ⟨τ, hτ, ?_⟩
    have hv := (singleton_nameValue_eq_iff u τ (checkName u x)).mpr he
    rw [nameValue_checkName (mem_singleton_iff.mpr rfl)] at hv
    exact hv.symm

theorem singleton_saturatedWoodinPrefix_value {u κ δ : V}
    (hδ : IsChoicelessInaccessible δ) (hP : ({u} : V) ∈ hierarchy δ) (hκ : κ ⊆ δ) :
    nameValue {u} (saturatedWoodinPrefixPosetName {u} (({u} : V) ×ˢ {u}) u κ δ) =
      woodinCollapse κ δ := by
  let := hδ.1
  let A := singletonForcingContext u
  let L := singletonForcingRealization u
  let e : A.Model ≃ V := Equiv.ofBijective L.value
    ⟨L.value_injective, fun x ↦ ⟨A.check x, L.value_check x⟩⟩
  have hv := A.saturatedWoodinPosetName_value hδ hP hκ
  have hf : totalWoodinCollapseFormula.Evalb
      ![A.ofName (A.saturatedWoodinPosetName κ δ), A.check κ, A.check δ] := by
    simpa [totalWoodinCollapse_eq] using hv
  have he := eval_membershipIso e L.value_mem_iff totalWoodinCollapseFormula
    ![A.ofName (A.saturatedWoodinPosetName κ δ), A.check κ, A.check δ] Empty.elim
  have hh := he.mp hf
  have hvec : e ∘ ![A.ofName (A.saturatedWoodinPosetName κ δ), A.check κ, A.check δ] =
      ![nameValue {u} (saturatedWoodinPrefixPosetName {u} (({u} : V) ×ˢ {u}) u κ δ), κ, δ] := by
    funext i
    fin_cases i
    · rfl
    · exact L.value_check κ
    · exact L.value_check δ
  have hemp : e ∘ (Empty.elim : Empty → A.Model) = Empty.elim := by
    funext x
    exact Empty.elim x
  rw [hvec, hemp] at hh
  change totalWoodinCollapseFormula.Evalb _ at hh
  simpa [totalWoodinCollapse_eq] using hh

theorem singleton_normalizedWoodinPrefixPool_image {u κ δ : V}
    (hδ : IsChoicelessInaccessible δ) (hP : ({u} : V) ∈ hierarchy δ) (hκ : κ ⊆ δ) :
    repl (nameValue {u}) (by definability)
      (normalizedNamePool {u} (({u} : V) ×ˢ {u}) u δ
        (saturatedWoodinPrefixPosetName {u} (({u} : V) ×ˢ {u}) u κ δ)) = woodinCollapse κ δ := by
  have hv := singleton_saturatedWoodinPrefix_value hδ hP hκ
  rw [singleton_normalizedNamePool_image hδ hP, hv]
  rw [hv]
  exact fun _ hp ↦ woodinCollapse_condition_mem_hierarchy hδ.regular hκ hp

end ZFVP
