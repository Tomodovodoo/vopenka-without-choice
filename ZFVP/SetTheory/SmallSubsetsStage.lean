import ZFVP.SetTheory.PiOneInitialOrdinal
import ZFVP.SetTheory.GroundUniqueness
import ZFVP.SetTheory.CodingUniverse
import ZFVP.SetTheory.CnAbsoluteness
import ZFVP.ModelTheory.CodedMembershipEmbedding

/-! # `P_a(t)` inside a rank stage

`smallSubsetsBelow a t` collects the subsets of `t` of size below `a`. This file gives a formula
that pins that set down, shows that a rank stage closed under successor contains it and reads the
formula the same way the ambient universe does, and transports the set along a coded elementary
embedding of two such stages.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- `S` is the set of subsets of `t` that inject into some member of `a`. -/
def smallSubsetsBelowFormula : SetTheorySemisentence 3 :=
  “S a t. ∀ x, x ∈ S ↔ x ⊆ t ∧ ∃ m ∈ a, ∃ g, !boundedInjectionFormula g x m”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_smallSubsetsBelowFormula (S a t : V) :
    smallSubsetsBelowFormula.Evalb ![S, a, t] ↔ S = smallSubsetsBelow a t := by
  simp only [smallSubsetsBelowFormula]
  simp
  constructor
  · intro h
    apply mem_ext
    intro x
    rw [mem_smallSubsetsBelow_iff]
    simpa [USmall, CardLE] using h x
  · rintro rfl x
    rw [mem_smallSubsetsBelow_iff]
    simp [USmall, CardLE]

/-- A rank stage closed under successor contains `P_a t` for its own members. -/
theorem smallSubsetsBelow_mem_hierarchy {δ a t : V} [IsOrdinal δ]
    (hδ : ∀ ξ ∈ δ, succ ξ ∈ δ) (ha : a ∈ hierarchy δ) (ht : t ∈ hierarchy δ) :
    smallSubsetsBelow a t ∈ hierarchy δ := by
  apply subset_mem_hierarchy_limit hδ (power_mem_hierarchy_limit hδ ht)
  intro x hx
  exact mem_power_iff.mpr ((mem_smallSubsetsBelow_iff a t x).mp hx).1

/-- A set of subsets of a member of a successor-closed stage is itself in the stage. -/
theorem subsets_mem_hierarchy {δ K U : V} [IsOrdinal δ] (hδ : ∀ ξ ∈ δ, succ ξ ∈ δ)
    (hK : K ∈ hierarchy δ) (hU : U ⊆ ℘ K) : U ∈ hierarchy δ :=
  subset_mem_hierarchy_limit hδ (power_mem_hierarchy_limit hδ hK) hU

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
/-- Inclusion between members of a transitive set is the real inclusion. -/
theorem setDomain_subset_iff {A : V} (hA : IsTransitive A) (x t : SetDomain A) :
    x ⊆ t ↔ x.val ⊆ t.val := by
  constructor
  · intro h z hz
    exact h (⟨z, hA.mem_trans hz x.property⟩ : SetDomain A) hz
  · intro h z hz
    exact h z.val hz

/-- A stage closed under successor has every injection of one of its members into another,
so the bounded injection formula read there says exactly `x.val ≤# m.val`. -/
theorem exists_injection_stage {δ : V} [IsOrdinal δ] (hδ : ∀ ξ ∈ δ, succ ξ ∈ δ)
    (x m : SetDomain (hierarchy δ)) :
    (∃ g : SetDomain (hierarchy δ), boundedInjectionFormula.Evalb ![g, x, m]) ↔
      x.val ≤# m.val := by
  let := hierarchy_transitive δ
  have habs : ∀ g : SetDomain (hierarchy δ),
      boundedInjectionFormula.Evalb ![g, x, m] ↔ g.val ∈ m.val ^ x.val ∧ Injective g.val := by
    intro g
    have h := bounded_formula_absolute (hierarchy δ) boundedInjectionFormula_bounded ![g, x, m]
    have hv : (fun i ↦ ((![g, x, m] : Fin 3 → SetDomain (hierarchy δ)) i).val)
        = ![g.val, x.val, m.val] := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
        (fun l ↦ Fin.elim0 l) k) j) i
    rw [hv] at h
    simpa using h
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨hf, hinj⟩ := (habs g).mp hg
    exact ⟨g.val, hf, hinj⟩
  · rintro ⟨f, hf, hinj⟩
    have hfmem : f ∈ hierarchy δ := (hierarchy_transitive δ).mem_trans hf
      (function_mem_hierarchy_limit hδ x.property m.property)
    exact ⟨⟨f, hfmem⟩, (habs ⟨f, hfmem⟩).mpr ⟨hf, hinj⟩⟩

/-- What the formula says inside a successor-closed rank stage. -/
theorem eval_smallSubsetsBelowFormula_body {δ : V} [IsOrdinal δ] (hδ : ∀ ξ ∈ δ, succ ξ ∈ δ)
    {S a t : V} (hS : S ∈ hierarchy δ) (ha : a ∈ hierarchy δ) (ht : t ∈ hierarchy δ) :
    smallSubsetsBelowFormula.Evalb
        (![⟨S, hS⟩, ⟨a, ha⟩, ⟨t, ht⟩] : Fin 3 → SetDomain (hierarchy δ)) ↔
      ∀ x ∈ hierarchy δ, (x ∈ S ↔ x ⊆ t ∧ USmall a x) := by
  let := hierarchy_transitive δ
  simp only [smallSubsetsBelowFormula]
  simp [exists_injection_stage hδ, USmall]
  have hsub := setDomain_subset_iff (hierarchy_transitive δ)
  constructor
  · intro h x hx
    have hxs := h ⟨x, hx⟩
    constructor
    · intro hmem
      obtain ⟨hs, μ, hμ, hle⟩ := hxs.mp hmem
      exact ⟨(hsub ⟨x, hx⟩ ⟨t, ht⟩).mp hs, μ.val, hμ, hle⟩
    · rintro ⟨hs, μ, hμ, hle⟩
      exact hxs.mpr ⟨(hsub ⟨x, hx⟩ ⟨t, ht⟩).mpr hs,
        ⟨μ, (hierarchy_transitive δ).mem_trans hμ ha⟩, hμ, hle⟩
  · intro h x
    have hxs := h x.val x.property
    constructor
    · intro hmem
      obtain ⟨hs, μ, hμ, hle⟩ := hxs.mp hmem
      exact ⟨(hsub x ⟨t, ht⟩).mpr hs, ⟨μ, (hierarchy_transitive δ).mem_trans hμ ha⟩, hμ, hle⟩
    · rintro ⟨hs, μ, hμ, hle⟩
      exact hxs.mpr ⟨(hsub x ⟨t, ht⟩).mp hs, μ.val, hμ, hle⟩

/-- Read inside a successor-closed rank stage, the formula still says what it says outside. -/
theorem eval_smallSubsetsBelowFormula_stage {δ : V} [IsOrdinal δ] (hδ : ∀ ξ ∈ δ, succ ξ ∈ δ)
    {S a t : V} (hS : S ∈ hierarchy δ) (ha : a ∈ hierarchy δ) (ht : t ∈ hierarchy δ) :
    smallSubsetsBelowFormula.Evalb
        (![⟨S, hS⟩, ⟨a, ha⟩, ⟨t, ht⟩] : Fin 3 → SetDomain (hierarchy δ)) ↔
      S = smallSubsetsBelow a t := by
  rw [eval_smallSubsetsBelowFormula_body hδ hS ha ht]
  constructor
  · intro h
    apply mem_ext
    intro x
    rw [mem_smallSubsetsBelow_iff]
    constructor
    · intro hx
      exact (h x ((hierarchy_transitive δ).mem_trans hx hS)).mp hx
    · rintro ⟨hxt, hus⟩
      exact (h x (subset_mem_hierarchy_limit hδ ht hxt)).mpr ⟨hxt, hus⟩
  · rintro rfl x _
    rw [mem_smallSubsetsBelow_iff]

/-- A coded elementary embedding of successor-closed rank stages moves `P_a t` to
`P_{e‘a}(e‘t)`. -/
theorem value_smallSubsetsBelow {lb gam e a t : V} [IsOrdinal lb] [IsOrdinal gam]
    (hlb : ∀ ξ ∈ lb, succ ξ ∈ lb) (hgam : ∀ ξ ∈ gam, succ ξ ∈ gam)
    (he : IsCodedMembershipEmbedding (hierarchy lb) (hierarchy gam) e)
    (ha : a ∈ lb) (ht : t ∈ lb) :
    e ‘ (smallSubsetsBelow a t) = smallSubsetsBelow (e ‘ a) (e ‘ t) := by
  have hao : IsOrdinal a := IsOrdinal.of_mem ha
  have hto : IsOrdinal t := IsOrdinal.of_mem ht
  have haV : a ∈ hierarchy lb := ordinal_mem_hierarchy_iff.mpr ha
  have htV : t ∈ hierarchy lb := ordinal_mem_hierarchy_iff.mpr ht
  have hSV : smallSubsetsBelow a t ∈ hierarchy lb := smallSubsetsBelow_mem_hierarchy hlb haV htV
  have haW : e ‘ a ∈ hierarchy gam := function_value_mem he.function haV
  have htW : e ‘ t ∈ hierarchy gam := function_value_mem he.function htV
  have hSW : e ‘ (smallSubsetsBelow a t) ∈ hierarchy gam := function_value_mem he.function hSV
  have hsrc := (eval_smallSubsetsBelowFormula_stage hlb hSV haV htV).mpr rfl
  have htr := (he.eval_semisentence smallSubsetsBelowFormula
    (![⟨smallSubsetsBelow a t, hSV⟩, ⟨a, haV⟩, ⟨t, htV⟩] :
      Fin 3 → SetDomain (hierarchy lb))).mp hsrc
  have hv : he.toFunction ∘ (![⟨smallSubsetsBelow a t, hSV⟩, ⟨a, haV⟩, ⟨t, htV⟩] :
      Fin 3 → SetDomain (hierarchy lb))
      = (![⟨e ‘ (smallSubsetsBelow a t), hSW⟩, ⟨e ‘ a, haW⟩, ⟨e ‘ t, htW⟩] :
        Fin 3 → SetDomain (hierarchy gam)) := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.elim0 l) k) j) i
  rw [hv] at htr
  exact (eval_smallSubsetsBelowFormula_stage hgam hSW haW htW).mp htr

end ZFVP
