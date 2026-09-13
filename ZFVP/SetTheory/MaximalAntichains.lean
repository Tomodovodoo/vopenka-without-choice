import ZFVP.SetTheory.OrdinalAddition
import ZFVP.SetTheory.ForcingOrder
import ZFVP.SetTheory.WellOrderedCardinal
import ZFVP.SetTheory.FunctionValue

/-! Maximal antichains inside a well-orderable subset of a forcing poset, built by transfinite
recursion along an injection of the subset into an ordinal: at each stage the element with that
index is added when it is incompatible with everything added earlier. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsForcingAntichain (P R A : V) : Prop :=
  A ⊆ P ∧ ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ForcingCompatible P R a b

instance isForcingAntichain_definable : ℒₛₑₜ-relation₃[V] IsForcingAntichain := by
  unfold IsForcingAntichain
  definability

def IsMaximalAntichainIn (P R D A : V) : Prop :=
  IsForcingAntichain P R A ∧ A ⊆ D ∧ ∀ d ∈ D, ∃ a ∈ A, ForcingCompatible P R a d

/-- One recursion step: the earlier stages together with the element of the current index
when it is incompatible with all earlier elements. -/
noncomputable def antichainStep (P R D e f : V) : V :=
  (⋃ˢ range f) ∪ {d ∈ D ; e ‘ d = domain f ∧ ∀ a ∈ ⋃ˢ range f, ¬ForcingCompatible P R a d}

theorem mem_antichainStep_iff (P R D e f d : V) :
    d ∈ antichainStep P R D e f ↔ d ∈ ⋃ˢ range f ∨
      (d ∈ D ∧ e ‘ d = domain f ∧ ∀ a ∈ ⋃ˢ range f, ¬ForcingCompatible P R a d) := by
  unfold antichainStep
  rw [mem_union_iff, mem_sep_iff]

instance antichainStep_definable (P R D e : V) : ℒₛₑₜ-function₁[V] (antichainStep P R D e) := by
  have hd : ℒₛₑₜ-relation[V] (fun S f ↦ ∀ d, d ∈ S ↔ d ∈ ⋃ˢ range f ∨
    (d ∈ D ∧ e ‘ d = domain f ∧ ∀ a ∈ ⋃ˢ range f, ¬ForcingCompatible P R a d)) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = antichainStep P R D e (v 1) ↔ _
  rw [mem_ext_iff]
  exact ⟨fun h d ↦ (h d).trans (mem_antichainStep_iff P R D e (v 1) d),
    fun h d ↦ (h d).trans (mem_antichainStep_iff P R D e (v 1) d).symm⟩

noncomputable def antichainStage (P R D e ξ : V) : V :=
  Replacement.transfiniteRec (antichainStep P R D e) (antichainStep_definable P R D e) ξ

instance antichainStage_definable (P R D e : V) : ℒₛₑₜ-function₁[V] (antichainStage P R D e) :=
  Replacement.transfiniteRec_definable (antichainStep_definable P R D e)

theorem domain_pairGraph (F : V → V) (hF : ℒₛₑₜ-function₁ (fun β ↦ ⟨β, F β⟩ₖ)) (ξ : V) :
    domain (repl (fun β ↦ ⟨β, F β⟩ₖ) hF ξ) = ξ := by
  ext x
  rw [mem_domain_iff]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨β, hβ, he⟩ := (repl_spec hF).mp hy
    obtain ⟨rfl, _⟩ := kpair_iff.mp he
    exact hβ
  · intro hx
    exact ⟨F x, (repl_spec hF).mpr ⟨x, hx, rfl⟩⟩

theorem mem_sUnion_range_pairGraph_iff (F : V → V) (hF : ℒₛₑₜ-function₁ (fun β ↦ ⟨β, F β⟩ₖ))
    (ξ d : V) : d ∈ ⋃ˢ range (repl (fun β ↦ ⟨β, F β⟩ₖ) hF ξ) ↔ ∃ β ∈ ξ, d ∈ F β := by
  rw [mem_sUnion_iff]
  constructor
  · rintro ⟨y, hy, hd⟩
    obtain ⟨x, hxy⟩ := mem_range_iff.mp hy
    obtain ⟨β, hβ, he⟩ := (repl_spec hF).mp hxy
    obtain ⟨_, h2⟩ := kpair_iff.mp he
    exact ⟨β, hβ, h2 ▸ hd⟩
  · rintro ⟨β, hβ, hd⟩
    exact ⟨F β, mem_range_of_kpair_mem ((repl_spec hF).mpr ⟨β, hβ, rfl⟩), hd⟩

variable {P R D e : V}

theorem mem_antichainStage_iff (ξ : V) [IsOrdinal ξ] (d : V) :
    d ∈ antichainStage P R D e ξ ↔ (∃ β ∈ ξ, d ∈ antichainStage P R D e β) ∨
      (d ∈ D ∧ e ‘ d = ξ ∧ ∀ β ∈ ξ, ∀ a ∈ antichainStage P R D e β, ¬ForcingCompatible P R a d) := by
  have hspec := Replacement.transfiniteRec_spec (antichainStep P R D e) (antichainStep_definable P R D e)
    (IsOrdinal.toOrdinal ξ)
  change antichainStage P R D e ξ = antichainStep P R D e _ at hspec
  rw [hspec, mem_antichainStep_iff, domain_pairGraph, mem_sUnion_range_pairGraph_iff]
  constructor
  · rintro (h | ⟨hD, he, hall⟩)
    · exact Or.inl h
    · refine Or.inr ⟨hD, he, fun β hβ a ha ↦ hall a ?_⟩
      exact (mem_sUnion_range_pairGraph_iff _ _ ξ a).mpr ⟨β, hβ, ha⟩
  · rintro (h | ⟨hD, he, hall⟩)
    · exact Or.inl h
    · refine Or.inr ⟨hD, he, fun a ha ↦ ?_⟩
      obtain ⟨β, hβ, ha⟩ := (mem_sUnion_range_pairGraph_iff _ _ ξ a).mp ha
      exact hall β hβ a ha

theorem antichainStage_mono {β ξ : V} [IsOrdinal ξ] (hβ : β ∈ ξ) :
    antichainStage P R D e β ⊆ antichainStage P R D e ξ := fun d hd ↦
  (mem_antichainStage_iff ξ d).mpr (Or.inl ⟨β, hβ, hd⟩)

theorem antichainStage_subset (ξ : V) [IsOrdinal ξ] : antichainStage P R D e ξ ⊆ D := by
  have key : ∀ α : Ordinal V, antichainStage P R D e (α : V) ⊆ D := by
    apply transfinite_induction (fun ξ ↦ antichainStage P R D e ξ ⊆ D) (by definability)
    intro α ih d hd
    rcases (mem_antichainStage_iff (α : V) d).mp hd with ⟨β, hβ, hd⟩ | ⟨hD, _, _⟩
    · have : IsOrdinal β := IsOrdinal.of_mem hβ
      exact ih (IsOrdinal.toOrdinal β) (Ordinal.lt_def.mpr hβ) d hd
    · exact hD
  exact key (IsOrdinal.toOrdinal ξ)

theorem antichainStage_antichain (hD : D ⊆ P)
    (hinj : ∀ d ∈ D, ∀ d' ∈ D, e ‘ d = e ‘ d' → d = d') (ξ : V) [IsOrdinal ξ] :
    IsForcingAntichain P R (antichainStage P R D e ξ) := by
  have key : ∀ α : Ordinal V, IsForcingAntichain P R (antichainStage P R D e (α : V)) := by
    apply transfinite_induction (fun ξ ↦ IsForcingAntichain P R (antichainStage P R D e ξ))
      (by definability)
    intro α ih
    have hsub : antichainStage P R D e (α : V) ⊆ P := subset_trans (antichainStage_subset (α : V)) hD
    refine ⟨hsub, fun a ha b hb hne ↦ ?_⟩
    have hold : ∀ x y : V, (∃ β ∈ (α : V), x ∈ antichainStage P R D e β) →
        (∃ γ ∈ (α : V), y ∈ antichainStage P R D e γ) → x ≠ y → ¬ForcingCompatible P R x y := by
      rintro x y ⟨β, hβ, hx⟩ ⟨γ, hγ, hy⟩ hxy
      have : IsOrdinal β := IsOrdinal.of_mem hβ
      have : IsOrdinal γ := IsOrdinal.of_mem hγ
      rcases IsOrdinal.subset_or_supset (α := β) (β := γ) with h | h
      · have hx' : x ∈ antichainStage P R D e γ := by
          rcases IsOrdinal.subset_iff.mp h with rfl | h
          · exact hx
          · exact antichainStage_mono h _ hx
        exact (ih (IsOrdinal.toOrdinal γ) (Ordinal.lt_def.mpr hγ)).2 x hx' y hy hxy
      · have hy' : y ∈ antichainStage P R D e β := by
          rcases IsOrdinal.subset_iff.mp h with rfl | h
          · exact hy
          · exact antichainStage_mono h _ hy
        exact (ih (IsOrdinal.toOrdinal β) (Ordinal.lt_def.mpr hβ)).2 x hx y hy' hxy
    rcases (mem_antichainStage_iff (α : V) a).mp ha with ha' | ⟨haD, hea, hall⟩ <;>
      rcases (mem_antichainStage_iff (α : V) b).mp hb with hb' | ⟨hbD, heb, hallb⟩
    · exact hold a b ha' hb' hne
    · obtain ⟨β, hβ, ha''⟩ := ha'
      exact hallb β hβ a ha''
    · obtain ⟨γ, hγ, hb''⟩ := hb'
      intro hc
      exact hall γ hγ b hb'' (forcingCompatible_symm hc)
    · exact (hne (hinj a haD b hbD (hea.trans heb.symm))).elim
  exact key (IsOrdinal.toOrdinal ξ)

theorem antichainStage_maximal (hR : IsForcingPreorder P R) (hD : D ⊆ P) {α : V} [IsOrdinal α]
    (he : ∀ d ∈ D, e ‘ d ∈ α) : ∀ d ∈ D, ∃ a ∈ antichainStage P R D e α, ForcingCompatible P R a d := by
  intro d hd
  have hξ : IsOrdinal (e ‘ d) := IsOrdinal.of_mem (he d hd)
  by_cases hall : ∀ β ∈ e ‘ d, ∀ a ∈ antichainStage P R D e β, ¬ForcingCompatible P R a d
  · have hnew : d ∈ antichainStage P R D e (e ‘ d) :=
      (mem_antichainStage_iff (e ‘ d) d).mpr (Or.inr ⟨hd, rfl, hall⟩)
    exact ⟨d, antichainStage_mono (he d hd) _ hnew, d, hD _ hd, hR.2.1 _ (hD _ hd), hR.2.1 _ (hD _ hd)⟩
  · push Not at hall
    obtain ⟨β, hβ, a, ha, hc⟩ := hall
    have hβα : β ∈ α := IsOrdinal.toIsTransitive.mem_trans hβ (he d hd)
    exact ⟨a, antichainStage_mono hβα _ ha, hc⟩

/-- Every well-orderable subset of a forcing preorder contains a maximal antichain. -/
theorem exists_maximalAntichain (hR : IsForcingPreorder P R) (hD : D ⊆ P)
    (hwo : IsWellOrderable D) : ∃ A, IsMaximalAntichainIn P R D A := by
  obtain ⟨α, hα, e, he, hinj⟩ := (wellOrderable_iff_cardLE_ordinal D).mp hwo
  have := hα
  let := IsFunction.of_mem he
  have hde : domain e = D := domain_eq_of_mem_function he
  have hinj' : ∀ d ∈ D, ∀ d' ∈ D, e ‘ d = e ‘ d' → d = d' := by
    intro d hd d' hd' h
    have h1 : ⟨d, e ‘ d⟩ₖ ∈ e := kpair_value_mem (by rw [hde]; exact hd)
    have h2 : ⟨d', e ‘ d'⟩ₖ ∈ e := kpair_value_mem (by rw [hde]; exact hd')
    rw [h] at h1
    exact hinj d d' _ h1 h2
  refine ⟨antichainStage P R D e α, antichainStage_antichain hD hinj' α, antichainStage_subset α,
    antichainStage_maximal hR hD (fun d hd ↦ function_value_mem he hd)⟩

end ZFVP
