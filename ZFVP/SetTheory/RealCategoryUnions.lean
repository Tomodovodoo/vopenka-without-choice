import ZFVP.SetTheory.RealCategoryClosure
import ZFVP.SetTheory.CountableUnions
import ZFVP.SetTheory.InjectionRetraction

/-! Internal countable unions of real opens and coded meagre covers. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def realSequenceUnion (f : V) : V :=
  {x ∈ dedekindReals V ; ∃ n ∈ (ω : V), x ∈ f ‘ n}

theorem mem_realSequenceUnion_iff (f x : V) : x ∈ realSequenceUnion f ↔
    IsDedekindCut x ∧ ∃ n ∈ (ω : V), x ∈ f ‘ n := by
  simp [realSequenceUnion, mem_dedekindReals_iff]

instance realSequenceUnion_definable : ℒₛₑₜ-function₁[V] realSequenceUnion := by
  have h : ℒₛₑₜ-relation (fun U f : V ↦ ∀ x, x ∈ U ↔
      IsDedekindCut x ∧ ∃ n ∈ (ω : V), x ∈ f ‘ n) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [mem_realSequenceUnion_iff]

theorem realSequenceUnion_isOpen {f : V} (hf : ∀ n ∈ (ω : V), IsRealOpen (f ‘ n)) :
    IsRealOpen (realSequenceUnion f) := by
  apply realOpen_of_neighborhoods
  intro x hx
  obtain ⟨_, n, hn, hxn⟩ := (mem_realSequenceUnion_iff _ _).mp hx
  obtain ⟨a, ha, b, hb, hab, hxi, hsub⟩ := realOpen_neighborhood (hf n hn) hxn
  refine ⟨a, ha, b, hb, hab, hxi, ?_⟩
  intro y hy
  exact (mem_realSequenceUnion_iff _ _).mpr
    ⟨((mem_realInterval_iff _ _ _).mp hy).1, n, hn, hsub y hy⟩

theorem realMeagre_of_double_cover {A f : V}
    (hf : ∀ n ∈ (ω : V), ∀ k ∈ (ω : V), (f ‘ n) ‘ k ⊆ realBasicCodes V)
    (hnd : ∀ n ∈ (ω : V), ∀ k ∈ (ω : V),
      IsRealNowhereDense (realClosedFrom ((f ‘ n) ‘ k)))
    (hcover : ∀ x ∈ A, ∃ n ∈ (ω : V), ∃ k ∈ (ω : V),
      x ∈ realClosedFrom ((f ‘ n) ‘ k)) : IsRealMeagre A := by
  obtain ⟨e, he, her⟩ := surjection_of_injection (omega_prod_cardLE_omega (V := V))
    (show IsNonempty ((ω : V) ×ˢ (ω : V)) from ⟨⟨0, 0⟩ₖ, by simp⟩)
  have : IsFunction e := IsFunction.of_mem he
  let F : V → V := fun j ↦ (f ‘ (kpair.π₁ (e ‘ j))) ‘ (kpair.π₂ (e ‘ j))
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  have hpair : ∀ j ∈ (ω : V), kpair.π₁ (e ‘ j) ∈ (ω : V) ∧ kpair.π₂ (e ‘ j) ∈ (ω : V) := by
    intro j hj
    obtain ⟨n, hn, k, hk, heq⟩ := mem_prod_iff.mp (function_value_mem he hj)
    rw [heq]
    simpa using And.intro hn hk
  refine ⟨definableGraph (ω : V) F hF,
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun j hj ↦
      mem_power_iff.mpr (hf _ (hpair j hj).1 _ (hpair j hj).2)), ?_, ?_⟩
  · intro j hj
    rw [value_definableGraph _ _ _ hj]
    exact hnd _ (hpair j hj).1 _ (hpair j hj).2
  · intro x hx
    obtain ⟨n, hn, k, hk, hxnk⟩ := hcover x hx
    have hnk : (⟨n, k⟩ₖ : V) ∈ range e := by rw [her]; simpa using And.intro hn hk
    obtain ⟨j, hj⟩ := mem_range_iff.mp hnk
    have hjw : j ∈ (ω : V) := domain_eq_of_mem_function he ▸ mem_domain_of_kpair_mem hj
    refine ⟨j, hjw, ?_⟩
    rw [value_definableGraph _ _ _ hjw]
    simpa only [F, value_eq_of_kpair_mem hj, kpair.π₁_kpair, kpair.π₂_kpair] using hxnk

def IsRealBPWitness (A p : V) : Prop :=
  IsRealOpen (kpair.π₁ p) ∧ kpair.π₂ p ∈ (℘ (realBasicCodes V)) ^ (ω : V) ∧
    (∀ k ∈ (ω : V), IsRealNowhereDense (realClosedFrom ((kpair.π₂ p) ‘ k))) ∧
    ∀ x ∈ ((A \ kpair.π₁ p) ∪ (kpair.π₁ p \ A)),
      ∃ k ∈ (ω : V), x ∈ realClosedFrom ((kpair.π₂ p) ‘ k)

instance isRealBPWitness_definable : ℒₛₑₜ-relation[V] IsRealBPWitness := by
  unfold IsRealBPWitness
  definability

theorem realBP_witness_family (hCC : InternalCountableChoice V) {A : V}
    (hA : ∀ n ∈ (ω : V), RealBaireProperty (A ‘ n)) :
    ∃ g, ∀ n ∈ (ω : V), IsRealBPWitness (A ‘ n) (g ‘ n) := by
  let D := (℘ (dedekindReals V)) ×ˢ ((℘ (realBasicCodes V)) ^ (ω : V))
  let W : V → V := fun n ↦ {p ∈ D ; IsRealBPWitness (A ‘ n) p}
  have hW : ℒₛₑₜ-function₁ W := by
    have h : ℒₛₑₜ-relation (fun S n : V ↦ ∀ p, p ∈ S ↔ p ∈ D ∧ IsRealBPWitness (A ‘ n) p) := by
      definability
    apply Language.Definable.of_iff h
    intro v
    rw [mem_ext_iff]
    simp [W]
  let w := definableGraph (ω : V) W hW
  have hw : ∀ n ∈ (ω : V), IsNonempty (w ‘ n) := by
    intro n hn
    obtain ⟨U, hU, f, hf, hfnd, hfcover⟩ := hA n hn
    have hUR : U ⊆ dedekindReals V := by
      obtain ⟨S, _, rfl⟩ := hU
      exact realOpenFrom_subset_reals S
    refine ⟨⟨U, f⟩ₖ, ?_⟩
    rw [value_definableGraph _ _ _ hn]
    apply mem_sep_iff.mpr
    constructor
    · exact kpair_mem_iff.mpr ⟨mem_power_iff.mpr hUR, hf⟩
    · simpa only [IsRealBPWitness, kpair.π₁_kpair, kpair.π₂_kpair] using
        And.intro hU (And.intro hf (And.intro hfnd hfcover))
  obtain ⟨g, _, hg⟩ := hCC w (definableGraph_isFunction _ _ _) (domain_definableGraph _ _ _) hw
  refine ⟨g, fun n hn ↦ ?_⟩
  have h := hg n hn
  rw [value_definableGraph _ _ _ hn] at h
  exact (mem_sep_iff.mp h).2

theorem realSequenceUnion_baireProperty (hCC : InternalCountableChoice V) {A : V}
    (hA : ∀ n ∈ (ω : V), RealBaireProperty (A ‘ n)) :
    RealBaireProperty (realSequenceUnion A) := by
  obtain ⟨g, hg⟩ := realBP_witness_family hCC hA
  let U := definableGraph (ω : V) (fun n ↦ kpair.π₁ (g ‘ n)) (by definability)
  let f := definableGraph (ω : V) (fun n ↦ kpair.π₂ (g ‘ n)) (by definability)
  have hU : ∀ n ∈ (ω : V), U ‘ n = kpair.π₁ (g ‘ n) := fun n hn ↦ value_definableGraph _ _ _ hn
  have hf : ∀ n ∈ (ω : V), f ‘ n = kpair.π₂ (g ‘ n) := fun n hn ↦ value_definableGraph _ _ _ hn
  refine ⟨realSequenceUnion U, realSequenceUnion_isOpen (fun n hn ↦ by
    rw [hU n hn]; exact (hg n hn).1), realMeagre_of_double_cover (f := f) ?_ ?_ ?_⟩
  · intro n hn k hk
    rw [hf n hn]
    exact mem_power_iff.mp (function_value_mem (hg n hn).2.1 hk)
  · intro n hn k hk
    rw [hf n hn]
    exact (hg n hn).2.2.1 k hk
  · intro x hx
    rcases mem_union_iff.mp hx with hxA | hxU
    · obtain ⟨hxA, hxU⟩ := mem_sdiff_iff.mp hxA
      obtain ⟨hxcut, n, hn, hxn⟩ := (mem_realSequenceUnion_iff _ _).mp hxA
      have hxnot : x ∉ kpair.π₁ (g ‘ n) := by
        intro h
        exact hxU ((mem_realSequenceUnion_iff _ _).mpr ⟨hxcut, n, hn, by rwa [hU n hn]⟩)
      obtain ⟨k, hk, hxk⟩ := (hg n hn).2.2.2 x
        (mem_union_iff.mpr (Or.inl (mem_sdiff_iff.mpr ⟨hxn, hxnot⟩)))
      exact ⟨n, hn, k, hk, by rwa [hf n hn]⟩
    · obtain ⟨hxU, hxA⟩ := mem_sdiff_iff.mp hxU
      obtain ⟨hxcut, n, hn, hxn⟩ := (mem_realSequenceUnion_iff _ _).mp hxU
      have hxnot : x ∉ A ‘ n := fun h ↦ hxA
        ((mem_realSequenceUnion_iff _ _).mpr ⟨hxcut, n, hn, h⟩)
      rw [hU n hn] at hxn
      obtain ⟨k, hk, hxk⟩ := (hg n hn).2.2.2 x
        (mem_union_iff.mpr (Or.inr (mem_sdiff_iff.mpr ⟨hxn, hxnot⟩)))
      exact ⟨n, hn, k, hk, by rwa [hf n hn]⟩

end ZFVP
