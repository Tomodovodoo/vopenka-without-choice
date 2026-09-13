import ZFVP.SetTheory.MaximalAntichains
import ZFVP.SetTheory.SchroederBernstein
import ZFVP.SetTheory.InternalChoice

/-! Collapsing systems and `λ`-indexed maximal antichains. A collapsing system for `P` and `λ`
is a sequence of labelled maximal antichains such that every label below `λ` is realised
compatibly with every condition; it witnesses combinatorially that `P` collapses `λ` to `ω`.
Below any condition of a `λ`-splitting poset of size at most `λ`, every dense set contains a
maximal antichain indexed bijectively by `λ` (with choice). -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- `A ‘ n` is a maximal antichain for every `n ∈ ω`, `L` labels its elements by ordinals below
`lam`, and every label is realised compatibly with every condition. -/
structure IsCollapsingSystem (P R lam A L : V) : Prop where
  antichain : ∀ n ∈ (ω : V), IsMaximalAntichainIn P R P (A ‘ n)
  label : ∀ n ∈ (ω : V), ∀ a ∈ A ‘ n, L ‘ ⟨n, a⟩ₖ ∈ lam
  cover : ∀ α ∈ lam, ∀ p ∈ P, ∃ n ∈ (ω : V), ∃ a ∈ A ‘ n, L ‘ ⟨n, a⟩ₖ = α ∧ ForcingCompatible P R a p

/-- Every condition has `lam` pairwise incompatible extensions. -/
def IsSplitting (P R lam : V) : Prop :=
  ∀ p ∈ P, ∃ B, IsForcingAntichain P R B ∧ (∀ b ∈ B, ⟨b, p⟩ₖ ∈ R) ∧ lam ≤# B

/-- The conditions below `p` that lie below some element `a` of the `n`-th antichain and decide
the condition `E ‘ (L ‘ ⟨n, a⟩)` enumerated by the label of `a`. -/
noncomputable def splitDecisionSet (P R A L E n p : V) : V :=
  {r ∈ P ; ⟨r, p⟩ₖ ∈ R ∧ ∃ a ∈ A ‘ n, ⟨r, a⟩ₖ ∈ R ∧
    (⟨r, E ‘ (L ‘ ⟨n, a⟩ₖ)⟩ₖ ∈ R ∨ ¬ForcingCompatible P R r (E ‘ (L ‘ ⟨n, a⟩ₖ)))}

theorem mem_decisionSet_iff (P R A L E n p r : V) :
    r ∈ splitDecisionSet P R A L E n p ↔ r ∈ P ∧ ⟨r, p⟩ₖ ∈ R ∧ ∃ a ∈ A ‘ n, ⟨r, a⟩ₖ ∈ R ∧
      (⟨r, E ‘ (L ‘ ⟨n, a⟩ₖ)⟩ₖ ∈ R ∨ ¬ForcingCompatible P R r (E ‘ (L ‘ ⟨n, a⟩ₖ))) := by
  simp only [splitDecisionSet, mem_sep_iff]

theorem decisionSet_definable (P R A L E : V) :
    ℒₛₑₜ-function₂[V] (fun n p ↦ splitDecisionSet P R A L E n p) := by
  have h : ℒₛₑₜ-relation₃ (fun D n p : V ↦ ∀ r, r ∈ D ↔ r ∈ P ∧ ⟨r, p⟩ₖ ∈ R ∧ ∃ a ∈ A ‘ n, ⟨r, a⟩ₖ ∈ R ∧
      (⟨r, E ‘ (L ‘ ⟨n, a⟩ₖ)⟩ₖ ∈ R ∨ ¬ForcingCompatible P R r (E ‘ (L ‘ ⟨n, a⟩ₖ)))) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = splitDecisionSet P R A L E (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_decisionSet_iff]

theorem decisionSet_subset (P R A L E n p : V) : splitDecisionSet P R A L E n p ⊆ P :=
  fun r hr ↦ ((mem_decisionSet_iff _ _ _ _ _ _ _ _).mp hr).1

theorem decisionSet_below (P R A L E n p : V) {r : V} (hr : r ∈ splitDecisionSet P R A L E n p) :
    ⟨r, p⟩ₖ ∈ R :=
  ((mem_decisionSet_iff _ _ _ _ _ _ _ _).mp hr).2.1

/-- The decision set is dense below `p`. -/
theorem decisionSet_dense {P R lam A L E : V} (hR : IsForcingPreorder P R)
    (hsys : IsCollapsingSystem P R lam A L) (hE : E ∈ P ^ lam) {n p : V} (hn : n ∈ (ω : V))
    (hp : p ∈ P) : ∀ r ∈ P, ⟨r, p⟩ₖ ∈ R → ∃ r' ∈ splitDecisionSet P R A L E n p, ⟨r', r⟩ₖ ∈ R := by
  intro r hr hrp
  obtain ⟨a, ha, r₁, hr₁, hr₁a, hr₁r⟩ := (hsys.antichain n hn).2.2 r hr
  have haP : a ∈ P := (hsys.antichain n hn).1.1 a ha
  have hq : E ‘ (L ‘ ⟨n, a⟩ₖ) ∈ P := function_value_mem hE (hsys.label n hn a ha)
  by_cases hc : ForcingCompatible P R r₁ (E ‘ (L ‘ ⟨n, a⟩ₖ))
  · obtain ⟨r', hr', hr'r₁, hr'q⟩ := hc
    have hr'r : ⟨r', r⟩ₖ ∈ R := hR.2.2 r' hr' r₁ hr₁ r hr hr'r₁ hr₁r
    refine ⟨r', (mem_decisionSet_iff _ _ _ _ _ _ _ _).mpr ⟨hr', hR.2.2 r' hr' r hr p hp hr'r hrp,
      a, ha, hR.2.2 r' hr' r₁ hr₁ a haP hr'r₁ hr₁a, Or.inl hr'q⟩, hr'r⟩
  · refine ⟨r₁, (mem_decisionSet_iff _ _ _ _ _ _ _ _).mpr ⟨hr₁, hR.2.2 r₁ hr₁ r hr p hp hr₁r hrp,
      a, ha, hr₁a, Or.inr hc⟩, hr₁r⟩

theorem incompatibleWithAll_definable (P R B : V) :
    ℒₛₑₜ-predicate[V] (fun d ↦ ∀ b ∈ B, ¬ForcingCompatible P R d b) := by
  definability

/-- Below any condition of a `lam`-splitting poset of size at most `lam`, any set dense below
the condition contains a maximal antichain (below the condition) indexed bijectively by `lam`. -/
theorem exists_indexed_maximalAntichain (hAC : InternalChoice V) {P R lam : V}
    (hR : IsForcingPreorder P R) [IsOrdinal lam] (hP : P ≤# lam) (hsplit : IsSplitting P R lam)
    {p D : V} (hp : p ∈ P) (hD : D ⊆ P)
    (hdense : ∀ r ∈ P, ⟨r, p⟩ₖ ∈ R → ∃ r' ∈ D, ⟨r', r⟩ₖ ∈ R) :
    ∃ f ∈ P ^ lam, Injective f ∧ range f ⊆ D ∧ IsForcingAntichain P R (range f) ∧
      ∀ r ∈ P, ⟨r, p⟩ₖ ∈ R → ∃ α ∈ lam, ForcingCompatible P R (f ‘ α) r := by
  obtain ⟨B, hBanti, hBp, i, hi, hiinj⟩ := hsplit p hp
  have hBP : B ⊆ P := hBanti.1
  -- refine each element of `B` into `D`
  let F : V → V := fun b ↦ {d ∈ D ; ⟨d, b⟩ₖ ∈ R}
  have hF : ℒₛₑₜ-function₁ F := by
    have h : ℒₛₑₜ-relation (fun S b : V ↦ ∀ d, d ∈ S ↔ d ∈ D ∧ ⟨d, b⟩ₖ ∈ R) := by definability
    apply Language.Definable.of_iff h
    intro v
    rw [mem_ext_iff]
    simp [F]
  obtain ⟨g, hgfun, hgdom, hg⟩ := choice_for_definable_family hAC B F hF (by
    intro b hb
    obtain ⟨d, hd, hdb⟩ := hdense b (hBP b hb) (hBp b hb)
    exact ⟨d, mem_sep_iff.mpr ⟨hd, hdb⟩⟩)
  have hgD : ∀ b ∈ B, g ‘ b ∈ D := fun b hb ↦ (mem_sep_iff.mp (hg b hb)).1
  have hgb : ∀ b ∈ B, ⟨g ‘ b, b⟩ₖ ∈ R := fun b hb ↦ (mem_sep_iff.mp (hg b hb)).2
  have hgdef : ℒₛₑₜ-function₁ (fun b : V ↦ g ‘ b) := by definability
  obtain ⟨B', hB'⟩ : ∃ B' : V, ∀ x, x ∈ B' ↔ ∃ b ∈ B, x = g ‘ b :=
    ⟨repl _ hgdef B, fun x ↦ repl_spec hgdef⟩
  have hB'D : B' ⊆ D := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := (hB' x).mp hx
    exact hgD b hb
  have hginj : ∀ b ∈ B, ∀ b' ∈ B, g ‘ b = g ‘ b' → b = b' := by
    intro b hb b' hb' heq
    by_contra hne
    apply hBanti.2 b hb b' hb' hne
    exact ⟨g ‘ b, hD _ (hgD b hb), hgb b hb, heq ▸ hgb b' hb'⟩
  have hB'anti : IsForcingAntichain P R B' := by
    refine ⟨fun x hx ↦ hD x (hB'D x hx), ?_⟩
    intro x hx y hy hne hc
    obtain ⟨b, hb, rfl⟩ := (hB' x).mp hx
    obtain ⟨b', hb', rfl⟩ := (hB' y).mp hy
    have hbb' : b ≠ b' := fun h ↦ hne (h ▸ rfl)
    apply hBanti.2 b hb b' hb' hbb'
    obtain ⟨r, hr, hr1, hr2⟩ := hc
    exact ⟨r, hr, hR.2.2 r hr _ (hD _ (hgD b hb)) b (hBP b hb) hr1 (hgb b hb),
      hR.2.2 r hr _ (hD _ (hgD b' hb')) b' (hBP b' hb') hr2 (hgb b' hb')⟩
  have hlamB' : lam ≤# B' := by
    let G : V → V := fun α ↦ g ‘ (i ‘ α)
    have hG : ℒₛₑₜ-function₁ G := by unfold G; definability
    refine ⟨definableGraph lam G hG, definableGraph_mem_function_of_mapsTo _ _ G hG
      (fun α hα ↦ (hB' _).mpr ⟨i ‘ α, function_value_mem hi hα, rfl⟩), ?_⟩
    intro α β z hα hβ
    obtain ⟨hαl, rfl⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hα
    obtain ⟨hβl, hz⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hβ
    have := hginj _ (function_value_mem hi hαl) _ (function_value_mem hi hβl) hz
    exact injective_value_eq hi hiinj hαl hβl this
  -- complete `B'` to a maximal antichain in `D`
  obtain ⟨D'', hD''⟩ : ∃ D'' : V, ∀ d, d ∈ D'' ↔ d ∈ D ∧ ∀ b ∈ B', ¬ForcingCompatible P R d b :=
    ⟨sep D (fun d ↦ ∀ b ∈ B', ¬ForcingCompatible P R d b) (incompatibleWithAll_definable P R B'),
      fun d ↦ mem_sep_iff⟩
  have hD''P : D'' ⊆ P := fun d hd ↦ hD d ((hD'' d).mp hd).1
  have hD''wo : IsWellOrderable D'' :=
    wellOrderable_of_cardLE ((cardLE_of_subset hD''P).trans hP) (ordinal_wellOrderable lam)
  obtain ⟨A', hA'⟩ := exists_maximalAntichain hR hD''P hD''wo
  obtain ⟨A, hA⟩ : ∃ A : V, ∀ x, x ∈ A ↔ x ∈ B' ∨ x ∈ A' := ⟨B' ∪ A', fun x ↦ mem_union_iff⟩
  have hAD : A ⊆ D := by
    intro x hx
    rcases (hA x).mp hx with hx | hx
    · exact hB'D x hx
    · exact ((hD'' x).mp (hA'.2.1 x hx)).1
  have hAanti : IsForcingAntichain P R A := by
    refine ⟨fun x hx ↦ hD x (hAD x hx), ?_⟩
    intro x hx y hy hne hc
    rcases (hA x).mp hx with hx | hx <;> rcases (hA y).mp hy with hy | hy
    · exact hB'anti.2 x hx y hy hne hc
    · exact ((hD'' y).mp (hA'.2.1 y hy)).2 x hx ⟨hc.choose, hc.choose_spec.1,
        hc.choose_spec.2.2, hc.choose_spec.2.1⟩
    · exact ((hD'' x).mp (hA'.2.1 x hx)).2 y hy hc
    · exact hA'.1.2 x hx y hy hne hc
  have hAmax : ∀ r ∈ P, ⟨r, p⟩ₖ ∈ R → ∃ a ∈ A, ForcingCompatible P R a r := by
    intro r hr hrp
    obtain ⟨d, hd, hdr⟩ := hdense r hr hrp
    by_cases hc : ∃ b ∈ B', ForcingCompatible P R d b
    · obtain ⟨b, hb, u, hu, hud, hub⟩ := hc
      exact ⟨b, (hA b).mpr (Or.inl hb), u, hu, hub, hR.2.2 u hu d (hD d hd) r hr hud hdr⟩
    · push_neg at hc
      obtain ⟨a, ha, u, hu, hua, hud⟩ := hA'.2.2 d ((hD'' d).mpr ⟨hd, hc⟩)
      exact ⟨a, (hA a).mpr (Or.inr ha), u, hu, hua, hR.2.2 u hu d (hD d hd) r hr hud hdr⟩
  have hAlam : lam ≋ A :=
    ⟨hlamB'.trans (cardLE_of_subset (fun x hx ↦ (hA x).mpr (Or.inl hx))),
      (cardLE_of_subset (fun x hx ↦ hD x (hAD x hx))).trans hP⟩
  obtain ⟨f, hf, hfinj, hfr⟩ := exists_bijection_of_cardEQ hAlam
  have : IsFunction f := IsFunction.of_mem hf
  refine ⟨f, mem_function_of_mem_function_of_subset hf (fun x hx ↦ hD x (hAD x hx)), hfinj,
    hfr ▸ hAD, hfr ▸ hAanti, ?_⟩
  intro r hr hrp
  obtain ⟨a, ha, hc⟩ := hAmax r hr hrp
  rw [← hfr] at ha
  obtain ⟨α, hα⟩ := mem_range_iff.mp ha
  have hαl : α ∈ lam := domain_eq_of_mem_function hf ▸ mem_domain_of_kpair_mem hα
  exact ⟨α, hαl, value_eq_of_kpair_mem hα ▸ hc⟩

end ZFVP
