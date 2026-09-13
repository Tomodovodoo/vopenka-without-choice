import ZFVP.SetTheory.DependentChoice
import ZFVP.SetTheory.FiniteSequences
import ZFVP.SetTheory.NaturalPredecessor

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsPointedFinitePath (A R a s : V) : Prop :=
  s ∈ finiteSequences A ∧ (0 : V) ∈ domain s ∧ s ‘ 0 = a ∧
    ∀ i ∈ domain s, succ i ∈ domain s → ⟨s ‘ i, s ‘ (succ i)⟩ₖ ∈ R

instance isPointedFinitePath_definable : ℒₛₑₜ-relation₄[V] IsPointedFinitePath := by
  unfold IsPointedFinitePath
  definability

theorem function_append_value_old {A s n x i : V} (hs : s ∈ A ^ n) (hx : x ∈ A) (hi : i ∈ n) :
    (insert ⟨n, x⟩ₖ s) ‘ i = s ‘ i := by
  have : IsFunction s := IsFunction.of_mem hs
  have : IsFunction (insert ⟨n, x⟩ₖ s) := IsFunction.of_mem (function_append_mem hs hx)
  exact value_eq_of_kpair_mem (mem_insert.mpr (Or.inr
    (kpair_value_mem (by simpa only [domain_eq_of_mem_function hs] using hi))))

theorem function_append_value_new {A s n x : V} (hs : s ∈ A ^ n) (hx : x ∈ A) :
    (insert ⟨n, x⟩ₖ s) ‘ n = x := by
  have : IsFunction (insert ⟨n, x⟩ₖ s) := IsFunction.of_mem (function_append_mem hs hx)
  exact value_eq_of_kpair_mem (mem_insert.mpr (Or.inl rfl))

theorem pointedFinitePath_exists {A R a : V} (ha : a ∈ A) : ∃ s, IsPointedFinitePath A R a s := by
  let s := definableGraph (succ (0 : V)) (fun _ ↦ a) (by definability)
  have hs : s ∈ A ^ succ (0 : V) := definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ _ ↦ ha)
  have hd : domain s = succ (0 : V) := domain_eq_of_mem_function hs
  refine ⟨s, (mem_finiteSequences_iff _ _).mpr ⟨_, ω_succ_closed (by simp), hs⟩,
    by simp [hd], value_definableGraph _ _ _ (by simp), ?_⟩
  intro i hi hsi
  have hi0 : i = 0 := by simpa [hd, mem_succ_iff, zero_def] using hi
  subst i
  exact False.elim (mem_irrefl (succ (0 : V)) (hd ▸ hsi))

theorem pointedFinitePath_extend {A R a s : V} (hs : IsPointedFinitePath A R a s)
    (hR : ∀ x ∈ A, ∃ y ∈ A, ⟨x, y⟩ₖ ∈ R) :
    ∃ t, IsPointedFinitePath A R a t ∧ s ⊆ t ∧ domain t = succ (domain s) := by
  obtain ⟨hdω, hf⟩ := (mem_finiteSequences_iff_domain _ _).mp hs.1
  obtain hzero | ⟨n, hn, hdn⟩ := internalNatural_cases hdω
  · exact False.elim (by simpa [hzero, zero_def] using hs.2.1)
  have hsn : s ∈ A ^ succ n := hdn ▸ hf
  obtain ⟨x, hx, hlast⟩ := hR (s ‘ n) (function_value_mem hsn (by simp))
  let t := insert ⟨succ n, x⟩ₖ s
  have ht : t ∈ A ^ succ (succ n) := function_append_mem hsn hx
  have hdt : domain t = succ (succ n) := domain_eq_of_mem_function ht
  have hold (i : V) (hi : i ∈ succ n) : t ‘ i = s ‘ i := function_append_value_old hsn hx hi
  have hnew : t ‘ (succ n) = x := function_append_value_new hsn hx
  refine ⟨t, ⟨(mem_finiteSequences_iff _ _).mpr ⟨_, ω_succ_closed (ω_succ_closed hn), ht⟩,
    by rw [hdt]; exact zero_mem_succ_natural (ω_succ_closed hn),
    (hold 0 (zero_mem_succ_natural hn)).trans hs.2.2.1, ?_⟩,
    fun p hp ↦ mem_insert.mpr (Or.inr hp), by rw [hdt, hdn]⟩
  intro i hi hsi
  have hiω : i ∈ (ω : V) := IsOrdinal.toIsTransitive.mem_trans hi
    (hdt.symm ▸ ω_succ_closed (ω_succ_closed hn))
  have : IsOrdinal i := IsOrdinal.of_mem hiω
  have : IsOrdinal n := IsOrdinal.of_mem hn
  rcases mem_succ_iff.mp (hdt ▸ hsi) with heq | hlt
  · have hin : i = n := by
      have he := congrArg (fun z : V ↦ ⋃ˢ z) heq
      simpa only [sUnion_succ_of_transitive] using he
    subst i
    rw [hold n (by simp), hnew]
    exact hlast
  · have hiold : i ∈ succ n := IsOrdinal.toIsTransitive.mem_trans (by simp : i ∈ succ i) hlt
    rw [hold i hiold, hold (succ i) hlt]
    exact hs.2.2.2 i (hdn.symm ▸ hiold) (hdn.symm ▸ hlt)

theorem pointedDependentChoice_of_unpointed (hDC : InternalDependentChoice V) :
    InternalPointedDependentChoice V := by
  intro A R a ha hR
  let P : V := {s ∈ finiteSequences A ; IsPointedFinitePath A R a s}
  have hP (s : V) : s ∈ P ↔ IsPointedFinitePath A R a s := by
    exact ⟨fun h ↦ (mem_sep_iff.mp h).2, fun h ↦ mem_sep_iff.mpr ⟨h.1, h⟩⟩
  let Q : V := {p ∈ P ×ˢ P ; kpair.π₁ p ⊆ kpair.π₂ p ∧
    domain (kpair.π₂ p) = succ (domain (kpair.π₁ p))}
  have hQ (s t : V) : ⟨s, t⟩ₖ ∈ Q ↔ s ∈ P ∧ t ∈ P ∧ s ⊆ t ∧ domain t = succ (domain s) := by
    simp only [Q, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
    tauto
  obtain ⟨s, hs⟩ := pointedFinitePath_exists (R := R) ha
  have hserial : ∀ s ∈ P, ∃ t ∈ P, ⟨s, t⟩ₖ ∈ Q := by
    intro s hs
    obtain ⟨t, ht, hst, hd⟩ := pointedFinitePath_extend ((hP s).mp hs) hR
    exact ⟨t, (hP t).mpr ht, (hQ s t).mpr ⟨hs, (hP t).mpr ht, hst, hd⟩⟩
  obtain ⟨g, hg, hsteps⟩ := hDC P Q ⟨s, (hP s).mpr hs⟩ hserial
  have hpath (n : V) (hn : n ∈ (ω : V)) : IsPointedFinitePath A R a (g ‘ n) :=
    (hP _).mp (function_value_mem hg hn)
  have hext (n : V) (hn : n ∈ (ω : V)) : g ‘ n ⊆ g ‘ (succ n) ∧
      domain (g ‘ (succ n)) = succ (domain (g ‘ n)) := ((hQ _ _).mp (hsteps n hn)).2.2
  have hlen : ∀ n ∈ (ω : V), n ∈ domain (g ‘ n) := by
    apply naturalNumber_induction (fun n ↦ n ∈ domain (g ‘ n)) (by definability)
    · exact (hpath 0 (by simp)).2.1
    · intro n hn ih
      rw [(hext n hn).2]
      exact succ_mem_succ_of_natural_mem ((mem_finiteSequences_iff_domain _ _).mp (hpath n hn).1).1 ih
  let f := definableGraph (ω : V) (fun n ↦ (g ‘ n) ‘ n) (by definability)
  have htyped (n : V) (hn : n ∈ (ω : V)) : g ‘ n ∈ A ^ domain (g ‘ n) :=
    ((mem_finiteSequences_iff_domain _ _).mp (hpath n hn).1).2
  have hf : f ∈ A ^ (ω : V) := definableGraph_mem_function_of_mapsTo _ _ _ _
    (fun n hn ↦ function_value_mem (htyped n hn) (hlen n hn))
  have hval (n : V) (hn : n ∈ (ω : V)) : f ‘ n = (g ‘ n) ‘ n := value_definableGraph _ _ _ hn
  refine ⟨f, hf, (hval 0 (by simp)).trans (hpath 0 (by simp)).2.2.1, ?_⟩
  intro n hn
  have hn' := ω_succ_closed hn
  have : IsFunction (g ‘ n) := IsFunction.of_mem (htyped n hn)
  have : IsFunction (g ‘ (succ n)) := IsFunction.of_mem (htyped (succ n) hn')
  have hpair : ⟨n, (g ‘ n) ‘ n⟩ₖ ∈ g ‘ (succ n) := (hext n hn).1 _ (kpair_value_mem (hlen n hn))
  have heq : (g ‘ (succ n)) ‘ n = (g ‘ n) ‘ n := value_eq_of_kpair_mem hpair
  rw [hval n hn, hval (succ n) hn', ← heq]
  exact (hpath (succ n) hn').2.2.2 n (mem_domain_of_kpair_mem hpair) (hlen (succ n) hn')

theorem pointedDependentChoice_iff_unpointed :
    InternalPointedDependentChoice V ↔ InternalDependentChoice V :=
  ⟨dependentChoice_of_pointed, pointedDependentChoice_of_unpointed⟩

end ZFVP
