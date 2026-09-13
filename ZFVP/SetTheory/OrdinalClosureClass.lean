import ZFVP.SetTheory.Cn
import ZFVP.SetTheory.TransfiniteIteration

/-! Closure points of a definable class function on the ordinals.

For a class function `G` on the ordinals, an ordinal closure point is a nonempty ordinal `lam`
with `G ξ ∈ lam` for every `ξ ∈ lam`. The class of these points is definable, unbounded, and
sits inside `C(n)` whenever every value of `G` does. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A nonempty ordinal closed under the class function `G`. -/
def IsOrdinalClosurePoint (G : V → V) (lam : V) : Prop :=
  IsOrdinal lam ∧ IsNonempty lam ∧ ∀ ξ ∈ lam, G ξ ∈ lam

theorem isOrdinalClosurePoint_definable {G : V → V} (hG : ℒₛₑₜ-function₁ G) :
    ℒₛₑₜ-predicate[V] (IsOrdinalClosurePoint G) := by
  unfold IsOrdinalClosurePoint
  definability

/-- Every closure point of a `C(n)`-valued increasing class function lies in `C(n)`. -/
theorem IsOrdinalClosurePoint.cn {k : ℕ} {G : V → V} {lam : V}
    (hGcn : ∀ ξ : V, IsOrdinal ξ → Cn k (G ξ))
    (hGgt : ∀ ξ : V, IsOrdinal ξ → ξ ∈ G ξ)
    (hlam : IsOrdinalClosurePoint G lam) : Cn k lam := by
  have hord : IsOrdinal lam := hlam.1
  refine cn_closed k hlam.2.1 ?_
  intro ξ hξ
  have hξo : IsOrdinal ξ := IsOrdinal.of_mem hξ
  exact ⟨G ξ, hlam.2.2 ξ hξ, hGgt ξ hξo, hGcn ξ hξo⟩

/-- A closure point of a strictly increasing class function is a limit ordinal. -/
theorem IsOrdinalClosurePoint.limit {G : V → V} {lam : V}
    (hGgt : ∀ ξ : V, IsOrdinal ξ → ξ ∈ G ξ) (hlam : IsOrdinalClosurePoint G lam) :
    IsLimitOrdinal lam := by
  have hord : IsOrdinal lam := hlam.1
  refine ⟨hord, ?_, ?_⟩
  · intro h
    obtain ⟨x, hx⟩ := hlam.2.1.nonempty
    exact not_mem_empty (h ▸ hx)
  · rintro ⟨β, rfl⟩
    have hβ : β ∈ succ β := mem_succ_self β
    have hβo : IsOrdinal β := IsOrdinal.of_mem hβ
    rcases mem_succ_iff.mp (hlam.2.2 β hβ) with he | hlt
    · have h1 : β ∈ G β := hGgt β hβo
      rw [he] at h1
      exact mem_irrefl β h1
    · exact mem_irrefl β (IsOrdinal.toIsTransitive.mem_trans (hGgt β hβo) hlt)

/-! ### Existence of closure points -/

/-- One step towards a closure point: the supremum of `succ (G ζ)` over `ζ ≤ α`. -/
noncomputable def ordinalClassClosureStep (G : V → V) (hG : ℒₛₑₜ-function₁ G) (α : V) : V :=
  ⋃ˢ (repl (fun ζ ↦ succ (G ζ)) (by definability) (succ α))

theorem ordinalClassClosureStep_definable (G : V → V) (hG : ℒₛₑₜ-function₁ G) :
    ℒₛₑₜ-function₁ (ordinalClassClosureStep G hG) := by
  unfold ordinalClassClosureStep
  definability

theorem mem_ordinalClassClosureStep_iff (G : V → V) (hG : ℒₛₑₜ-function₁ G) (α x : V) :
    x ∈ ordinalClassClosureStep G hG α ↔ ∃ ζ ∈ succ α, x ∈ succ (G ζ) := by
  unfold ordinalClassClosureStep
  rw [mem_sUnion_iff]
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨ζ, hζ, rfl⟩ := (repl_spec _).mp hy
    exact ⟨ζ, hζ, hxy⟩
  · rintro ⟨ζ, hζ, hx⟩
    exact ⟨_, (repl_spec _).mpr ⟨ζ, hζ, rfl⟩, hx⟩

theorem value_mem_ordinalClassClosureStep {G : V → V} (hG : ℒₛₑₜ-function₁ G) {α ζ : V}
    (h : ζ ∈ succ α) : G ζ ∈ ordinalClassClosureStep G hG α :=
  (mem_ordinalClassClosureStep_iff G hG α _).mpr ⟨ζ, h, mem_succ_self _⟩

theorem ordinalClassClosureStep_isOrdinal {G : V → V} (hG : ℒₛₑₜ-function₁ G)
    (hGord : ∀ ξ : V, IsOrdinal ξ → IsOrdinal (G ξ)) {α : V} (hα : IsOrdinal α) :
    IsOrdinal (ordinalClassClosureStep G hG α) := by
  have : IsOrdinal α := hα
  have hsα : IsOrdinal (succ α) := inferInstance
  unfold ordinalClassClosureStep
  apply IsOrdinal.sUnion
  intro y hy
  obtain ⟨ζ, hζ, rfl⟩ := (repl_spec _).mp hy
  have hζo : IsOrdinal ζ := IsOrdinal.of_mem hζ
  have : IsOrdinal (G ζ) := hGord ζ hζo
  exact inferInstance

/-- `ω` is a limit ordinal. -/
theorem isLimitOrdinal_omega' : IsLimitOrdinal (ω : V) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · intro h
    exact not_mem_empty (h ▸ (empty_mem_ω : (∅ : V) ∈ (ω : V)))
  · rintro ⟨ξ, hξ⟩
    have hξω : ξ ∈ (ω : V) := hξ ▸ mem_succ_self ξ
    exact mem_irrefl _ (hξ ▸ ω_succ_closed hξω)

/-- Above every ordinal there is an ordinal closure point of `G`. -/
theorem exists_ordinalClosurePoint_above {G : V → V} (hG : ℒₛₑₜ-function₁ G)
    (hGord : ∀ ξ : V, IsOrdinal ξ → IsOrdinal (G ξ))
    (hGgt : ∀ ξ : V, IsOrdinal ξ → ξ ∈ G ξ)
    (γ : V) [IsOrdinal γ] : ∃ lam : V, γ ∈ lam ∧ IsOrdinalClosurePoint G lam := by
  have hH : ℒₛₑₜ-function₁ (ordinalClassClosureStep G hG) := ordinalClassClosureStep_definable G hG
  have hlim : IsLimitOrdinal (ω : V) := isLimitOrdinal_omega'
  have hit : ℒₛₑₜ-function₁ (iterate (ordinalClassClosureStep G hG) hH (succ γ)) :=
    iterate_definable hH (succ γ)
  have hzero : iterate (ordinalClassClosureStep G hG) hH (succ γ) 0 = succ γ := by
    have h0 : (0 : V) = (∅ : V) := rfl
    rw [h0, iterate_zero]
  have hiter : ∀ n ∈ (ω : V),
      IsOrdinal (iterate (ordinalClassClosureStep G hG) hH (succ γ) n) := by
    apply naturalNumber_induction
      (fun n ↦ IsOrdinal (iterate (ordinalClassClosureStep G hG) hH (succ γ) n)) (by definability)
    · rw [hzero]
      exact inferInstance
    · intro n hn ih
      have hno : IsOrdinal n := IsOrdinal.of_mem hn
      rw [iterate_succ hH (succ γ) n]
      exact ordinalClassClosureStep_isOrdinal hG hGord ih
  have hmem : ∀ x : V, x ∈ iterate (ordinalClassClosureStep G hG) hH (succ γ) ω ↔
      ∃ n ∈ (ω : V), x ∈ iterate (ordinalClassClosureStep G hG) hH (succ γ) n :=
    fun x ↦ mem_iterate_limit_iff hH (succ γ) ω hlim x
  have hlamord : IsOrdinal (iterate (ordinalClassClosureStep G hG) hH (succ γ) ω) := by
    rw [iterate_limit hH (succ γ) ω hlim]
    apply IsOrdinal.sUnion
    intro y hy
    obtain ⟨n, hn, rfl⟩ := (repl_spec _).mp hy
    exact hiter n hn
  have hγ : γ ∈ iterate (ordinalClassClosureStep G hG) hH (succ γ) ω := by
    refine (hmem γ).mpr ⟨0, by simp, ?_⟩
    rw [hzero]
    exact mem_succ_self γ
  refine ⟨_, hγ, hlamord, ⟨γ, hγ⟩, ?_⟩
  intro ξ hξ
  obtain ⟨n, hn, hξn⟩ := (hmem ξ).mp hξ
  have hno : IsOrdinal n := IsOrdinal.of_mem hn
  refine (hmem (G ξ)).mpr ⟨succ n, ω_succ_closed hn, ?_⟩
  rw [iterate_succ hH (succ γ) n]
  exact value_mem_ordinalClassClosureStep hG (mem_succ_iff.mpr (Or.inr hξn))

/-- Above every ordinal there is a least ordinal closure point of `G`. -/
theorem exists_least_ordinalClosurePoint_above {G : V → V} (hG : ℒₛₑₜ-function₁ G)
    (hGord : ∀ ξ : V, IsOrdinal ξ → IsOrdinal (G ξ))
    (hGgt : ∀ ξ : V, IsOrdinal ξ → ξ ∈ G ξ)
    (γ : V) [IsOrdinal γ] :
    ∃! lam : V, IsLeastOrdinal (fun x ↦ γ ∈ x ∧ IsOrdinalClosurePoint G x) lam := by
  have hdef : ℒₛₑₜ-predicate[V] (IsOrdinalClosurePoint G) := isOrdinalClosurePoint_definable hG
  apply leastOrdinal_existsUnique _ (by definability)
  obtain ⟨lam, hγ, hlam⟩ := exists_ordinalClosurePoint_above hG hGord hGgt γ
  exact ⟨lam, hlam.1, hγ, hlam⟩

end ZFVP
