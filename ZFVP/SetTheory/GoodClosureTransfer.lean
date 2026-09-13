import ZFVP.SetTheory.ExtendibilityFailureClass
import ZFVP.ModelTheory.RankEmbeddingDictionary

/-! Moving the good closure point class through an elementary embedding between `C(k+2)` rank
stages.

`IsGoodClosurePoint k α x` is defined by the `Pi_{k+2}` formula `goodClosurePointFormula k`, so
`rankEmbedding_defined_iff` transfers it. The second theorem transfers the least good closure
point above a fixed ordinal: it is again least, hence fixed by the embedding. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Free variables `x`, `γ`, `α`: `γ ∈ x` and `x` is a good closure point for `α`. -/
def goodAboveFormula (k : ℕ) : SetTheorySemisentence 3 :=
  “x γ α. γ ∈ x ∧ !(goodClosurePointFormula k) x α”

theorem goodAboveFormula_pi (k : ℕ) : IsPiFormula (k + 2) (goodAboveFormula k) :=
  .and (.bounded (.rel _ _)) ((goodClosurePointFormula_pi k).subst _)

/-- Free variables `x`, `γ`, `α`: no element of `x` is a good closure point for `α` above `γ`. -/
def noGoodBelowFormula (k : ℕ) : SetTheorySemisentence 3 :=
  “x γ α. ∀ ξ ∈ x, ¬(γ ∈ ξ ∧ !(goodClosurePointFormula k) ξ α)”

theorem noGoodBelowFormula_sigma (k : ℕ) : IsSigmaFormula (k + 2) (noGoodBelowFormula k) :=
  .boundedAll (.bvar 0)
    (IsLevyFormula.neg (p := .pi)
      (.and (.bounded (.rel _ _)) ((goodClosurePointFormula_pi k).subst _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance goodClosurePointFormula_defined (k : ℕ) :
    Defined (fun v : Fin 2 → V ↦ IsGoodClosurePoint k (v 1) (v 0)) (goodClosurePointFormula k) :=
  goodClosurePointFormula_defines k

theorem goodAboveFormula_defines (k : ℕ) :
    Defined (fun v : Fin 3 → V ↦ v 1 ∈ v 0 ∧ IsGoodClosurePoint k (v 2) (v 0))
      (goodAboveFormula k) :=
  ⟨fun v ↦ by simp [goodAboveFormula]⟩

theorem noGoodBelowFormula_defines (k : ℕ) :
    Defined (fun v : Fin 3 → V ↦ ∀ ξ ∈ v 0, ¬(v 1 ∈ ξ ∧ IsGoodClosurePoint k (v 2) ξ))
      (noGoodBelowFormula k) :=
  ⟨fun v ↦ by simp [noGoodBelowFormula, imp_iff_not_or]⟩

/-! ### Least ordinals -/

/-- Two least ordinals for the same predicate agree. -/
theorem IsLeastOrdinal.unique {P : V → Prop} {a b : V} (ha : IsLeastOrdinal P a)
    (hb : IsLeastOrdinal P b) : a = b :=
  subset_antisymm (ha.2.2 b hb.1 hb.2.1) (hb.2.2 a ha.1 ha.2.1)

/-- Being the least ordinal satisfying `P` is the same as satisfying `P` with no element of the
ordinal satisfying `P`. The second form only quantifies over elements, so an embedding between
rank stages transfers it. -/
theorem isLeastOrdinal_iff {P : V → Prop} {d : V} :
    IsLeastOrdinal P d ↔ IsOrdinal d ∧ P d ∧ ∀ ξ ∈ d, ¬ P ξ := by
  constructor
  · rintro ⟨hd, hPd, hmin⟩
    have : IsOrdinal d := hd
    refine ⟨hd, hPd, ?_⟩
    intro ξ hξ hPξ
    have : IsOrdinal ξ := IsOrdinal.of_mem hξ
    exact mem_irrefl ξ (hmin ξ this hPξ ξ hξ)
  · rintro ⟨hd, hPd, hno⟩
    refine ⟨hd, hPd, ?_⟩
    intro β hβ hPβ
    have : IsOrdinal d := hd
    have : IsOrdinal β := hβ
    rcases IsOrdinal.mem_trichotomy d β with hlt | heq | hgt
    · exact IsOrdinal.toIsTransitive.transitive d hlt
    · exact heq ▸ fun x hx ↦ hx
    · exact absurd hPβ (hno β hgt)

/-! ### Transfer -/

theorem goodClosurePoint_transfer {k : ℕ} {δ ε f α x : V}
    (hδ : Cn (k + 2) δ) (hε : Cn (k + 2) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hα : α ∈ hierarchy δ) (hx : x ∈ hierarchy δ) (hfα : f ‘ α = α) :
    IsGoodClosurePoint k α x ↔ IsGoodClosurePoint k α (f ‘ x) := by
  have htransfer := rankEmbedding_defined_iff hδ hε h (goodClosurePointFormula_pi k)
    (fun v : Fin 2 → V ↦ IsGoodClosurePoint k (v 1) (v 0)) ![x, α]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hx, hα])
  simpa [hfα] using htransfer

theorem leastGoodClosurePoint_transfer_fixed {k : ℕ} {δ ε f α γ d : V}
    (hδ : Cn (k + 2) δ) (hε : Cn (k + 2) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hα : α ∈ hierarchy δ) (hfα : f ‘ α = α)
    (hγ : γ ∈ hierarchy δ) (hfγ : f ‘ γ = γ) (hd : d ∈ hierarchy δ)
    (hleast : IsLeastOrdinal (fun x ↦ γ ∈ x ∧ IsGoodClosurePoint k α x) d) :
    f ‘ d = d := by
  obtain ⟨hdord, hdP, hdno⟩ := isLeastOrdinal_iff.mp hleast
  have hv : ∀ i, (![d, γ, α] : Fin 3 → V) i ∈ hierarchy δ := by
    simp [Fin.forall_fin_iff_zero_and_forall_succ, hd, hγ, hα]
  have habove :=
    letI := goodAboveFormula_defines (V := V) k
    rankEmbedding_defined_iff hδ hε h (goodAboveFormula_pi k)
      (fun v : Fin 3 → V ↦ v 1 ∈ v 0 ∧ IsGoodClosurePoint k (v 2) (v 0)) ![d, γ, α] hv
  have hbelow :=
    letI := noGoodBelowFormula_defines (V := V) k
    rankEmbedding_defined_iff hδ hε h (noGoodBelowFormula_sigma k)
      (fun v : Fin 3 → V ↦ ∀ ξ ∈ v 0, ¬(v 1 ∈ ξ ∧ IsGoodClosurePoint k (v 2) ξ)) ![d, γ, α] hv
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, hfγ, hfα] at habove hbelow
  have hordfd : IsOrdinal (f ‘ d) := rankEmbedding_value_ordinal hδ hε h hdord hd
  refine (IsLeastOrdinal.unique (isLeastOrdinal_iff.mpr ⟨hordfd, habove.mp hdP, ?_⟩) hleast)
  exact hbelow.mp (fun ξ hξ hc ↦ hdno ξ hξ hc)

end ZFVP
