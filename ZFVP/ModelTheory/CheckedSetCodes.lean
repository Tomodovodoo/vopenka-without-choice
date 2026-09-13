import ZFVP.ModelTheory.ForcingModelRank
import ZFVP.SetTheory.GodelPairing
import ZFVP.SetTheory.EndExtensionCollapseDescent
import ZFVP.SetTheory.SetCodes

/-! Set codes across a forcing extension.

Every piece of a set code is a check as soon as the data it is built from are checks. The Gödel
pairing of a checked ordinal is the check of the ground pairing, the relation that a set of
ordinals reads off through the pairing is the check of the ground relation, and a transitive
collapse of checked data takes checked values. Together with `exists_set_code` in the ground these
are the recognition steps of Laver's ground-model definability theorem. Everything here is about
an arbitrary `ForcingContext`, not about a particular forcing. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The Gödel pairing of a checked ordinal is the check of the Gödel pairing computed in the
ground. -/
theorem ForcingContext.godelPairing_eq_check (S : ForcingContext V) {lam : V} [IsOrdinal lam]
    {p : S.Model} (h : IsGodelPairing (S.check lam) p) :
    ∃ p₀ : V, IsGodelPairing lam p₀ ∧ p = S.check p₀ := by
  obtain ⟨p₀, hp₀⟩ := exists_godelPairing lam
  have h' : IsGodelPairing (S.check lam) (S.check p₀) :=
    S.checkEmbedding.isGodelPairing_map hp₀
  exact ⟨p₀, hp₀, godelPairing_unique h h'⟩

/-- The pairs of `lam` whose Gödel code under `p` lies in `A`. -/
noncomputable def pairingPreimage (lam p A : V) : V := {q ∈ lam ×ˢ lam ; p ‘ q ∈ A}

theorem mem_pairingPreimage_iff (lam p A q : V) :
    q ∈ pairingPreimage lam p A ↔ q ∈ lam ×ˢ lam ∧ p ‘ q ∈ A := by
  simp [pairingPreimage]

/-- The relation that a set of ordinals codes through a Gödel pairing is a check. -/
theorem ForcingContext.check_pairingPreimage (S : ForcingContext V) {lam p A : V}
    (hp : IsGodelPairing lam p) :
    S.check (pairingPreimage lam p A) = pairingPreimage (S.check lam) (S.check p) (S.check A) := by
  have : IsFunction p := hp.1
  have hdom : domain p = lam ×ˢ lam := hp.2.1
  have hside : ∀ q ∈ lam ×ˢ lam,
      (p ‘ q ∈ A ↔ (S.check p) ‘ (S.checkEmbedding q) ∈ S.check A) := by
    intro q hq
    have hv : (S.check p) ‘ (S.check q) = S.check (p ‘ q) :=
      S.check_value (by rw [hdom]; exact hq)
    show p ‘ q ∈ A ↔ (S.check p) ‘ (S.check q) ∈ S.check A
    rw [hv, S.check_mem_iff]
  have h := S.checkEmbedding.map_separation (lam ×ˢ lam) (fun q ↦ p ‘ q ∈ A)
    (fun q ↦ (S.check p) ‘ q ∈ S.check A) (by definability) (by definability) hside
  rw [S.checkEmbedding.map_prod lam lam] at h
  exact h

/-- A subset of the checked square that is the pairing preimage of a checked set is itself a
check. -/
theorem ForcingContext.check_of_pairingPreimage (S : ForcingContext V) {lam p₀ A₀ : V}
    [IsOrdinal lam] (hp : IsGodelPairing lam p₀) {E : S.Model}
    (hE : ∀ q : S.Model, q ∈ E ↔
      (q ∈ S.check lam ×ˢ S.check lam ∧ (S.check p₀) ‘ q ∈ S.check A₀)) :
    E = S.check (pairingPreimage lam p₀ A₀) := by
  rw [S.check_pairingPreimage (A := A₀) hp]
  apply mem_ext
  intro q
  rw [hE q, mem_pairingPreimage_iff]

/-- A transitive collapse of checked data takes checked values at checked points. -/
theorem ForcingContext.check_of_collapse (S : ForcingContext V) {E₀ β₀ : V}
    {C f : S.Model} {t : S.Model}
    (hcol : IsTransitiveCollapse (S.check E₀) (S.check β₀) C f) (ht : t ∈ S.check β₀) :
    ∃ a : V, f ‘ t = S.check a := by
  have hcol' : IsTransitiveCollapse (S.checkEmbedding E₀) (S.checkEmbedding β₀) C f := hcol
  obtain ⟨C₀, f₀, _, hf, hcol₀⟩ :=
    S.checkEmbedding.exists_transitiveCollapse_descend hcol'
  obtain ⟨t₀, ht₀, rfl⟩ := (S.mem_check_iff β₀ t).mp ht
  have hf₀ : f₀ ∈ C₀ ^ β₀ := hcol₀.2.1
  have : IsFunction f₀ := IsFunction.of_mem hf₀
  have hdom : domain f₀ = β₀ := domain_eq_of_mem_function hf₀
  refine ⟨f₀ ‘ t₀, ?_⟩
  have hfe : f = S.check f₀ := hf
  rw [hfe]
  exact S.check_value (by rw [hdom]; exact ht₀)

/-- Under internal choice every set of the ground has a code whose collapse data are all checks,
and its check is the value of that checked collapse. -/
theorem ForcingContext.exists_checked_code (S : ForcingContext V) (hAC : InternalChoice V)
    (a : V) :
    ∃ β₀ E₀ t₀ : V, IsOrdinal β₀ ∧ E₀ ⊆ β₀ ×ˢ β₀ ∧ t₀ ∈ β₀ ∧
      IsTransitiveCollapse (S.check E₀) (S.check β₀)
        (S.check (range (mostowskiMap E₀ β₀))) (S.check (mostowskiMap E₀ β₀)) ∧
      S.check a = (S.check (mostowskiMap E₀ β₀)) ‘ (S.check t₀) := by
  obtain ⟨β, E, t, hβ, hsub, hwf, hext, ht, hval⟩ := exists_set_code hAC a
  have hc := mostowskiMap_isTransitiveCollapse hwf hext
  have : IsFunction (mostowskiMap E β) := IsFunction.of_mem hc.2.1
  have hdom : domain (mostowskiMap E β) = β := domain_eq_of_mem_function hc.2.1
  refine ⟨β, E, t, hβ, hsub, ht, ?_, ?_⟩
  · exact S.checkEmbedding.isTransitiveCollapse_map hc
  · rw [S.check_value (by rw [hdom]; exact ht), hval]

end ZFVP
