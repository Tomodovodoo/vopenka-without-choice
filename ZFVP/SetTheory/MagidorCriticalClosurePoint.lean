import ZFVP.SetTheory.MagidorLemmaThreeOne
import ZFVP.SetTheory.MagidorLeastClosurePointTransfer
import ZFVP.SetTheory.MagidorClosureLimitPoint

/-! # The critical point of a Vopenka embedding is a Magidor closure point

This is the step of Bagaria's Theorem 4.3(2) that calls on Kunen's theorem.

`f` embeds `V_{lam+ω}` into `V_{lam'+ω}` with critical point `κ ∈ lam`, and the closure points of
the failure function `magidorFailure ρ` are cofinal in `lam`. The claim is that `κ` is itself a
closure point: the failure stage of every `ν ∈ κ` above `ρ` is again below `κ`.

Without Kunen's theorem the claim can fail on its face. Nothing said so far stops `κ` from sitting
above all the closure points that the cofinality hypothesis produces below it, and then the failure
stage of some `ν ∈ κ` could land above `κ`. The argument rules that out as follows. If
`magidorFailure ρ ν` escapes `κ`, take `d` to be the least closure point above `ν`. It lies below
`lam` because the closure points are cofinal there, and it lies above `κ` because it already
contains `magidorFailure ρ ν`. Both `ν` and `d` are fixed by `f`: `ν` because it is below the
critical point, and `d` because it is the least ordinal with a condition that crosses the embedding
(`value_eq_of_isLeastMagidorClosurePointAbove`). Now the two halves collide. Kunen's theorem, in
the form `exists_criticalIterate_mem`, says the critical sequence of `κ` passes above `d`, while a
fixed `d` containing `κ` keeps the whole critical sequence inside `d`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- If `f` fixes `β`, the whole critical sequence of `κ ∈ β` stays inside `β`. Same statement and
proof as `ZFVP.criticalIterate_mem_of_fixed` in `ZFVP.SetTheory.CriticalPointGoodClosure`, repeated
here so that this module does not have to import the `C(n)` machinery. -/
private theorem criticalIterate_mem_of_fixed' {A B f κ β : V} [IsTransitive A]
    (h : IsCodedMembershipEmbedding A B f) (hβA : β ∈ A) (hβsub : β ⊆ A)
    (hfix : f ‘ β = β) (hκβ : κ ∈ β) {n : V} (hn : n ∈ (ω : V)) :
    criticalIterate f κ n ∈ β := by
  have hi : ∀ m ∈ (ω : V), criticalIterate f κ m ∈ β := by
    apply naturalNumber_induction (fun m ↦ criticalIterate f κ m ∈ β) (by definability)
    · simpa using hκβ
    · intro m hm ih
      rw [criticalIterate_succ f κ hm, ← hfix]
      exact (h.value_mem_iff (hβsub _ ih) hβA).mpr ih
  exact hi n hn

/-- The critical point of a coded embedding of `V_{lam+ω}` is a closure point of the failure
function `magidorFailure ρ`, provided `f` fixes `ρ`, the critical point is above `ρ` and below
`lam`, and the closure points are cofinal in `lam`. -/
theorem criticalPoint_isMagidorClosurePoint (hAC : InternalChoice V) {lam lam' f κ ρ : V}
    [IsOrdinal lam] [IsOrdinal lam'] [IsOrdinal ρ]
    (hlim : IsLimitOrdinal lam) (hωlam : (ω : V) ∈ lam)
    (hlim' : IsLimitOrdinal lam') (hωlam' : (ω : V) ∈ lam')
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy (ordinalAdd (ω : V) (ω : V)))
    (h : IsCodedMembershipEmbedding (hierarchy (ordinalAdd lam (ω : V)))
      (hierarchy (ordinalAdd lam' (ω : V))) f)
    (hκ : IsCriticalPoint (hierarchy (ordinalAdd lam (ω : V))) f κ)
    (htot : MagidorFailureTotal ρ) (hfρ : f ‘ ρ = ρ) (hρκ : ρ ∈ κ) (hκlam : κ ∈ lam)
    (hlimpt : ∀ ξ ∈ lam, ∃ d ∈ lam, ξ ∈ d ∧ IsMagidorClosurePoint ρ d) :
    IsMagidorClosurePoint ρ κ := by
  let := hierarchy_transitive (ordinalAdd lam (ω : V))
  let := hierarchy_transitive (ordinalAdd lam' (ω : V))
  have hlamθ : lam ∈ ordinalAdd lam (ω : V) := ordinalAdd_omega_gt lam
  have hωθ : (ω : V) ∈ ordinalAdd lam (ω : V) :=
    IsOrdinal.toIsTransitive.mem_trans hωlam hlamθ
  have hsuccθ : ∀ ξ ∈ ordinalAdd lam (ω : V), succ ξ ∈ ordinalAdd lam (ω : V) :=
    fun _ hξ ↦ ordinalAdd_omega_succ_closed lam hξ
  let := (hierarchy_isSequenceSupport hωθ hsuccθ).toIsCodingSupport
  let := hκ.ordinal
  -- the critical point is a limit ordinal: it holds `ω` and is closed under successors
  have hωκ : (ω : V) ∈ κ := hκ.omega_lt h
  have hsuccκ : ∀ ξ ∈ κ, succ ξ ∈ κ := fun _ hξ ↦ hκ.succ_closed h hξ
  have hlimκ : IsLimitOrdinal κ := by
    refine ⟨hκ.ordinal, ?_, ?_⟩
    · intro he
      exact not_mem_empty (he ▸ hωκ)
    · rintro ⟨β, hβ⟩
      have hβκ : β ∈ κ := by rw [hβ]; exact mem_succ_self β
      have hsβ : succ β ∈ κ := hsuccκ β hβκ
      rw [← hβ] at hsβ
      exact mem_irrefl κ hsβ
  refine ⟨hlimκ, hρκ, ?_⟩
  intro ν hνκ hρν
  by_contra hbad
  have hνord : IsOrdinal ν := IsOrdinal.of_mem hνκ
  let := hνord
  -- the escaping failure stage sits above `κ`
  have hFord : IsOrdinal (magidorFailure ρ ν) := magidorFailure_isOrdinal htot ν
  let := hFord
  have hκF : κ ⊆ magidorFailure ρ ν := by
    rcases IsOrdinal.mem_trichotomy (magidorFailure ρ ν) κ with hlt | heq | hgt
    · exact absurd hlt hbad
    · rw [heq]
    · exact IsOrdinal.toIsTransitive.transitive κ hgt
  -- the least closure point above `ν`
  set d : V := leastMagidorClosurePoint ρ ν with hddef
  have hdord : IsOrdinal d := leastMagidorClosurePoint_isOrdinal htot ν
  let := hdord
  have hνd : ν ∈ d := mem_leastMagidorClosurePoint htot ν
  have hdcp : IsMagidorClosurePoint ρ d := leastMagidorClosurePoint_isClosurePoint htot ν
  have hdmin : ∀ ξ ∈ d, ν ∈ ξ → ¬ IsMagidorClosurePoint ρ ξ :=
    leastMagidorClosurePoint_least htot ν
  have hleast : IsLeastMagidorClosurePointAbove ρ ν d := ⟨hνd, hdcp, hdmin⟩
  -- `d` is below `lam`, because the closure points are cofinal in `lam`
  have hνlam : ν ∈ lam := IsOrdinal.toIsTransitive.mem_trans hνκ hκlam
  have hdlam : d ∈ lam := by
    obtain ⟨d₀, hd₀lam, hνd₀, hd₀cp⟩ := hlimpt ν hνlam
    have hd₀ord : IsOrdinal d₀ := IsOrdinal.of_mem hd₀lam
    let := hd₀ord
    rcases IsOrdinal.mem_trichotomy d d₀ with hlt | heq | hgt
    · exact IsOrdinal.toIsTransitive.mem_trans hlt hd₀lam
    · exact heq ▸ hd₀lam
    · exact absurd hd₀cp (hdmin d₀ hgt hνd₀)
  -- `f` fixes `ν`, hence also `d`
  have hfν : f ‘ ν = ν := hκ.fixed_below hνκ
  have hρd : ρ ∈ d := hdcp.2.1
  have hfd : f ‘ d = d :=
    value_eq_of_isLeastMagidorClosurePointAbove hlim hωlam hlim' hωlam' h htot hfρ hdlam hρd
      hνd hfν hleast
  -- `κ` is below `d`, since `d` already holds the failure stage of `ν`
  have hFd : magidorFailure ρ ν ∈ d := hdcp.2.2 ν hνd hρν
  have hκd : κ ∈ d := by
    rcases IsOrdinal.subset_iff.mp hκF with he | hlt
    · exact he ▸ hFd
    · exact IsOrdinal.toIsTransitive.mem_trans hlt hFd
  -- Kunen's theorem pushes the critical sequence above `d`, but a fixed `d` holds it in
  have hdθ : d ∈ ordinalAdd lam (ω : V) := IsOrdinal.toIsTransitive.mem_trans hdlam hlamθ
  have hdH : d ∈ hierarchy (ordinalAdd lam (ω : V)) :=
    ordinal_subset_hierarchy (ordinalAdd lam (ω : V)) _ hdθ
  have hdsub : d ⊆ hierarchy (ordinalAdd lam (ω : V)) := fun x hx ↦
    ordinal_subset_hierarchy (ordinalAdd lam (ω : V)) _
      (IsOrdinal.toIsTransitive.mem_trans hx hdθ)
  obtain ⟨n, hn, hdn⟩ :=
    exists_criticalIterate_mem hlim hωlam hlim' hωlam' hF h hκ hAC hκd hdlam
  have hnd : criticalIterate f κ n ∈ d := criticalIterate_mem_of_fixed' h hdH hdsub hfd hκd hn
  exact mem_irrefl d (IsOrdinal.toIsTransitive.mem_trans hdn hnd)

end ZFVP
