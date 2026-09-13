import ZFVP.SetTheory.MagidorClosurePoint
import ZFVP.SetTheory.MagidorLemmaThreeOne

/-! # One step reflection at a closure point of the failure function

Magidor's Lemma 3.1, in the form `ZFVP.SetTheory.MagidorLemmaThreeOne`, needs finite iterates of
the embedding `f` for one reason: the stage `γ` at which the critical point `κ` fails the small
embedding property may sit above `f ‘ κ`, and then one step of `f` has nothing to reflect. The
iterate is what pushes the critical sequence past `γ`.

Indexing the Vopenka class by closure points of the failure function removes that reason. If `κ` is
itself a closure point of `magidorFailure ρ`, then `γ := magidorFailure ρ κ` is below `κ`'s own
closure point condition transported by `f`, so `γ ∈ f ‘ κ` after one step, and
`magidorSupercompactAt_of_mem_value` already gives the small embedding at `γ`. That contradicts the
defining property of `γ`, so the situation is impossible. No iterate of `f` appears.

The transport of the closure point condition across `f` is `magidorClosurePoint_value_iff` of
`ZFVP.SetTheory.MagidorClosurePoint`, which reads the condition through a bounded formula.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- If the critical point `κ` of a coded embedding between the stages `V_{lam+ω}` and `V_{lam'+ω}`
is a closure point of the failure function, and `lam` is one too, there is no such embedding. One
step of `f` puts the failure stage of `κ` below `f ‘ κ`, the one step reflection gives the small
embedding at that stage, and being a failure stage denies it. -/
theorem false_of_magidorClosurePoint_criticalPoint {lam lam' f κ ρ : V}
    [IsOrdinal lam] [IsOrdinal lam'] [IsOrdinal ρ]
    (hlim : IsLimitOrdinal lam) (hωlam : (ω : V) ∈ lam)
    (hlim' : IsLimitOrdinal lam') (hωlam' : (ω : V) ∈ lam')
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy (ordinalAdd (ω : V) (ω : V)))
    (h : IsCodedMembershipEmbedding (hierarchy (ordinalAdd lam (ω : V)))
      (hierarchy (ordinalAdd lam' (ω : V))) f)
    (hκ : IsCriticalPoint (hierarchy (ordinalAdd lam (ω : V))) f κ)
    (htot : MagidorFailureTotal ρ) (hfρ : f ‘ ρ = ρ) (hρκ : ρ ∈ κ) (hκlam : κ ∈ lam)
    (hlamclos : IsMagidorClosurePoint ρ lam) (hκclos : IsMagidorClosurePoint ρ κ) :
    False := by
  let := hκ.ordinal
  let := hierarchy_transitive (ordinalAdd lam (ω : V))
  let := hierarchy_transitive (ordinalAdd lam' (ω : V))
  have hρsub : ρ ⊆ κ := IsOrdinal.toIsTransitive.transitive ρ hρκ
  -- the failure stage of the critical point
  set γ : V := magidorFailure ρ κ with hγdef
  have hκγ : κ ∈ γ := mem_magidorFailure htot κ
  have hγlam : γ ∈ lam := magidorFailure_mem_of_closurePoint hlamclos hρsub hκlam
  -- one step of `f` moves the critical point up and carries the closure point condition
  have hκf : κ ∈ f ‘ κ := hκ.lt_value h
  have hclos' : IsMagidorClosurePoint ρ (f ‘ κ) :=
    (magidorClosurePoint_value_iff hlim hωlam hlim' hωlam' h htot hfρ hκlam hρκ).mp hκclos
  have hγf : γ ∈ f ‘ κ := magidorFailure_mem_of_closurePoint hclos' hρsub hκf
  -- the one step reflection at that stage, against the failure
  have hsc : IsMagidorSupercompactAt κ γ :=
    magidorSupercompactAt_of_mem_value hlim hωlam hlim' hωlam' hF h hκ hκγ hγlam hγf
  exact not_magidorSupercompactAt_magidorFailure htot hρsub hsc

end ZFVP
