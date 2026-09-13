import ZFVP.ModelTheory.WoodinSuccessorTailEmpty
import ZFVP.ModelTheory.WoodinInverseTailEmpty

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinBound_eventual_empty_tails [Countable V] {δ θ i j p X : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hj : j ∈ θ) (hi : i ∈ j) (hlim : j ≠ succ (⋃ˢ j))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (hjinac : IsChoicelessInaccessible j)
    (hB : (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i ∈ hierarchy j)
    (hX : X ∈ hierarchy j)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ∀ (A : ForcingContext V),
      A.P = (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i →
      A.R = (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i →
      A.one = (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i → p ∈ A.G →
      ∀ g : ForcingName A.P, g.val = f.val →
        A.ofName g ∈ A.check (forcingInverseCodePoset θ (woodinIterationPrefix θ)) ^ A.check X) :
    ∃ b ∈ j, i ⊆ b ∧
      (∀ k, succ k ∈ j → b ⊆ k → woodinBoundSuccessorTail θ i p f.val k = ∅) ∧
      (∀ k ∈ j, b ∈ k → k ≠ succ (⋃ˢ k) →
        ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix k)) →
          woodinBoundInverseTail θ i p f.val k = ∅) := by
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hi
  have h0 : j ≠ ∅ := by rintro rfl; exact not_mem_empty hi
  obtain ⟨b, hb, hib, hsupport⟩ := woodinBound_uniform_direct_support hs hj hi hlim hinac hjinac hB hX f
  let := IsOrdinal.of_mem hb
  have hsA (A : ForcingContext V)
      (hP : A.P = (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      (hR : A.R = (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
      (ho : A.one = (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)
      (hpG : p ∈ A.G) (g : ForcingName A.P) (hg : g.val = f.val) :
      ∀ a ∈ A.check X, ∀ d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ),
        (A.ofName g) ‘ a = A.check d →
          IsThreadSupport j (forcingCodeE (woodinIterationPrefix j)) (d ‘ j) b := by
    obtain ⟨P, R, o, G, hR', ho', hG⟩ := A
    dsimp only at hP hR ho
    subst P R o
    have he : g = f := Subtype.ext hg
    subst g
    exact hsupport G hG hR' ho' (hf ⟨_, _, _, G, hR', ho', hG⟩ rfl rfl rfl hpG f rfl)
  refine ⟨b, hb, hib, ?_, ?_⟩
  · intro k hk hbk
    let := IsOrdinal.of_mem hk
    let := IsOrdinal.of_mem (mem_succ_self k)
    have hik : i ∈ succ k := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (subset_trans hib hbk))
    apply woodinBoundSuccessorTail_empty hs (IsOrdinal.toIsTransitive.mem_trans hk hj) hik hp f
    intro A hP hR ho hpG g hg
    refine ⟨hf A hP hR ho hpG g hg, ?_⟩
    intro a ha d hd had
    exact woodinThread_successor_tail_empty_of_support hs hj h0 hlim hinac hd
      (hsA A hP hR ho hpG g hg a ha d hd had) hk hbk
  · intro k hk hbk hklim hkinac
    let := IsOrdinal.of_mem hk
    have hik : i ∈ k := ordinal_mem_of_subset_mem hib hbk
    apply woodinBoundInverseTail_empty hs (IsOrdinal.toIsTransitive.mem_trans hk hj) hik hklim hkinac hp f
    intro A hP hR ho hpG g hg
    refine ⟨hf A hP hR ho hpG g hg, ?_⟩
    intro a ha d hd had
    exact woodinThread_inverse_tail_empty_of_support hs hj h0 hlim hinac hd
      (hsA A hP hR ho hpG g hg a ha d hd had) hk hbk hklim hkinac

end ZFVP
