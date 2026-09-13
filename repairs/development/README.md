# Rejected intermediate routes

These claims appeared in local proof development. Their failure is not evidence that the cited papers state them.

| Draft claim or shortcut | Why it fails or is insufficient | Replacement |
| --- | --- | --- |
| Every new rank below a Woodin cutoff remains small | Cantor's theorem defeats the asserted bound. | Bound the ranks below the stage index and enumerate the old ranks. [Marked-stage proof](../../ZFVP/ModelTheory/WoodinMarkedStageTheorem.lean). |
| Correctness at γ+ω follows from the cited lifting lemma | The required correctness does not follow at that fixed rank. | Capture a taller correct rank and use canonical inverses of compatible prefixes. The restricted lift is in [WoodinSparseActualCriticalLift](../../ZFVP/ModelTheory/WoodinSparseActualCriticalLift.lean). |
| Σ₁ membership of a collapse condition proves a Σ₁ graph for the entire carrier | These are different definability claims. | Separate the readouts and prove the relevant chain condition. [WoodinCollapse](../../ZFVP/SetTheory/WoodinCollapse.lean). |
| Being determined below ξ implies membership in the proposed support algebra | At empty support the algebra is only the two-element algebra, while a proper low condition need not belong to it. | [Support-algebra limits](../../ZFVP/ModelTheory/LevySupportAlgebraClosure.lean), then [high-cone transfer](../../ZFVP/ModelTheory/LevyHighConeTransfer.lean). |
| One support fixing a name fixes every subname | Name invariance does not imply hereditary support invariance. The local obstruction is conditional on its stated nontriviality premise. | [Exact limitation](../../ZFVP/ModelTheory/SolovaySupportAlgebraLimits.lean), then the high-cone route. |
| All complementary cones admit the proposed uniform isomorphism | The complement of the top cone is empty; a proper cone can have nonempty complement. | [Counterexample](../../ZFVP/ModelTheory/LevyComplementRefutation.lean), then supported cone shrinking. |
| Uncountably many ordinals alone supply the needed Q-cofinality | Bounded sections can already be uncountable. Ordinary first-order compactness also does not supply Q-completeness. | Explicit Q-smallness and the appropriate completeness theorem. [Weakly Rubin extraction](../../ZFVP/ModelTheory/SchmerlWeaklyRubinExtraction.lean). |

The arbitrary-ground Cohen and PSP restrictions, and the ordinary-real bridge, were implementation gaps that have been closed. They should not be listed as outstanding paper gaps. General second incompleteness, universal Boolean completion and prescribed-ground downward absoluteness were stronger unused routes; their absence does not block the current paper conclusions.
