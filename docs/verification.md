# Verification

The working-project full build recorded on 14 September 2026 completed 5,048 jobs. The accompanying [paper coverage map](paper-coverage.md) compares all 43 stated results: 41 are covered, including checked compositions, and two contain unmatched auxiliary clauses. It reports checks of 80 existing exports and four compositions, using only `propext`, `Classical.choice` and `Quot.sound`. Lean's metatheoretic choice axiom does not assert AC inside the modeled ZF universe.

The [composition checks](../verification/ExportChecks.lean) are included. After building, run `lake env lean verification/ExportChecks.lean` to repeat those checks. They supplement, rather than replace, inspection of hypotheses and definitions.

The initial publication preserved every copied Lean source byte-for-byte. [Initial source hashes](../verification/initial-source-sha256.json) identify that baseline; they are not a substitute for a clean build. Later Comparator and bridge additions are identified by their Git commits. The previous full-build result is historical evidence from the working project, not a claim that a fresh dependency download was rebuilt during repository preparation.

The kernel checks the formal propositions. The remaining question for each paper statement is whether its hypotheses and conclusion match those propositions. The two known differences are stated in the README and repair notes.

During repository preparation, both included verification files were run successfully with `lake env lean` against the working project's installed dependencies. Every copied project source matched its working-project counterpart, and every local ZFVP/Foundation import resolved in the snapshot. This check reused installed dependencies; it was not a fresh build of the published clone.

The independent Theorem B bridge passed checks of all eight modules. Its [receipt and source hashes](../verification/bridge-check.json) and [check output](../verification/bridge-check.txt) record the result against the installed pinned dependencies. The standalone PalomarChallenge and PalomarSolution also compiled locally. Protected Comparator and NanoDa results are reported by GitHub Actions, separately from these Lean compilation checks.

The independent Theorem A bridge passed checks of all four modules. Its [receipt and source hashes](../verification/preservation-bridge-check.json) record the same installed-dependency scope. PalomarPreservationChallenge and PalomarPreservationSolution compiled locally; the Solution's axiom report contains only the three axioms listed above.

The DC bridge's three modules and the Solovay bridge's five modules also compiled
against the installed dependencies. Their generated Challenge and Solution files
compiled separately. The [DC receipt](../verification/dc-bridge-check.json) and
[Solovay receipt](../verification/solovay-bridge-check.json) record source hashes;
the [Solovay export output](../verification/solovay-bridge-check.txt) includes
thirteen direct axiom checks. All final Solution reports contain only the three
permitted axioms. These records do not claim a protected comparison verdict.
