# Working on the formalization

Keep proved source modules in place. Use the paper coverage map to locate an
existing result before starting another proof. A broader statement gets its own
explicit obligation; an old progress label does not invalidate a compiled proof.

The root `Challenge.lean` and `Solution.lean` use identical theorem names in
separate environments. Never import Challenge from Solution. Change both
statements together and rerun Comparator when their types change. Deliberate
proof holes belong only to Challenge; implementation proofs must use no custom
axioms or `sorryAx`.

Run the repository preflight and targeted Lean checks for changes. The GitHub
workflow performs the full build and independent comparison. Keep mathematical
correspondence claims separate from these mechanical checks.

For a paper or source repair, record the exact theorem or lemma, the failed
inference, the replacement statement, and its proof link. Say whether the edit
belongs in this paper or in a proposed source correction. Do not describe a
proposed correction as endorsed by the cited authors.

See [Palomar preparation](docs/palomar.md) before changing the submission
interface. Do not claim registration from a green repository workflow.
