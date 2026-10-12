# Palomar statement package

The repository root is the selected Lean project. Use `comparator-palomar.json`
and `formalization.yaml`. The combined configuration compares four theorems
in `PalomarPaperChallenge` and `PalomarPaperSolution`:

| Paper conclusion | Selected declaration |
| --- | --- |
| Full symmetric VP preservation | `VopenkaWithoutChoice.palomar_preservation` |
| Equiconsistency | `VopenkaWithoutChoice.palomar_equiconsistency` |
| DC and failure of Choice | `VopenkaWithoutChoice.palomar_dependent_choice` |
| Ordinary-real Solovay consequence and ultrafilter | `VopenkaWithoutChoice.palomar_solovay_reals` |

The independent Challenge has 673 lines and imports only Mathlib. Its
membership, forcing, syntax and real-line definitions are explicit. The
proof-side dictionaries establish correspondence with the library; they
supply no extra hypotheses on the object models. The model domains need
not be externally well-founded or countable.

The Solution names the same four declarations and composes the dictionary
proofs with the formalization. The generator checks that its vocabularies
match the individual statement packages. The selected theorem families
retain the parameters and quantifiers stated in the paper.

The separate `comparator-palomar-*.json` files select individual result
families for diagnosis. `comparator.json` uses the Foundation vocabulary
and is not the Palomar intake configuration.

The protected local command is
`bash scripts/verify-protected.sh comparator-palomar.json` on Linux with
bubblewrap. It uses the pinned toolchainâ€™s Comparator and independent kernels.
The official **Palomar mechanical preflight** workflow runs the registryâ€™s
full reusable pipeline at its pinned revision. Wait for its passing
mechanical report before intake.

[Complete submission steps and publication order](submission.md) Â·
[Verification records](verification.md) Â·
[Mathematical supplement](../paper/supplement.pdf).
