# Dependency provenance and licensing

This is a source snapshot of the local `ZF_VP_AC/lean` project, prepared on 14 September 2026. It includes the Lean sources and the original and V13 manuscripts. Build caches, local toolchains, credentials, conversation exports, external literature PDFs and the working repository's Git history are excluded.

Foundation originates at [FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation), commit `f212e81484a045697b3f6f171adf28fb57c750fc`. The vendored files include local changes and use the pinned mathlib revision. Its [Apache 2.0 license](../vendor/Foundation/LICENSE), citation file and upstream README are retained. The historical [compatibility patch](../patches/foundation-4.34.patch) documents the initial port; the vendored source is authoritative for this snapshot and may contain subsequent changes.

Mathlib is fetched at `065356127b1dc0016f66b7283ce0ce2c4055aa55`; its own license applies. Project code and documentation use the root Apache-2.0 licence. The mathematical paper and supplement use CC-BY-4.0 under paper/LICENSE. Third-party files retain their notices and licences.

The verification scripts use Comparator, lean4export, Lean's independent checker,
NanoDa and con-ron from the pinned Lean toolchain. These tools are not vendored
here. The historical scripts adapted the Apache-2.0 PalomarTemplate scripts at
`128a6c5ce5f48622e69927ccd639cbff401022e8`. Their licence copy is retained in
[scripts/LICENSE.Apache-2.0](../scripts/LICENSE.Apache-2.0). The root LICENSE supplies the Apache-2.0 licence for project code.

Foundation uses its standard `.lake/build` directory. Palomar grants build
access to that directory while keeping the vendored sources read-only.
