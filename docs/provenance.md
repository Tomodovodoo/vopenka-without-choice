# Dependency provenance and licensing

This is a source snapshot of the local `ZF_VP_AC/lean` project, prepared on 14 September 2026. It includes the Lean sources and the original and V13 manuscripts. Build caches, local toolchains, credentials, conversation exports, external literature PDFs and the working repository's Git history are excluded.

Foundation originates at [FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation), commit `f212e81484a045697b3f6f171adf28fb57c750fc`. The vendored files include local changes and use the pinned mathlib revision. Its [Apache 2.0 license](../vendor/Foundation/LICENSE), citation file and upstream README are retained. The historical [compatibility patch](../patches/foundation-4.34.patch) documents the initial port; the vendored source is authoritative for this snapshot and may contain subsequent changes.

Mathlib is fetched at `83abb3e776bdefcbc447a1e44d0debe4010039e5`; its own license applies. This repository does not assign a new license to the project-authored proofs, repair notes or manuscripts. Existing author and third-party rights remain in force.

The Comparator setup scripts adapt the Apache-2.0 PalomarTemplate scripts at
`128a6c5ce5f48622e69927ccd639cbff401022e8`. Their source is recorded in the file
headers. Comparator, lean4export, Landrun and NanoDa are downloaded from their
recorded revisions by the verification script; they are not vendored here.
The adapted shell scripts retain the upstream Apache-2.0 terms; a copy is in
[scripts/LICENSE.Apache-2.0](../scripts/LICENSE.Apache-2.0). This does not select
a license for the project-authored proofs or manuscripts.

Foundation's Lake `buildDir` points into the root `.lake/foundation-build` so
the protected comparison can build this vendored path dependency without
granting write access to its source directory.
