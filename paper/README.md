# Paper and supplement

- [Article PDF](vopenka_without_choice_V3.pdf) and [TeX source](vopenka_without_choice_V3.tex).
- [Supplement PDF](supplement.pdf) and [TeX source](supplement.tex).
- [Publication and submission instructions](../docs/submission.md).

The supplement contains the completed Woodin iteration and marked-rank lift,
finite-syntax and model interpretation, full Solovay identification,
membership-language end-extension construction and formal statement
correspondence. It is included as ancillary material in the arXiv source
archive. Its editable source and the Lean proof development are preserved in
the repository.

`python scripts/prepare-v3.py` reproduces the article from its archived arXiv
source and the specified mathematical edits. `python scripts/package-publication.py`
creates the upload archive. The review records are in `verification/`.

For page comparisons, download the published V2 PDF and run
`python scripts/render-v2-v3-comparison.py V2.pdf output/review`.
The script uses PyMuPDF and Pillow. It renders V2 on the left and V3 on the
right, with changed V3 words in red, and produces PNGs and a comparison PDF.
