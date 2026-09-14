# Repair index

Start with [which paper should contain each repair](placement.md). It gives a separate placement argument for every recorded source issue, then distinguishes application details and formalization differences. A source-proof defect belongs in a repair to the source; our paper needs an accurate repaired input and citation.

| Source and exact locus | Kind of issue | Where the proposed change belongs |
| --- | --- | --- |
| Woodin, Theorem 226, p. 323 | Initial-collapse convention needs a consistent seed or justification. | Source construction first; identify the imported convention in our paper. [Argument W1](placement.md#w1-initial-collapse). |
| Woodin, Theorem 226, pp. 323–324; Spoerl, Definition 43 and Theorem 44 | Raw and completed inverse stages must be distinguished. | Comparative source supplement; different conventions alone are not errors. [Argument W2](placement.md#w2-raw-inverse-stage-completed-stage-and-dc-bound). |
| Spoerl, Lemma 45, pp. 26–27 | Successor-rank agreement does not follow from prefix agreement. | Source lifting proof; our paper cites the sufficient restricted replacement. The stronger statement is not thereby proved. [Argument W3](placement.md#w3-lifting-to-the-final-successor-ranks). |
| Woodin, Theorem 226, clause 3, p. 326 | Correctness and ambient-HOD identifications remain unclosed here. | Separate source inquiry. The paper does not use this clause. |
| Enayat, Definition 5.13(b), Theorem 5.15 | Literal class member-coding contradicts ZF. | Source definition and construction. Our Proposition 9.7 cites the repaired existence input. [Argument E1](placement.md#e1-coding-a-proper-class-by-a-member). |
| Enayat, Definition 5.10(c), footnote 30 and appendix A3–A5, A7, Stage 2 | Maximality, quantifier, preservation, language and finite-domain problems. | Source supplement, with six separate arguments [E2–E7](placement.md#e2-maximal-directed-filter-versus-maximal-compatibility). |
| Mohammd, Definition 4.4 | Vacuous zero case. | Source definition and our explicitly repeated definition. [Argument M1](placement.md#m1-the-zero-rank-berkeley-case). |
| Karagila–Schilhan, Proposition 9.4, p. 33 | Lemma 9.3 requires same-extension comparison generics. | Source proof first; update the citation in our Solovay application. [Argument K1](placement.md#k1-comparison-generics-must-generate-the-same-extension). |
| Solovay regularity, Bagaria Theorem 4.11, Usuba Corollary 4.5 | Application details that must be supplied. | Our paper or its formalization supplement. No source defect asserted. |

Details and proof links: [Woodin and Spoerl](sources/woodin-spoerl/README.md), [Enayat](sources/enayat/README.md), [other inputs](sources/other/README.md). [Rejected development routes](development/README.md) are recorded separately to avoid attributing our failed intermediate claims to the authors.

[Consequences for our manuscript](our-paper/README.md) explains which downstream changes are citations, changed inputs, or proof expansions. [Remaining formalization differences](formalization/README.md) records the two unmatched V13 auxiliary clauses without inferring source errors from them.

The ambient-HOD clause is the source argument for which this work supplies no complete repair. The source lifting claim also deserves review at its original stronger scope; the paper uses the repaired restricted route. Enayat's literal coded-class definition must be changed, but a corrected definable-filter construction is supplied. None of these notes establishes author agreement with a proposed correction.
