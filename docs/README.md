# Documentation

* [V14 and earlier manuscripts](../paper/README.md): minimal revision from final,
  exact diff and individual edit reasons.
* [Palomar and Comparator](palomar.md): exact compared statements, tool pins,
  remaining interface work, and submission order.
* [Paper coverage](paper-coverage.md): all 43 stated V13 results and their exports.
* [Verification](verification.md): checks performed and their limits.
* [Provenance](provenance.md): source snapshot, dependencies and licensing.
* [Repair index](../repairs/README.md): source issues and proposed placement.
* [Arguments for repair placement](../repairs/placement.md): each source correction and its distinct consequence for our manuscript.

Lean source stays in its existing module hierarchy to preserve imports. The
root Challenge and Solution are the small comparison entry points. Manuscripts
remain in `paper/`; repair explanations remain in `repairs/`; reproducible
checks are in `scripts/` and `verification/`.
