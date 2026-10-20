# Concrete source construction contracts

The proof library includes complete forest, bounded-live-AND and proper-basis
constructors alongside the ten registry statement surfaces. The Comparator
configuration for each entry lists its registry-selected declarations.
[The companion audit manifest](provenance/construction-audit-targets.json)
identifies 402 audit targets covering construction, recovery,
optimality and native width.

Let `n` count channels, `q` observed roots, `G` the counted decoder source size,
and `S` the selected native source-circuit size. Construction uses the stated
source word/list model. Native source description, generic weight arithmetic,
encoded bit costs and retained external output are identified separately in
the theorem interfaces.

| Constructor | Checked contract | Source |
| --- | --- | --- |
| Forest | Exact cold resident image; linear source construction work and temporary storage; healthy-zero attained physical optimum for nonnegative weights | [ForestSourceCompiler](Controller/Cost/ForestSourceCompiler.lean), [ForestWeightedCold](Controller/Cost/ForestWeightedCold.lean) |
| Bounded live AND | Exact complete detector image; construction plus execution at most `8000000*(B_k(n)+q*2^k)*(G+1)+200000*(S+1)`; temporary constructor buffers at most `20000000000*(G+1)+2000000000*(S+1)` | [ConstructedExtensionsComplete](Controller/Cost/ConstructedExtensionsComplete.lean), [ExtensionConstructionStorage](Controller/Cost/ExtensionConstructionStorage.lean) |
| Proper basis | Complete constructed machine, termination, exact acceptance and native checking; construction plus execution at most `21000000*(n+q+1)*(G+1)+210000*(S+1)`; temporary constructor buffers at most `20000000000*(n+1)*(G+1)+2000000000*(S+1)` | [ProperDetectorConstruction](Controller/Cost/ProperDetectorConstruction.lean), [ExtensionConstructionStorage](Controller/Cost/ExtensionConstructionStorage.lean) |
| Critical/cycle recovery | One fixed 57-instruction source-reading program per width; complete source loading, canonical indicator output and physical realization under the specified source promise | [CriticalSourceRecovery](Controller/Cost/CriticalSourceRecovery.lean) |

`B_k(n)` is the bounded-support sum used by the bounded detector. Temporary
construction storage includes source validation/cache buffers, normalized row
profiles, operand emission, provisional images, discarded layout passes, packet
exchange, native finishing, relocation and final code copying. The assembly
trace charges instruction formation and left-spine copying. These are proved
word-model bounds, not measurements of the Lean runtime allocator.

The forest optimum contract requires healthy-zero observations, nonnegative
weights, positive bus count and detectability. No mixed-output maximum-weight
claim is made. The extension execution contracts retain raw native layout and
the stated basis or live-conjunction promises. Recovery consumes the supplied
structured source; it is not a recognizer for arbitrary malformed input.

The proof package uses Lean 4.35.0-rc3 and the exact Mathlib revision in
[lake-manifest.json](lake-manifest.json). Every Lean source uses the modern
module system. Public imports expose the proof interfaces; generated construction
recipes export their checked definition bodies for downstream reduction.

Build the companion import surface with:

```sh
lake build Phase1.Audit.Construction
python3 scripts/audit_construction.py --output .lake/construction-kernel-audit
```

The replay exports the listed declaration closures and standard kernel
primitives, then runs bundled con-ron, NanoDa and Lean's default checker with
only `propext`, `Classical.choice` and `Quot.sound` permitted. Its report records
source and export hashes. This local replay is separate from Palomar's protected
Linux workflow and editorial assessment.

The K00 bridge remains included. K01, full encoded-language classification and
the remaining whole-paper tranche are outside this package's construction scope.
