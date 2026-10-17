Verification inputs and generated evidence

Run ./scripts/verify.sh from the repository root. Its absolute or relative path
can also be invoked from another directory; it finds its own repository.
See docs/REPRODUCIBILITY.md for the supported Linux environment and full CLI.

source-manifest.json records SHA-256 and size for the unchanged 57 mathematical
modules, import-only root, historical CheckAxioms.lean, and three configuration
files. The 57 mathematical hashes equal the Step 22 audited baseline. The two
auxiliary source exceptions are explicit; unknown Lean sources cause refusal.
These hashes establish source identity, not mathematical correctness by themselves.

expected-declarations.json records all 1,742 compiled project declarations from
Step 22, including private and generated declarations. The current run obtains
their types, kinds, safety flags and transitive logical axioms from Lean again;
it does not infer proof completeness from a textual source scan. Definitions
and theorem assumptions are not custom logical axioms. The only allowed
transitive logical axioms are propext, Classical.choice and Quot.sound.

Seven compiler-generated non-theorem ._unsafe_rec helpers are partial runtime
definitions. Lean's replay intentionally excludes partial definitions. The
separate type/value dependency inspection checks all 1,735 safe project
constants and rejects any reference to an unsafe/partial constant. The seven
helpers are an exact named allowlist, not permission for authored partial
proofs, sorryAx, custom mathematical axioms or arbitrary unsafe declarations.

endpoints.json lists the 19 explicit principal endpoint/variant declarations
for #check and #print axioms. mathlib-imports.txt lists the 50 direct imports
whose official pinned cache closure is downloaded by preparation.

Each nonstatic run accepted after the preliminary source and lock checks creates
a new runs/<UTC>-<pid>-<random>/ directory. Static checks and preliminary refusals
report directly without creating a run directory. summary.json and
status.json contain exact command statuses, resource observations and scope.
The successful all-phase run has 57 explicit leaf builds, an import-only root
build, 1,742 declaration audits, 19 principal endpoint checks, and 57 exact-leaf
kernel replays. kernel-inputs.json hashes all 171 required .olean, .olean.server
and .olean.private parts before replay, then checks their hashes again.
Imported libraries are trusted; this does not replay Mathlib or use an external
independent kernel. Fresh output directories preserve previous run evidence.

The preparation/build/axiom/kernel phase summaries report only their own
completed phase(s). A successful --check is explicitly a static check and is
never a substitute for the complete default verification.

Generated runs, caches and the lock are excluded from the public source archive.
Historical development logs are not required by the portable verifier.

Step24 combined-repository records

The retained RELEASE_VERIFICATION.json, release-*.json and package-manifest.json
are historical Step23 evidence. The old package manifest describes only the
previous 87-file Lean archive. Current combined verification and file identity
are in COMBINED_VERIFICATION.json, manuscript-fidelity.json and
repository-manifest.json. The new Apache grant and manuscript rights decisions
are in ../LICENSE, ../NOTICE and ../docs/LICENSING.md.

Step24B successor candidate

COMBINED_VERIFICATION.json is preserved historical Step24 full-verification
evidence, including its superseded pending-rights assessment. STEP24B_AUDIT.json
is the current packaging/license/attribution assessment. LICENSE_INVENTORY.tsv
covers all original129 paths plus added paths, with the three historical support
files explicitly externalized. repository-manifest.json describes current files.
No Lean rebuild is claimed for Step24B: exact source, configuration and verifier
input preservation connects this candidate to the existing full certificate.

Author-approved acknowledgement follow-up (0.1.0-rc.4)

Victor approved and the candidate applies exactly one acknowledgement correction
in Main.tex. The other16 TeX files,8 figures and69 Lean/config/verifier inputs
remain unchanged from Step24. STEP24B_AUDIT.json records the precise source
and PDF delta plus two matching builds. Old manuscript-fidelity and combined
verification records remain historical; this current delta connects them to
the new PDF without rewriting their certificates. No Lean rebuild was needed.

Step25 initial public publication

The author explicitly authorized initial public commit/push and keeping the
target public, superseding prior private-upload prerequisites. Step24B records
remain historical. repository-manifest.json describes the exact publication
files. All mathematical Lean sources, pins and verifier inputs are unchanged.
The official versioned release is a later separately authorized action.
