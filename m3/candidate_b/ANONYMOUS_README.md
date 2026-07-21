# Anonymous Candidate B Artifact

> Candidate B is an artifact-defined M3-B instantiation under the declared bundled contract.

This archive is generated independently from the public evidence package. Git
commit identities, source-branch names, author metadata, local paths, and run
timestamps are withheld. Evidence content is rehashed after sanitization.

From the extracted `candidate_b_artifact/` directory, run:

```bash
python3 tools/m3_candidate_b/validate_candidate_b.py \
  --contract m3/candidate_b/contract.json \
  --case-schema m3/candidate_b/case_schema.json \
  --source-artifacts m3/candidate_b/source_artifacts.json \
  --evidence m3/candidate_b/evidence \
  --theorem-binding m3/candidate_b/theorem_binding.json \
  --out m3/candidate_b/generated \
  --repo-root .

python3 verify_anonymous_manifest.py
```

The first command recomputes the finite application audit. The second checks
the exact archive file closure. The source-commit relationship was checked
when the public package was frozen; it is intentionally withheld here.

The included Lean files bind the abstract theorem-core content used by the
audit. Candidate B is not formalized in Lean, and this archive makes no claim
about semantic atom validity, encoder correctness, solver correctness,
prevalence, generality, or family-scale transfer.
