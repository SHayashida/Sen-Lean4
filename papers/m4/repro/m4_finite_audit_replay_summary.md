# M4 Finite-Audit Replay Summary

Classification: Case B. No single release-bound command was documented in the
result docs, but the existing scripts and expected artifacts made a safe replay
command reconstructable without changing checker logic.

Replay wrapper:

```text
papers/m4/repro/run_m4_finite_audit_replay.sh
```

Tracked replay log:

```text
papers/m4/repro/m4_finite_audit_checker.log
```

Temporary output root:

```text
/tmp/sen_m4_repro
```

The replay ran three existing scripts with fixed arguments:

```text
python3 scripts/exploration/m4/residual_class_coverage_certificate.py --solver cadical --timeout 10.0 --out /tmp/sen_m4_repro/residual_class_coverage_certificate
python3 scripts/exploration/m4/mask_shape_collapse_law_audit.py --certificate-dir /tmp/sen_m4_repro/residual_class_coverage_certificate --solver cadical --timeout 10.0 --out /tmp/sen_m4_repro/mask_shape_collapse_law_audit
python3 scripts/exploration/m4/certificate2_phase_diagram_checker.py --certificate1-dir /tmp/sen_m4_repro/residual_class_coverage_certificate --mask-shape-dir /tmp/sen_m4_repro/mask_shape_collapse_law_audit --out /tmp/sen_m4_repro/certificate2_phase_diagram_checker
```

Exit status: `0`.

## Headline Value Check

| Quantity | Expected from docs | Observed in replay | Status |
|---|---:|---:|---|
| total cells | 48 | 48 | reproduced |
| `ALL_UNSAT` cells | 18 | 18 | reproduced |
| `ALL_SAT` cells | 30 | 30 | reproduced |
| `MIXED_WITHIN_SHAPE` cells | 0 | 0 | reproduced |
| `UNKNOWN` cells | 0 | 0 | reproduced |
| repair-empty cells | 30 | 30 | reproduced |
| repair objects | 816 | 816 | reproduced |
| repair orbits | 46 | 46 | reproduced |
| cell report fibers | 46 | 46 | reproduced |
| shape-blind fibers | 33 | 33 | reproduced |
| support truncation verdict | `PASS` | `PASS` | reproduced |
| orbit/fiber exactness verdict | `PASS` | `PASS` | reproduced |
| orbit-stabilizer verdict | `PASS` | `PASS` | reproduced |
| non-circularity verdict | `PASS` | `PASS` | reproduced |
| Certificate 2 verdict | `PASS` | `PASS` | reproduced |

The replay log also records hashes for the machine-readable JSON outputs under
`/tmp/sen_m4_repro`. These generated outputs are not committed.

This replay does not prove checker correctness, Python encoder correctness,
semantic-to-CNF correctness, or Lean verification of the whole finite
certificate.
