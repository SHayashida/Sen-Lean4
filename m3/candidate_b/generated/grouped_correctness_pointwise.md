# Pointwise Grouped Correctness

| Deletion G | GroupedRepair | ContractRepair | Match |
|---|---|---|---|
| {} | False | False | PASS |
| {asymm} | True | True | PASS |
| {un} | True | True | PASS |
| {asymm, un} | False | False | PASS |
| {minlib} | True | True | PASS |
| {asymm, minlib} | False | False | PASS |
| {un, minlib} | False | False | PASS |
| {asymm, un, minlib} | False | False | PASS |
| {no_cycle4} | True | True | PASS |
| {asymm, no_cycle4} | False | False | PASS |
| {un, no_cycle4} | False | False | PASS |
| {asymm, un, no_cycle4} | False | False | PASS |
| {minlib, no_cycle4} | False | False | PASS |
| {asymm, minlib, no_cycle4} | False | False | PASS |
| {un, minlib, no_cycle4} | False | False | PASS |
| {asymm, un, minlib, no_cycle4} | False | False | PASS |

Points: 16/16. Mismatches: 0.

Raw repair canonicity: **FAIL**

Artifact-defined grouped correctness: **PASS**
