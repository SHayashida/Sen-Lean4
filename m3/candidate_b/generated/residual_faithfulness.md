# Residual Faithfulness

| Retained T | Bundled | Status | Split | Status | Match |
|---|---|---|---|---|---|
| {} | `case_00000` | SAT | `case_000000` | SAT | PASS |
| {asymm} | `case_10000` | SAT | `case_100000` | SAT | PASS |
| {un} | `case_01000` | SAT | `case_010000` | SAT | PASS |
| {asymm, un} | `case_11000` | SAT | `case_110000` | SAT | PASS |
| {minlib} | `case_00100` | SAT | `case_001100` | SAT | PASS |
| {asymm, minlib} | `case_10100` | SAT | `case_101100` | SAT | PASS |
| {un, minlib} | `case_01100` | SAT | `case_011100` | SAT | PASS |
| {asymm, un, minlib} | `case_11100` | SAT | `case_111100` | SAT | PASS |
| {no_cycle4} | `case_00001` | SAT | `case_000001` | SAT | PASS |
| {asymm, no_cycle4} | `case_10001` | SAT | `case_100001` | SAT | PASS |
| {un, no_cycle4} | `case_01001` | SAT | `case_010001` | SAT | PASS |
| {asymm, un, no_cycle4} | `case_11001` | SAT | `case_110001` | SAT | PASS |
| {minlib, no_cycle4} | `case_00101` | SAT | `case_001101` | SAT | PASS |
| {asymm, minlib, no_cycle4} | `case_10101` | SAT | `case_101101` | SAT | PASS |
| {un, minlib, no_cycle4} | `case_01101` | SAT | `case_011101` | SAT | PASS |
| {asymm, un, minlib, no_cycle4} | `case_11101` | UNSAT | `case_111101` | UNSAT | PASS |

Rows: 16/16. Mismatches: 0. Result: **PASS**.
