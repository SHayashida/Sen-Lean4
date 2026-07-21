# Direct Exhaustive GroupSoundness

| Deletion R | Split | Group | Bundled | Result |
|---|---|---|---|---|
| {} | case_111101 UNSAT | {} | case_11101 UNSAT | PASS |
| {asymm} | case_011101 SAT | {asymm} | case_01101 SAT | PASS |
| {un} | case_101101 SAT | {un} | case_10101 SAT | PASS |
| {asymm, un} | case_001101 SAT | {asymm, un} | case_00101 SAT | PASS |
| {decisive_voter0} | case_110101 SAT | {minlib} | case_11001 SAT | PASS |
| {asymm, decisive_voter0} | case_010101 SAT | {asymm, minlib} | case_01001 SAT | PASS |
| {un, decisive_voter0} | case_100101 SAT | {un, minlib} | case_10001 SAT | PASS |
| {asymm, un, decisive_voter0} | case_000101 SAT | {asymm, un, minlib} | case_00001 SAT | PASS |
| {decisive_voter1} | case_111001 SAT | {minlib} | case_11001 SAT | PASS |
| {asymm, decisive_voter1} | case_011001 SAT | {asymm, minlib} | case_01001 SAT | PASS |
| {un, decisive_voter1} | case_101001 SAT | {un, minlib} | case_10001 SAT | PASS |
| {asymm, un, decisive_voter1} | case_001001 SAT | {asymm, un, minlib} | case_00001 SAT | PASS |
| {decisive_voter0, decisive_voter1} | case_110001 SAT | {minlib} | case_11001 SAT | PASS |
| {asymm, decisive_voter0, decisive_voter1} | case_010001 SAT | {asymm, minlib} | case_01001 SAT | PASS |
| {un, decisive_voter0, decisive_voter1} | case_100001 SAT | {un, minlib} | case_10001 SAT | PASS |
| {asymm, un, decisive_voter0, decisive_voter1} | case_000001 SAT | {asymm, un, minlib} | case_00001 SAT | PASS |
| {no_cycle4} | case_111100 SAT | {no_cycle4} | case_11100 SAT | PASS |
| {asymm, no_cycle4} | case_011100 SAT | {asymm, no_cycle4} | case_01100 SAT | PASS |
| {un, no_cycle4} | case_101100 SAT | {un, no_cycle4} | case_10100 SAT | PASS |
| {asymm, un, no_cycle4} | case_001100 SAT | {asymm, un, no_cycle4} | case_00100 SAT | PASS |
| {decisive_voter0, no_cycle4} | case_110100 SAT | {minlib, no_cycle4} | case_11000 SAT | PASS |
| {asymm, decisive_voter0, no_cycle4} | case_010100 SAT | {asymm, minlib, no_cycle4} | case_01000 SAT | PASS |
| {un, decisive_voter0, no_cycle4} | case_100100 SAT | {un, minlib, no_cycle4} | case_10000 SAT | PASS |
| {asymm, un, decisive_voter0, no_cycle4} | case_000100 SAT | {asymm, un, minlib, no_cycle4} | case_00000 SAT | PASS |
| {decisive_voter1, no_cycle4} | case_111000 SAT | {minlib, no_cycle4} | case_11000 SAT | PASS |
| {asymm, decisive_voter1, no_cycle4} | case_011000 SAT | {asymm, minlib, no_cycle4} | case_01000 SAT | PASS |
| {un, decisive_voter1, no_cycle4} | case_101000 SAT | {un, minlib, no_cycle4} | case_10000 SAT | PASS |
| {asymm, un, decisive_voter1, no_cycle4} | case_001000 SAT | {asymm, un, minlib, no_cycle4} | case_00000 SAT | PASS |
| {decisive_voter0, decisive_voter1, no_cycle4} | case_110000 SAT | {minlib, no_cycle4} | case_11000 SAT | PASS |
| {asymm, decisive_voter0, decisive_voter1, no_cycle4} | case_010000 SAT | {asymm, minlib, no_cycle4} | case_01000 SAT | PASS |
| {un, decisive_voter0, decisive_voter1, no_cycle4} | case_100000 SAT | {un, minlib, no_cycle4} | case_10000 SAT | PASS |
| {asymm, un, decisive_voter0, decisive_voter1, no_cycle4} | case_000000 SAT | {asymm, un, minlib, no_cycle4} | case_00000 SAT | PASS |

Implementation deletions: 32/32. Violations: 0. Result: **PASS**.
