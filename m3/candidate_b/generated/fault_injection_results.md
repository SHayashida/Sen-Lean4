# Fault-Injection Results

| Fault | Expected gate | Observed gate | Exit | Result |
|---|---|---|---:|---|
| `fully_active_bundled_status` | `fully_active_bundled` | `fully_active_bundled` | 1 | PASS |
| `fully_active_split_status` | `fully_active_split` | `fully_active_split` | 1 | PASS |
| `delete_mapped_row` | `residual_faithfulness` | `residual_faithfulness` | 1 | PASS |
| `swap_case_id` | `residual_faithfulness` | `residual_faithfulness` | 1 | PASS |
| `activate_no_cycle3` | `contract_schema` | `contract_schema` | 1 | PASS |
| `delete_d0_precomputed` | `precomputed_claim_crosscheck` | `precomputed_claim_crosscheck` | 1 | PASS |
| `add_fake_nonsingleton` | `precomputed_claim_crosscheck` | `precomputed_claim_crosscheck` | 1 | PASS |
| `mutate_bundled_residual` | `residual_faithfulness` | `residual_faithfulness` | 1 | PASS |
| `remove_d1_block` | `contract_schema` | `contract_schema` | 1 | PASS |
| `touch_all_grouping` | `contract_schema` | `contract_schema` | 1 | PASS |
| `source_content_hash` | `source_artifact_binding` | `source_artifact_binding` | 1 | PASS |
| `theorem_source_sha` | `theorem_binding` | `theorem_binding` | 1 | PASS |
| `duplicate_mapped_row` | `residual_faithfulness` | `residual_faithfulness` | 1 | PASS |
| `unknown_contract_atom` | `contract_schema` | `contract_schema` | 1 | PASS |
| `bit_order_change` | `case_schema` | `case_schema` | 1 | PASS |

All 15 mandatory faults were rejected at the expected gate.
