#!/usr/bin/env bash
set -euo pipefail

# M4 finite-audit replay wrapper.
# This is not checker logic: it only invokes existing M4 scripts with fixed
# arguments and writes replay artifacts under /tmp/sen_m4_repro.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../../.." && pwd)"
OUT_ROOT="/tmp/sen_m4_repro"
CERT1_DIR="${OUT_ROOT}/residual_class_coverage_certificate"
MASK_SHAPE_DIR="${OUT_ROOT}/mask_shape_collapse_law_audit"
CERT2_DIR="${OUT_ROOT}/certificate2_phase_diagram_checker"

cd "${REPO_ROOT}"

echo "M4 finite-audit replay"
echo "repository_root=${REPO_ROOT}"
echo "working_directory=$(pwd)"
echo "commit=$(git rev-parse HEAD)"
echo "out_root=${OUT_ROOT}"
echo "solver=cadical"
echo "timeout=10.0"
mkdir -p "${OUT_ROOT}"

echo
echo "+ python3 scripts/exploration/m4/residual_class_coverage_certificate.py --solver cadical --timeout 10.0 --out ${CERT1_DIR}"
python3 scripts/exploration/m4/residual_class_coverage_certificate.py \
  --solver cadical \
  --timeout 10.0 \
  --out "${CERT1_DIR}"

echo
echo "+ python3 scripts/exploration/m4/mask_shape_collapse_law_audit.py --certificate-dir ${CERT1_DIR} --solver cadical --timeout 10.0 --out ${MASK_SHAPE_DIR}"
python3 scripts/exploration/m4/mask_shape_collapse_law_audit.py \
  --certificate-dir "${CERT1_DIR}" \
  --solver cadical \
  --timeout 10.0 \
  --out "${MASK_SHAPE_DIR}"

echo
echo "+ python3 scripts/exploration/m4/certificate2_phase_diagram_checker.py --certificate1-dir ${CERT1_DIR} --mask-shape-dir ${MASK_SHAPE_DIR} --out ${CERT2_DIR}"
python3 scripts/exploration/m4/certificate2_phase_diagram_checker.py \
  --certificate1-dir "${CERT1_DIR}" \
  --mask-shape-dir "${MASK_SHAPE_DIR}" \
  --out "${CERT2_DIR}"

echo
echo "machine_readable_output_hashes:"
shasum -a 256 \
  "${CERT1_DIR}/coverage_summary.json" \
  "${CERT1_DIR}/residual_class_coverage_certificate.json" \
  "${MASK_SHAPE_DIR}/mask_shape_collapse_summary.json" \
  "${MASK_SHAPE_DIR}/mask_shape_collapse_certificate.json" \
  "${CERT2_DIR}/m4_certificate2_summary.json" \
  "${CERT2_DIR}/m4_certificate2_certificate.json"

echo
echo "certificate2_summary_json:"
cat "${CERT2_DIR}/m4_certificate2_summary.json"
