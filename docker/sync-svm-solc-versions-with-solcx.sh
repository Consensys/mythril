#!/usr/bin/env bash
set -euo pipefail

# Let solcx know about the solc versions installed by svm.
# We do this by symlinking svm's solc binaries into solcx's solc dir.
[[ -e ~/.svm ]] || exit 0
mkdir -p ~/.solcx
readarray -t svm_solc_bins <<<"$(find ~/.svm -type f -name 'solc-*')"
[[ ${svm_solc_bins[0]} != "" ]] || exit 0
for svm_solc in "${svm_solc_bins[@]}"; do
    name=$(basename "${svm_solc:?}")
    version="${name#"solc-"}" # strip solc- prefix
    solcx_solc=~/.solcx/"solc-v${version:?}"
    if [[ ! -e $solcx_solc ]]; then
        ln -s "${svm_solc:?}" "${solcx_solc:?}"
    fi
done
