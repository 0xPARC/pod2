#!/bin/sh

set -ex

replace () {
    new=$1
    old=$2

    find -name "*.rs" -exec sed -i "s/Error::$old/Error::$new/g" {} \;
}

# replace custom Custom
# replace plonky2_proof_fail Plonky2ProofFail
# replace key_not_found KeyNotFound
# replace statement_not_check StatementNotCheck
# replace repeated_value_of KeyNotFound
# replace statement_not_check StatementNotCheck
# replace repeated_value_of RepeatedValueOf
# replace not_type_statement NotTypeStatement
# replace pod_id_invalid PodIdInvalid
# replace op_invalid_args OpInvalidArgs
# replace statements_dont_match StatementsDontMatch
# replace diff_amount DiffAmount
# replace max_length MaxLength
# replace not_equal NotEqual
# replace middleware Middleware

replace key_not_found KeyNotFound
replace key_exists KeyExists
replace max_depth MaxDepth
replace empty_node EmptyNode
replace proof_fail ProofFail
replace invalid_proof InvalidProof
replace too_short_key TooShortKey
