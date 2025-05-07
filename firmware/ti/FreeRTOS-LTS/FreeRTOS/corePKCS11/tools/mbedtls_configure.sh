#!/bin/sh

if [ $# -ne 2 ]; then
    echo "Usage: mbedtls_configure.sh <MBEDTLS_SRC_DIR> <CONFIG_H_NAME>"
    exit 1
fi

MBEDTLS_DIR="${1}"
CONFIG="${2}"

cp "${MBEDTLS_DIR}/include/mbedtls/${CONFIG}" mbedtls_config_patch.h
"${MBEDTLS_DIR}/scripts/config.py" --file mbedtls_config_patch.h full_no_deprecated
"${MBEDTLS_DIR}/scripts/config.py" --file mbedtls_config_patch.h unset MBEDTLS_PSA_CRYPTO_BUILTIN_KEYS
"${MBEDTLS_DIR}/scripts/config.py" --file mbedtls_config_patch.h unset MBEDTLS_ENTROPY_NV_SEED
"${MBEDTLS_DIR}/scripts/config.py" --file mbedtls_config_patch.h unset MBEDTLS_PLATFORM_NV_SEED_ALT
"${MBEDTLS_DIR}/scripts/config.py" --file mbedtls_config_patch.h unset MBEDTLS_PSA_CRYPTO_C
"${MBEDTLS_DIR}/scripts/config.py" --file mbedtls_config_patch.h unset MBEDTLS_PSA_CRYPTO_CLIENT
"${MBEDTLS_DIR}/scripts/config.py" --file mbedtls_config_patch.h unset MBEDTLS_PSA_CRYPTO_DRIVERS
"${MBEDTLS_DIR}/scripts/config.py" --file mbedtls_config_patch.h unset MBEDTLS_SSL_PROTO_TLS1_3
"${MBEDTLS_DIR}/scripts/config.py" --file mbedtls_config_patch.h unset MBEDTLS_USE_PSA_CRYPTO
"${MBEDTLS_DIR}/scripts/config.py" --file mbedtls_config_patch.h unset MBEDTLS_PSA_CRYPTO_C
"${MBEDTLS_DIR}/scripts/config.py" --file mbedtls_config_patch.h unset MBEDTLS_PSA_CRYPTO_STORAGE_C
"${MBEDTLS_DIR}/scripts/config.py" --file mbedtls_config_patch.h unset MBEDTLS_PSA_ITS_FILE_C
"${MBEDTLS_DIR}/scripts/config.py" --file mbedtls_config_patch.h unset MBEDTLS_PSA_CRYPTO_SE_C
"${MBEDTLS_DIR}/scripts/config.py" --file mbedtls_config_patch.h unset MBEDTLS_LMS_C
"${MBEDTLS_DIR}/scripts/config.py" --file mbedtls_config_patch.h unset MBEDTLS_LMS_PRIVATE

cmp --quiet "${MBEDTLS_DIR}/include/mbedtls/config.h" mbedtls_config_patch.h || {
    cp mbedtls_config_patch.h "${MBEDTLS_DIR}/include/mbedtls/${CONFIG}"
}
