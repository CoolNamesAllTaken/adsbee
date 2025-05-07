#!/usr/bin/env python3

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0


"""Prepare the source tree for proofs in continuous integration."""


import os
import subprocess


MAKEFILE = "Makefile"
CBMC_BATCH_YAML = "cbmc-batch.yaml"


def create_cbmc_batch_yaml(folder):
    """Run make to create cbmc-batch.yaml in folder."""

    try:
        subprocess.run(
            ["make", "-B", CBMC_BATCH_YAML],
            cwd=folder,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            universal_newlines=True,
            check=True
        )
    except subprocess.CalledProcessError as error:
        raise UserWarning("Failed to create {} in {}: "
                          "command was '{}': "
                          "error was '{}'"
                          .format(CBMC_BATCH_YAML, folder,
                                  ' '.join(error.cmd),
                                  error.stderr.strip())) from None


def create_cbmc_batch_yaml_files(root='.'):
    """Create cbmc-batch.yaml in all directories under root."""

    for folder, _, files in os.walk(root):
        if CBMC_BATCH_YAML in files and MAKEFILE in files:
            create_cbmc_batch_yaml(folder)


def prepare():
    """Prepare the source tree for proofs in continuous integration."""

    create_cbmc_batch_yaml_files()


if __name__ == "__main__":
    prepare()
