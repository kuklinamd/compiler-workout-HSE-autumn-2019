#!/usr/bin/env bash

make check \
    && pushd expressions && make check && popd \
    && pushd deep-expressions && make check && popd
