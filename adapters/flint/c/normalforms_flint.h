/*
 * Copyright (c) 2026 Junye Ji. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 */

#ifndef NORMALFORMS_FLINT_H
#define NORMALFORMS_FLINT_H

#include <flint/fmpz_mat.h>

#define NORMALFORMS_FLINT_EXPECTED_VERSION "3.6.0"

enum normalforms_flint_status
{
    NORMALFORMS_FLINT_OK = 0,
    NORMALFORMS_FLINT_BAD_DIMENSIONS = 1,
    NORMALFORMS_FLINT_SINGULAR_TRANSFORM = 2,
    NORMALFORMS_FLINT_NONINTEGRAL_INVERSE = 3
};

const char * normalforms_flint_version(void);

int normalforms_flint_hnf(
    fmpz_mat_t h,
    fmpz_mat_t u,
    fmpz_mat_t u_inverse,
    const fmpz_mat_t input);

int normalforms_flint_snf(
    fmpz_mat_t s,
    fmpz_mat_t u,
    fmpz_mat_t u_inverse,
    fmpz_mat_t v,
    fmpz_mat_t v_inverse,
    const fmpz_mat_t input);

#endif
