/*
 * Copyright (c) 2026 Junye Ji. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 */

#include "normalforms_flint.h"

#include <gmp.h>
#include <mpfr.h>

#include <flint/flint.h>
#include <flint/fmpz.h>

#if __GNU_MP_VERSION != 6 \
    || __GNU_MP_VERSION_MINOR != 3 \
    || __GNU_MP_VERSION_PATCHLEVEL != 0
#error "The normalforms FLINT adapter must be compiled against GMP 6.3.0"
#endif

#if MPFR_VERSION_MAJOR != 4 \
    || MPFR_VERSION_MINOR != 2 \
    || MPFR_VERSION_PATCHLEVEL != 2
#error "The normalforms FLINT adapter must be compiled against MPFR 4.2.2"
#endif

#if __FLINT_RELEASE != __FLINT_RELEASE_NUM(3, 6, 0)
#error "The normalforms FLINT adapter must be compiled against FLINT 3.6.0"
#endif

static int
matrix_dimensions_are(
    const fmpz_mat_t matrix,
    slong rows,
    slong columns)
{
    return fmpz_mat_nrows(matrix) == rows
        && fmpz_mat_ncols(matrix) == columns;
}

/*
 * FLINT represents an inverse as a numerator matrix and a common
 * denominator. A transformation is accepted only when that denominator is
 * exactly 1 or -1. In the latter case, negate the numerator so the output is
 * the actual integral inverse.
 */
static int
integral_inverse(
    fmpz_mat_t inverse,
    const fmpz_mat_t matrix)
{
    fmpz_t denominator;
    int success;

    fmpz_init(denominator);
    success = fmpz_mat_inv(inverse, denominator, matrix);
    if (!success)
    {
        fmpz_clear(denominator);
        return NORMALFORMS_FLINT_SINGULAR_TRANSFORM;
    }

    if (fmpz_is_one(denominator))
    {
        fmpz_clear(denominator);
        return NORMALFORMS_FLINT_OK;
    }

    if (fmpz_equal_si(denominator, -1))
    {
        fmpz_mat_neg(inverse, inverse);
        fmpz_clear(denominator);
        return NORMALFORMS_FLINT_OK;
    }

    fmpz_clear(denominator);
    return NORMALFORMS_FLINT_NONINTEGRAL_INVERSE;
}

const char *
normalforms_flint_version(void)
{
    return flint_version;
}

int
normalforms_flint_hnf(
    fmpz_mat_t h,
    fmpz_mat_t u,
    fmpz_mat_t u_inverse,
    const fmpz_mat_t input)
{
    slong rows = fmpz_mat_nrows(input);
    slong columns = fmpz_mat_ncols(input);

    if (!matrix_dimensions_are(h, rows, columns)
        || !matrix_dimensions_are(u, rows, rows)
        || !matrix_dimensions_are(u_inverse, rows, rows))
    {
        return NORMALFORMS_FLINT_BAD_DIMENSIONS;
    }

    /*
     * The explicit branch avoids depending on an implementation detail of
     * the HNF routine for empty matrices.
     */
    if (rows == 0 || columns == 0)
    {
        fmpz_mat_set(h, input);
        fmpz_mat_one(u);
        fmpz_mat_one(u_inverse);
        return NORMALFORMS_FLINT_OK;
    }

    fmpz_mat_hnf_transform(h, u, input);
    return integral_inverse(u_inverse, u);
}

int
normalforms_flint_snf(
    fmpz_mat_t s,
    fmpz_mat_t u,
    fmpz_mat_t u_inverse,
    fmpz_mat_t v,
    fmpz_mat_t v_inverse,
    const fmpz_mat_t input)
{
    slong rows = fmpz_mat_nrows(input);
    slong columns = fmpz_mat_ncols(input);
    int status;

    if (!matrix_dimensions_are(s, rows, columns)
        || !matrix_dimensions_are(u, rows, rows)
        || !matrix_dimensions_are(u_inverse, rows, rows)
        || !matrix_dimensions_are(v, columns, columns)
        || !matrix_dimensions_are(v_inverse, columns, columns))
    {
        return NORMALFORMS_FLINT_BAD_DIMENSIONS;
    }

    fmpz_mat_snf_transform(s, u, v, input);

    status = integral_inverse(u_inverse, u);
    if (status != NORMALFORMS_FLINT_OK)
        return status;

    return integral_inverse(v_inverse, v);
}
