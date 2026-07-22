/*
 * Copyright (c) 2026 Junye Ji. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 */

#define _POSIX_C_SOURCE 200809L

#include "normalforms_flint.h"
#include "normalforms_protocol.h"

#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <gmp.h>
#include <mpfr.h>

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_mat.h>

#define NORMALFORMS_PROTOCOL "normalforms.decimal/v1"
#define NORMALFORMS_MAX_DIMENSION 4096UL
#define NORMALFORMS_MAX_ENTRIES 16777216UL
#define NORMALFORMS_MAX_LINE 1048576UL

enum normalforms_kind
{
    NORMALFORMS_KIND_HNF,
    NORMALFORMS_KIND_SNF
};

static void
protocol_error(FILE * error_stream, const char * detail)
{
    fprintf(
        error_stream,
        "normalforms-flint-worker: protocol error: %s\n",
        detail);
}

static void
computation_error(FILE * error_stream, int status)
{
    const char * detail = "unknown adapter failure";

    if (status == NORMALFORMS_FLINT_BAD_DIMENSIONS)
        detail = "internal matrix dimension mismatch";
    else if (status == NORMALFORMS_FLINT_SINGULAR_TRANSFORM)
        detail = "FLINT returned a singular transformation";
    else if (status == NORMALFORMS_FLINT_NONINTEGRAL_INVERSE)
        detail = "transformation inverse denominator was not a unit";

    fprintf(
        error_stream,
        "normalforms-flint-worker: computation error: %s\n",
        detail);
}

/*
 * Read one LF-terminated line. CRLF, embedded NUL bytes, overlong lines, and
 * a final unterminated line are rejected so the protocol has one canonical
 * byte representation.
 */
static int
read_line(FILE * input_stream, char * buffer, size_t capacity)
{
    size_t length;

    if (fgets(buffer, (int) capacity, input_stream) == NULL)
        return 0;

    length = strlen(buffer);
    if (length == 0 || buffer[length - 1] != '\n')
        return -1;
    if (length >= capacity - 1)
        return -1;

    buffer[length - 1] = '\0';
    if (length >= 2 && buffer[length - 2] == '\r')
        return -1;
    return 1;
}

static int
canonical_unsigned_decimal(const char * value)
{
    const unsigned char * cursor =
        (const unsigned char *) value;

    if (cursor[0] == '0' && cursor[1] == '\0')
        return 1;
    if (cursor[0] < '1' || cursor[0] > '9')
        return 0;

    for (cursor++; *cursor != '\0'; cursor++)
    {
        if (*cursor < '0' || *cursor > '9')
            return 0;
    }
    return 1;
}

static int
canonical_integer(const char * value)
{
    const unsigned char * cursor =
        (const unsigned char *) value;

    if (cursor[0] == '0' && cursor[1] == '\0')
        return 1;
    if (cursor[0] == '-')
        cursor++;
    if (cursor[0] < '1' || cursor[0] > '9')
        return 0;

    for (cursor++; *cursor != '\0'; cursor++)
    {
        if (*cursor < '0' || *cursor > '9')
            return 0;
    }
    return 1;
}

static int
parse_bounded_unsigned(
    const char * value,
    unsigned long bound,
    unsigned long * result)
{
    char * end = NULL;
    unsigned long parsed;

    if (!canonical_unsigned_decimal(value))
        return 0;

    errno = 0;
    parsed = strtoul(value, &end, 10);
    if (errno != 0 || end == NULL || *end != '\0' || parsed > bound)
        return 0;

    *result = parsed;
    return 1;
}

static int
parse_prefixed_unsigned(
    const char * line,
    const char * prefix,
    unsigned long bound,
    unsigned long * result)
{
    size_t prefix_length = strlen(prefix);

    if (strncmp(line, prefix, prefix_length) != 0)
        return 0;
    return parse_bounded_unsigned(line + prefix_length, bound, result);
}

static int
write_matrix(
    FILE * output_stream,
    const char * name,
    const fmpz_mat_t matrix)
{
    slong row;
    slong column;
    slong rows = fmpz_mat_nrows(matrix);
    slong columns = fmpz_mat_ncols(matrix);
    unsigned long entries =
        (unsigned long) rows * (unsigned long) columns;

    if (fprintf(
            output_stream,
            "matrix %s %ld %ld %lu\n",
            name,
            (long) rows,
            (long) columns,
            entries) < 0)
        return 0;

    for (row = 0; row < rows; row++)
    {
        for (column = 0; column < columns; column++)
        {
            char * value = fmpz_get_str(
                NULL, 10, fmpz_mat_entry(matrix, row, column));
            int success;

            if (value == NULL)
                return 0;
            success = fprintf(output_stream, "%s\n", value) >= 0;
            flint_free(value);
            if (!success)
                return 0;
        }
    }
    return 1;
}

int
normalforms_flint_run_protocol(
    FILE * input_stream,
    FILE * output_stream,
    FILE * error_stream)
{
    char * line = NULL;
    enum normalforms_kind kind;
    unsigned long rows_unsigned;
    unsigned long columns_unsigned;
    unsigned long entries_unsigned;
    unsigned long expected_entries;
    slong rows;
    slong columns;
    slong row;
    slong column;
    int read_status;
    int computation_status;
    int exit_status = 2;
    int input_initialized = 0;
    fmpz_mat_t input;
    fmpz_mat_t result;
    fmpz_mat_t u;
    fmpz_mat_t u_inverse;
    fmpz_mat_t v;
    fmpz_mat_t v_inverse;

    line = malloc(NORMALFORMS_MAX_LINE + 2UL);
    if (line == NULL)
    {
        fprintf(
            error_stream,
            "normalforms-flint-worker: allocation failure\n");
        return 2;
    }

    if (strcmp(normalforms_flint_version(),
            NORMALFORMS_FLINT_EXPECTED_VERSION) != 0)
    {
        fprintf(
            error_stream,
            "normalforms-flint-worker: expected FLINT %s, loaded %s\n",
            NORMALFORMS_FLINT_EXPECTED_VERSION,
            normalforms_flint_version());
        goto cleanup;
    }
    if (strcmp(gmp_version, "6.3.0") != 0)
    {
        fprintf(
            error_stream,
            "normalforms-flint-worker: expected GMP 6.3.0, loaded %s\n",
            gmp_version);
        goto cleanup;
    }
    if (strcmp(mpfr_get_version(), "4.2.2") != 0)
    {
        fprintf(
            error_stream,
            "normalforms-flint-worker: expected MPFR 4.2.2, loaded %s\n",
            mpfr_get_version());
        goto cleanup;
    }

    read_status =
        read_line(input_stream, line, NORMALFORMS_MAX_LINE + 2UL);
    if (read_status != 1 || strcmp(line, NORMALFORMS_PROTOCOL) != 0)
    {
        protocol_error(error_stream, "missing or invalid protocol header");
        goto cleanup;
    }

    read_status =
        read_line(input_stream, line, NORMALFORMS_MAX_LINE + 2UL);
    if (read_status != 1)
    {
        protocol_error(error_stream, "missing kind");
        goto cleanup;
    }
    if (strcmp(line, "kind hnf") == 0)
        kind = NORMALFORMS_KIND_HNF;
    else if (strcmp(line, "kind snf") == 0)
        kind = NORMALFORMS_KIND_SNF;
    else
    {
        protocol_error(error_stream, "kind must be hnf or snf");
        goto cleanup;
    }

    read_status =
        read_line(input_stream, line, NORMALFORMS_MAX_LINE + 2UL);
    if (read_status != 1
        || !parse_prefixed_unsigned(
            line,
            "rows ",
            NORMALFORMS_MAX_DIMENSION,
            &rows_unsigned))
    {
        protocol_error(error_stream, "invalid rows line");
        goto cleanup;
    }

    read_status =
        read_line(input_stream, line, NORMALFORMS_MAX_LINE + 2UL);
    if (read_status != 1
        || !parse_prefixed_unsigned(
            line,
            "cols ",
            NORMALFORMS_MAX_DIMENSION,
            &columns_unsigned))
    {
        protocol_error(error_stream, "invalid cols line");
        goto cleanup;
    }

    if (rows_unsigned != 0UL
        && columns_unsigned > ULONG_MAX / rows_unsigned)
    {
        protocol_error(error_stream, "matrix entry count overflows");
        goto cleanup;
    }
    expected_entries = rows_unsigned * columns_unsigned;
    if (expected_entries > NORMALFORMS_MAX_ENTRIES)
    {
        protocol_error(error_stream, "matrix has too many entries");
        goto cleanup;
    }

    read_status =
        read_line(input_stream, line, NORMALFORMS_MAX_LINE + 2UL);
    if (read_status != 1
        || !parse_prefixed_unsigned(
            line,
            "entries ",
            NORMALFORMS_MAX_ENTRIES,
            &entries_unsigned)
        || entries_unsigned != expected_entries)
    {
        protocol_error(
            error_stream,
            "entry count does not match dimensions");
        goto cleanup;
    }

    rows = (slong) rows_unsigned;
    columns = (slong) columns_unsigned;
    fmpz_mat_init(input, rows, columns);
    input_initialized = 1;

    for (row = 0; row < rows; row++)
    {
        for (column = 0; column < columns; column++)
        {
            read_status =
                read_line(input_stream, line, NORMALFORMS_MAX_LINE + 2UL);
            if (read_status != 1 || !canonical_integer(line))
            {
                protocol_error(
                    error_stream,
                    "matrix entry is not a canonical integer");
                goto cleanup;
            }
            if (fmpz_set_str(
                    fmpz_mat_entry(input, row, column), line, 10) != 0)
            {
                protocol_error(
                    error_stream,
                    "matrix entry could not be parsed");
                goto cleanup;
            }
        }
    }

    read_status =
        read_line(input_stream, line, NORMALFORMS_MAX_LINE + 2UL);
    if (read_status != 1 || strcmp(line, "end") != 0)
    {
        protocol_error(error_stream, "missing end marker");
        goto cleanup;
    }
    if (fgetc(input_stream) != EOF)
    {
        protocol_error(error_stream, "trailing input after end marker");
        goto cleanup;
    }

    fmpz_mat_init(result, rows, columns);
    fmpz_mat_init(u, rows, rows);
    fmpz_mat_init(u_inverse, rows, rows);

    if (kind == NORMALFORMS_KIND_HNF)
    {
        computation_status =
            normalforms_flint_hnf(result, u, u_inverse, input);
        if (computation_status != NORMALFORMS_FLINT_OK)
        {
            computation_error(error_stream, computation_status);
            exit_status = 3;
            goto clear_hnf;
        }

        if (fprintf(
                output_stream,
                "%s\nkind hnf\nflint %s\n",
                NORMALFORMS_PROTOCOL,
                normalforms_flint_version()) < 0
            || !write_matrix(output_stream, "input", input)
            || !write_matrix(output_stream, "U", u)
            || !write_matrix(output_stream, "UInverse", u_inverse)
            || !write_matrix(output_stream, "H", result)
            || fprintf(output_stream, "end\n") < 0
            || fflush(output_stream) != 0)
        {
            fprintf(
                error_stream,
                "normalforms-flint-worker: output failure\n");
            exit_status = 4;
            goto clear_hnf;
        }

        exit_status = 0;

clear_hnf:
        fmpz_mat_clear(u_inverse);
        fmpz_mat_clear(u);
        fmpz_mat_clear(result);
        goto cleanup;
    }

    fmpz_mat_init(v, columns, columns);
    fmpz_mat_init(v_inverse, columns, columns);
    computation_status =
        normalforms_flint_snf(
            result, u, u_inverse, v, v_inverse, input);
    if (computation_status != NORMALFORMS_FLINT_OK)
    {
        computation_error(error_stream, computation_status);
        exit_status = 3;
        goto clear_snf;
    }

    if (fprintf(
            output_stream,
            "%s\nkind snf\nflint %s\n",
            NORMALFORMS_PROTOCOL,
            normalforms_flint_version()) < 0
        || !write_matrix(output_stream, "input", input)
        || !write_matrix(output_stream, "U", u)
        || !write_matrix(output_stream, "UInverse", u_inverse)
        || !write_matrix(output_stream, "S", result)
        || !write_matrix(output_stream, "V", v)
        || !write_matrix(output_stream, "VInverse", v_inverse)
        || fprintf(output_stream, "end\n") < 0
        || fflush(output_stream) != 0)
    {
        fprintf(
            error_stream,
            "normalforms-flint-worker: output failure\n");
        exit_status = 4;
        goto clear_snf;
    }

    exit_status = 0;

clear_snf:
    fmpz_mat_clear(v_inverse);
    fmpz_mat_clear(v);
    fmpz_mat_clear(u_inverse);
    fmpz_mat_clear(u);
    fmpz_mat_clear(result);

cleanup:
    if (input_initialized)
        fmpz_mat_clear(input);
    free(line);
    flint_cleanup();
    return exit_status;
}

#ifndef NORMALFORMS_FLINT_NO_MAIN
int
main(void)
{
    return normalforms_flint_run_protocol(stdin, stdout, stderr);
}
#endif
