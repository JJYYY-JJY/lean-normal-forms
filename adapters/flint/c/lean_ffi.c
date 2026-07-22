/*
 * Copyright (c) 2026 Junye Ji. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 */

#define _GNU_SOURCE

#include "normalforms_protocol.h"

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <lean/lean.h>

static lean_obj_res
io_except_string(unsigned int tag, const char * value, size_t size)
{
    lean_object * payload =
        lean_mk_string_from_bytes(value, size);
    lean_object * result = lean_alloc_ctor(tag, 1, 0);

    lean_ctor_set(result, 0, payload);
    return lean_io_result_mk_ok(result);
}

static lean_obj_res
io_except_error_literal(const char * value)
{
    return io_except_string(0, value, strlen(value));
}

/*
 * The Lean declaration uses a borrowed String argument. Copy it before
 * fmemopen so libc never receives a writable pointer into Lean-managed data.
 * The result is IO (Except String String): protocol/computation failures are
 * data errors, not trusted IO exceptions.
 */
LEAN_EXPORT lean_obj_res
normalforms_flint_ffi_run(b_lean_obj_arg request)
{
    size_t request_object_size = lean_string_size(request);
    size_t request_size;
    char * request_copy = NULL;
    char * output = NULL;
    char * error = NULL;
    size_t output_size = 0;
    size_t error_size = 0;
    FILE * input_stream = NULL;
    FILE * output_stream = NULL;
    FILE * error_stream = NULL;
    int status;
    int close_failed = 0;
    lean_obj_res result;

    if (request_object_size == 0)
        return io_except_error_literal("invalid Lean string representation");
    request_size = request_object_size - 1;

    request_copy = malloc(request_size + 1);
    if (request_copy == NULL)
        return io_except_error_literal("FFI request allocation failed");
    memcpy(request_copy, lean_string_cstr(request), request_size);
    request_copy[request_size] = '\0';

    input_stream = fmemopen(request_copy, request_size, "r");
    if (input_stream == NULL)
    {
        free(request_copy);
        return io_except_error_literal("FFI input stream creation failed");
    }
    output_stream = open_memstream(&output, &output_size);
    if (output_stream == NULL)
    {
        fclose(input_stream);
        free(request_copy);
        return io_except_error_literal("FFI output stream creation failed");
    }
    error_stream = open_memstream(&error, &error_size);
    if (error_stream == NULL)
    {
        fclose(output_stream);
        fclose(input_stream);
        free(output);
        free(request_copy);
        return io_except_error_literal("FFI error stream creation failed");
    }

    status = normalforms_flint_run_protocol(
        input_stream, output_stream, error_stream);

    if (fclose(error_stream) != 0)
        close_failed = 1;
    if (fclose(output_stream) != 0)
        close_failed = 1;
    if (fclose(input_stream) != 0)
        close_failed = 1;
    free(request_copy);

    if (close_failed)
    {
        free(error);
        free(output);
        return io_except_error_literal("FFI memory stream close failed");
    }

    if (status == 0 && error_size == 0)
    {
        result = io_except_string(1, output, output_size);
    }
    else if (error_size != 0)
    {
        result = io_except_string(0, error, error_size);
    }
    else
    {
        char fallback[96];
        int rendered = snprintf(
            fallback,
            sizeof(fallback),
            "FLINT protocol failed with status %d and no diagnostic",
            status);
        size_t fallback_size =
            rendered > 0 && (size_t) rendered < sizeof(fallback)
                ? (size_t) rendered
                : strlen("FLINT protocol failed without a diagnostic");
        const char * fallback_value =
            rendered > 0 && (size_t) rendered < sizeof(fallback)
                ? fallback
                : "FLINT protocol failed without a diagnostic";

        result = io_except_string(0, fallback_value, fallback_size);
    }

    free(error);
    free(output);
    return result;
}
