/*
 * Copyright (c) 2026 Junye Ji. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 */

#ifndef NORMALFORMS_PROTOCOL_H
#define NORMALFORMS_PROTOCOL_H

#include <stdio.h>

/*
 * Run one canonical normalforms.decimal/v1 request. The function owns none of
 * the streams and leaves closing them to the caller.
 */
int normalforms_flint_run_protocol(
    FILE * input_stream,
    FILE * output_stream,
    FILE * error_stream);

#endif
