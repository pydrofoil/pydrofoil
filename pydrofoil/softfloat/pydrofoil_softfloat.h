#ifndef PYDROFOIL_SOFTFLOAT_H
#define PYDROFOIL_SOFTFLOAT_H

#include <stdint.h>

RPY_EXPORTED uint64_t get_exception_flags();

RPY_EXPORTED uint64_t f16sqrt(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t f32sqrt(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t f64sqrt(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t f16tof32(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t f16tof64(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t f16toi32(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t f16toi64(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t f16toui32(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t f16toui64(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t f32tof16(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t f32tof64(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t f32toi32(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t f32toi64(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t f32toui32(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t f32toui64(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t f64tof16(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t f64tof32(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t f64toui64(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t f64toi32(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t f64toi64(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t f64toui32(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t i32tof16(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t i32tof32(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t i32tof64(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t i64tof16(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t i64tof32(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t i64tof64(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t ui32tof16(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t ui32tof32(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t ui32tof64(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t ui64tof16(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t ui64tof32(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t ui64tof64(uint64_t rm, uint64_t v1);
RPY_EXPORTED uint64_t f16add(uint64_t rm, uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f16sub(uint64_t rm, uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f16mul(uint64_t rm, uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f16div(uint64_t rm, uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f32add(uint64_t rm, uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f32sub(uint64_t rm, uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f32mul(uint64_t rm, uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f32div(uint64_t rm, uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f64add(uint64_t rm, uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f64sub(uint64_t rm, uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f64mul(uint64_t rm, uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f64div(uint64_t rm, uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f16eq(uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f16le(uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f16lt(uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f32eq(uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f32le(uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f32lt(uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f64eq(uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f64le(uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f64lt(uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f16le_quiet(uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f16lt_quiet(uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f32le_quiet(uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f32lt_quiet(uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f64le_quiet(uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f64lt_quiet(uint64_t v1, uint64_t v2);
RPY_EXPORTED uint64_t f16muladd(uint64_t rm, uint64_t v1, uint64_t v2, uint64_t v3);
RPY_EXPORTED uint64_t f32muladd(uint64_t rm, uint64_t v1, uint64_t v2, uint64_t v3);
RPY_EXPORTED uint64_t f64muladd(uint64_t rm, uint64_t v1, uint64_t v2, uint64_t v3);

#endif

