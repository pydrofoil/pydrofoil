#include <stdint.h>
#include "softfloat.h"
#include "softfloat_types.h"

uint64_t get_exception_flags() {
    return (uint64_t)softfloat_exceptionFlags;
}

uint64_t f16sqrt(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float16_t fv1 = { (uint16_t)v1 };
    float16_t res = f16_sqrt(fv1);
    return (uint64_t)res.v & 0xffff;
}

uint64_t f32sqrt(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float32_t fv1 = { (uint32_t)v1 };
    float32_t res = f32_sqrt(fv1);
    return (uint64_t)res.v & 0xffffffff;
}

uint64_t f64sqrt(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float64_t fv1 = { (uint64_t)v1 };
    float64_t res = f64_sqrt(fv1);
    return (uint64_t)res.v;
}

uint64_t f16tof32(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float16_t fv1 = { (uint16_t)v1 };
    float32_t res = f16_to_f32(fv1);
    return (uint64_t)res.v & 0xffffffff;
}

uint64_t f16tof64(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float16_t fv1 = { (uint16_t)v1 };
    float64_t res = f16_to_f64(fv1);
    return (uint64_t)res.v;
}

uint64_t f16toi32(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float16_t fv1 = { (uint16_t)v1 };
    return (uint64_t)f16_to_i32(fv1, (uint_fast8_t)rm, true) & 0xffffffff;
}

uint64_t f16toi64(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float16_t fv1 = { (uint16_t)v1 };
    return (uint64_t)f16_to_i64(fv1, (uint_fast8_t)rm, true);
}

uint64_t f16toui32(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float16_t fv1 = { (uint16_t)v1 };
    return (uint64_t)f16_to_ui32(fv1, (uint_fast8_t)rm, true) & 0xffffffff;
}

uint64_t f16toui64(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float16_t fv1 = { (uint16_t)v1 };
    return (uint64_t)f16_to_ui64(fv1, (uint_fast8_t)rm, true);
}

uint64_t f32tof16(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float32_t fv1 = { (uint32_t)v1 };
    float16_t res = f32_to_f16(fv1);
    return (uint64_t)res.v & 0xffff;
}

uint64_t f32tof64(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float32_t fv1 = { (uint32_t)v1 };
    float64_t res = f32_to_f64(fv1);
    return (uint64_t)res.v;
}

uint64_t f32toi32(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float32_t fv1 = { (uint32_t)v1 };
    return (uint64_t)f32_to_i32(fv1, (uint_fast8_t)rm, true) & 0xffffffff;
}

uint64_t f32toi64(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float32_t fv1 = { (uint32_t)v1 };
    return (uint64_t)f32_to_i64(fv1, (uint_fast8_t)rm, true);
}

uint64_t f32toui32(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float32_t fv1 = { (uint32_t)v1 };
    return (uint64_t)f32_to_ui32(fv1, (uint_fast8_t)rm, true) & 0xffffffff;
}

uint64_t f32toui64(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float32_t fv1 = { (uint32_t)v1 };
    return (uint64_t)f32_to_ui64(fv1, (uint_fast8_t)rm, true);
}

uint64_t f64tof16(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float64_t fv1 = { (uint64_t)v1 };
    float16_t res = f64_to_f16(fv1);
    return (uint64_t)res.v & 0xffff;
}

uint64_t f64tof32(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float64_t fv1 = { (uint64_t)v1 };
    float32_t res = f64_to_f32(fv1);
    return (uint64_t)res.v & 0xffffffff;
}

uint64_t f64toui64(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float64_t fv1 = { (uint64_t)v1 };
    return (uint64_t)f64_to_ui64(fv1, (uint_fast8_t)rm, true);
}

uint64_t f64toi32(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float64_t fv1 = { (uint64_t)v1 };
    return (uint64_t)f64_to_i32(fv1, (uint_fast8_t)rm, true) & 0xffffffff;
}

uint64_t f64toi64(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float64_t fv1 = { (uint64_t)v1 };
    return (uint64_t)f64_to_i64(fv1, (uint_fast8_t)rm, true);
}

uint64_t f64toui32(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float64_t fv1 = { (uint64_t)v1 };
    return (uint64_t)f64_to_ui32(fv1, (uint_fast8_t)rm, true) & 0xffffffff;
}

uint64_t i32tof16(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float16_t res = i32_to_f16((int32_t)v1);
    return (uint64_t)res.v & 0xffff;
}

uint64_t i32tof32(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float32_t res = i32_to_f32((int32_t)v1);
    return (uint64_t)res.v & 0xffffffff;
}

uint64_t i32tof64(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float64_t res = i32_to_f64((int32_t)v1);
    return (uint64_t)res.v;
}

uint64_t i64tof16(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float16_t res = i64_to_f16((int64_t)v1);
    return (uint64_t)res.v & 0xffff;
}

uint64_t i64tof32(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float32_t res = i64_to_f32((int64_t)v1);
    return (uint64_t)res.v & 0xffffffff;
}

uint64_t i64tof64(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float64_t res = i64_to_f64((int64_t)v1);
    return (uint64_t)res.v;
}

uint64_t ui32tof16(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float16_t res = ui32_to_f16((uint32_t)v1);
    return (uint64_t)res.v & 0xffff;
}

uint64_t ui32tof32(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float32_t res = ui32_to_f32((uint32_t)v1);
    return (uint64_t)res.v & 0xffffffff;
}

uint64_t ui32tof64(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float64_t res = ui32_to_f64((uint32_t)v1);
    return (uint64_t)res.v;
}

uint64_t ui64tof16(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float16_t res = ui64_to_f16((uint64_t)v1);
    return (uint64_t)res.v & 0xffff;
}

uint64_t ui64tof32(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float32_t res = ui64_to_f32((uint64_t)v1);
    return (uint64_t)res.v & 0xffffffff;
}

uint64_t ui64tof64(uint64_t rm, uint64_t v1) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float64_t res = ui64_to_f64((uint64_t)v1);
    return (uint64_t)res.v;
}

uint64_t f16add(uint64_t rm, uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float16_t fv1 = { (uint16_t)v1 };
    float16_t fv2 = { (uint16_t)v2 };
    float16_t res = f16_add(fv1, fv2);
    return (uint64_t)res.v & 0xffff;
}

uint64_t f16sub(uint64_t rm, uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float16_t fv1 = { (uint16_t)v1 };
    float16_t fv2 = { (uint16_t)v2 };
    float16_t res = f16_sub(fv1, fv2);
    return (uint64_t)res.v & 0xffff;
}

uint64_t f16mul(uint64_t rm, uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float16_t fv1 = { (uint16_t)v1 };
    float16_t fv2 = { (uint16_t)v2 };
    float16_t res = f16_mul(fv1, fv2);
    return (uint64_t)res.v & 0xffff;
}

uint64_t f16div(uint64_t rm, uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float16_t fv1 = { (uint16_t)v1 };
    float16_t fv2 = { (uint16_t)v2 };
    float16_t res = f16_div(fv1, fv2);
    return (uint64_t)res.v & 0xffff;
}

uint64_t f32add(uint64_t rm, uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float32_t fv1 = { (uint32_t)v1 };
    float32_t fv2 = { (uint32_t)v2 };
    float32_t res = f32_add(fv1, fv2);
    return (uint64_t)res.v & 0xffffffff;
}

uint64_t f32sub(uint64_t rm, uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float32_t fv1 = { (uint32_t)v1 };
    float32_t fv2 = { (uint32_t)v2 };
    float32_t res = f32_sub(fv1, fv2);
    return (uint64_t)res.v & 0xffffffff;
}

uint64_t f32mul(uint64_t rm, uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float32_t fv1 = { (uint32_t)v1 };
    float32_t fv2 = { (uint32_t)v2 };
    float32_t res = f32_mul(fv1, fv2);
    return (uint64_t)res.v & 0xffffffff;
}

uint64_t f32div(uint64_t rm, uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float32_t fv1 = { (uint32_t)v1 };
    float32_t fv2 = { (uint32_t)v2 };
    float32_t res = f32_div(fv1, fv2);
    return (uint64_t)res.v & 0xffffffff;
}

uint64_t f64add(uint64_t rm, uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float64_t fv1 = { (uint64_t)v1 };
    float64_t fv2 = { (uint64_t)v2 };
    float64_t res = f64_add(fv1, fv2);
    return (uint64_t)res.v;
}

uint64_t f64sub(uint64_t rm, uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float64_t fv1 = { (uint64_t)v1 };
    float64_t fv2 = { (uint64_t)v2 };
    float64_t res = f64_sub(fv1, fv2);
    return (uint64_t)res.v;
}

uint64_t f64mul(uint64_t rm, uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float64_t fv1 = { (uint64_t)v1 };
    float64_t fv2 = { (uint64_t)v2 };
    float64_t res = f64_mul(fv1, fv2);
    return (uint64_t)res.v;
}

uint64_t f64div(uint64_t rm, uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float64_t fv1 = { (uint64_t)v1 };
    float64_t fv2 = { (uint64_t)v2 };
    float64_t res = f64_div(fv1, fv2);
    return (uint64_t)res.v;
}

uint64_t f16eq(uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    float16_t fv1 = { (uint16_t)v1 };
    float16_t fv2 = { (uint16_t)v2 };
    return (uint64_t)f16_eq(fv1, fv2) & 0xffff;
}

uint64_t f16le(uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    float16_t fv1 = { (uint16_t)v1 };
    float16_t fv2 = { (uint16_t)v2 };
    return (uint64_t)f16_le(fv1, fv2) & 0xffff;
}

uint64_t f16lt(uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    float16_t fv1 = { (uint16_t)v1 };
    float16_t fv2 = { (uint16_t)v2 };
    return (uint64_t)f16_lt(fv1, fv2) & 0xffff;
}

uint64_t f32eq(uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    float32_t fv1 = { (uint32_t)v1 };
    float32_t fv2 = { (uint32_t)v2 };
    return (uint64_t)f32_eq(fv1, fv2) & 0xffffffff;
}

uint64_t f32le(uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    float32_t fv1 = { (uint32_t)v1 };
    float32_t fv2 = { (uint32_t)v2 };
    return (uint64_t)f32_le(fv1, fv2) & 0xffffffff;
}

uint64_t f32lt(uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    float32_t fv1 = { (uint32_t)v1 };
    float32_t fv2 = { (uint32_t)v2 };
    return (uint64_t)f32_lt(fv1, fv2) & 0xffffffff;
}

uint64_t f64eq(uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    float64_t fv1 = { (uint64_t)v1 };
    float64_t fv2 = { (uint64_t)v2 };
    return (uint64_t)f64_eq(fv1, fv2);
}

uint64_t f64le(uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    float64_t fv1 = { (uint64_t)v1 };
    float64_t fv2 = { (uint64_t)v2 };
    return (uint64_t)f64_le(fv1, fv2);
}

uint64_t f64lt(uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    float64_t fv1 = { (uint64_t)v1 };
    float64_t fv2 = { (uint64_t)v2 };
    return (uint64_t)f64_lt(fv1, fv2);
}

uint64_t f16le_quiet(uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    float16_t fv1 = { (uint16_t)v1 };
    float16_t fv2 = { (uint16_t)v2 };
    return (uint64_t)f16_le_quiet(fv1, fv2) & 0xffff;
}

uint64_t f16lt_quiet(uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    float16_t fv1 = { (uint16_t)v1 };
    float16_t fv2 = { (uint16_t)v2 };
    return (uint64_t)f16_lt_quiet(fv1, fv2) & 0xffff;
}

uint64_t f32le_quiet(uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    float32_t fv1 = { (uint32_t)v1 };
    float32_t fv2 = { (uint32_t)v2 };
    return (uint64_t)f32_le_quiet(fv1, fv2) & 0xffffffff;
}

uint64_t f32lt_quiet(uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    float32_t fv1 = { (uint32_t)v1 };
    float32_t fv2 = { (uint32_t)v2 };
    return (uint64_t)f32_lt_quiet(fv1, fv2) & 0xffffffff;
}

uint64_t f64le_quiet(uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    float64_t fv1 = { (uint64_t)v1 };
    float64_t fv2 = { (uint64_t)v2 };
    return (uint64_t)f64_le_quiet(fv1, fv2);
}

uint64_t f64lt_quiet(uint64_t v1, uint64_t v2) {
    softfloat_exceptionFlags = 0;
    float64_t fv1 = { (uint64_t)v1 };
    float64_t fv2 = { (uint64_t)v2 };
    return (uint64_t)f64_lt_quiet(fv1, fv2);
}

uint64_t f16muladd(uint64_t rm, uint64_t v1, uint64_t v2, uint64_t v3) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float16_t fv1 = { (uint16_t)v1 };
    float16_t fv2 = { (uint16_t)v2 };
    float16_t fv3 = { (uint16_t)v3 };
    float16_t res = f16_mulAdd(fv1, fv2, fv3);
    return (uint64_t)res.v & 0xffff;
}

uint64_t f32muladd(uint64_t rm, uint64_t v1, uint64_t v2, uint64_t v3) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float32_t fv1 = { (uint32_t)v1 };
    float32_t fv2 = { (uint32_t)v2 };
    float32_t fv3 = { (uint32_t)v3 };
    float32_t res = f32_mulAdd(fv1, fv2, fv3);
    return (uint64_t)res.v & 0xffffffff;
}

uint64_t f64muladd(uint64_t rm, uint64_t v1, uint64_t v2, uint64_t v3) {
    softfloat_exceptionFlags = 0;
    softfloat_roundingMode = (uint_fast8_t)rm;
    float64_t fv1 = { (uint64_t)v1 };
    float64_t fv2 = { (uint64_t)v2 };
    float64_t fv3 = { (uint64_t)v3 };
    float64_t res = f64_mulAdd(fv1, fv2, fv3);
    return (uint64_t)res.v;
}

