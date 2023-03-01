#include "softfloat.h"
#include "softfloat_types.h"

uint32_t f32add(uint_fast8_t rm, uint32_t v1, uint32_t v2) {
    softfloat_roundingMode = rm;
    float32_t fv1 = { v1 };
    float32_t fv2 = { v2 };
    float32_t res = f32_add(fv1, fv2);
    return res.v;
}

