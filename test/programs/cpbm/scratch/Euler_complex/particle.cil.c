/* Generated by CIL v. 1.3.7 */
/* print_CIL_Input is true */

#line 60 "particle.h"
struct __anonstruct_parm_context_2 {
   int particles ;
   void *pos_v ;
   void *vel_v ;
   float *inv_mass ;
   float dt ;
};
#line 60 "particle.h"
typedef struct __anonstruct_parm_context_2 parm_context;
#line 108 "particle.c"
struct float4_s {
   float data[4] ;
};
#line 108 "particle.c"
typedef struct float4_s float4;
#line 203 "../spu_mfcio.h"
extern void mfc_put(void volatile   *ls , unsigned int ea , unsigned int size , unsigned int tag ,
                    unsigned int tid , unsigned int rid ) ;
#line 211
extern void mfc_get(void volatile   *ls , unsigned int ea , unsigned int size , unsigned int tag ,
                    unsigned int tid , unsigned int rid ) ;
#line 213
extern void mfc_getb(void volatile   *ls , unsigned int ea , unsigned int size , unsigned int tag ,
                     unsigned int tid , unsigned int rid ) ;
#line 252
extern void mfc_write_tag_mask(unsigned int mask ) ;
#line 270
extern void mfc_read_tag_status_all() ;
#line 116 "particle.c"
parm_context volatile   ctx  ;
#line 117 "particle.c"
float4 volatile   pos[2][1024]  __attribute__((__aligned__(128)))  ;
#line 118 "particle.c"
float4 volatile   vel[2][1024]  __attribute__((__aligned__(128)))  ;
#line 119 "particle.c"
float4 volatile   inv_mass[2][256]  __attribute__((__aligned__(128)))  ;
#line 211
extern int __VERIFIER_nondet_int() ;
#line 211
extern int ( /* missing proto */  __CROVER_ndet_int)() ;
#line 226
extern int ( /* missing proto */  assert)() ;
#line 189 "particle.c"
int spu_main(unsigned long long spu_id  __attribute__((__unused__)) , unsigned long long argv ) 
{ int buffer ;
  int next_buffer ;
  int cnt ;
  int next_cnt ;
  unsigned int left ;
  float time ;
  float dt ;
  float4 volatile   *ctx_pos_v ;
  float4 volatile   *ctx_vel_v ;
  float4 volatile   *next_ctx_pos_v ;
  float4 volatile   *next_ctx_vel_v ;
  float volatile   *ctx_inv_mass ;
  float volatile   *next_ctx_inv_mass ;
  unsigned int tags[2] ;
  int state ;
  int tmp ;
  int tmp___0 ;
  int tmp___1 ;
  int tmp___2 ;
  int tmp___3 ;
  int tmp___4 ;
  unsigned long __cil_tmp25 ;
  unsigned long __cil_tmp26 ;
  unsigned long __cil_tmp27 ;
  unsigned long __cil_tmp28 ;
  unsigned long __cil_tmp29 ;
  unsigned long __cil_tmp30 ;
  unsigned int __cil_tmp31 ;
  int __cil_tmp32 ;
  unsigned int __cil_tmp33 ;
  void *__cil_tmp34 ;
  void volatile   *__cil_tmp35 ;
  unsigned int __cil_tmp36 ;
  unsigned int __cil_tmp37 ;
  unsigned long __cil_tmp38 ;
  unsigned long __cil_tmp39 ;
  unsigned int __cil_tmp40 ;
  parm_context volatile   *__cil_tmp41 ;
  unsigned long __cil_tmp42 ;
  unsigned long __cil_tmp43 ;
  unsigned long __cil_tmp44 ;
  unsigned long __cil_tmp45 ;
  unsigned long __cil_tmp46 ;
  float volatile   __cil_tmp47 ;
  float __cil_tmp48 ;
  unsigned long __cil_tmp49 ;
  unsigned long __cil_tmp50 ;
  unsigned int __cil_tmp51 ;
  int __cil_tmp52 ;
  unsigned long __cil_tmp53 ;
  unsigned long __cil_tmp54 ;
  unsigned int __cil_tmp55 ;
  int __cil_tmp56 ;
  parm_context volatile   *__cil_tmp57 ;
  int volatile   __cil_tmp58 ;
  unsigned long __cil_tmp59 ;
  void * volatile  __cil_tmp60 ;
  unsigned long __cil_tmp61 ;
  void * volatile  __cil_tmp62 ;
  unsigned long __cil_tmp63 ;
  float * volatile  __cil_tmp64 ;
  unsigned long __cil_tmp65 ;
  unsigned long __cil_tmp66 ;
  float4 volatile   (*__cil_tmp67)[1024] ;
  void *__cil_tmp68 ;
  void volatile   *__cil_tmp69 ;
  unsigned int __cil_tmp70 ;
  unsigned long __cil_tmp71 ;
  unsigned long __cil_tmp72 ;
  unsigned int __cil_tmp73 ;
  unsigned long __cil_tmp74 ;
  unsigned long __cil_tmp75 ;
  unsigned int __cil_tmp76 ;
  unsigned long __cil_tmp77 ;
  unsigned long __cil_tmp78 ;
  float4 volatile   (*__cil_tmp79)[1024] ;
  void *__cil_tmp80 ;
  void volatile   *__cil_tmp81 ;
  unsigned int __cil_tmp82 ;
  unsigned long __cil_tmp83 ;
  unsigned long __cil_tmp84 ;
  unsigned int __cil_tmp85 ;
  unsigned long __cil_tmp86 ;
  unsigned long __cil_tmp87 ;
  unsigned int __cil_tmp88 ;
  unsigned long __cil_tmp89 ;
  unsigned long __cil_tmp90 ;
  float4 volatile   (*__cil_tmp91)[256] ;
  void *__cil_tmp92 ;
  void volatile   *__cil_tmp93 ;
  unsigned int __cil_tmp94 ;
  unsigned long __cil_tmp95 ;
  unsigned long __cil_tmp96 ;
  unsigned int __cil_tmp97 ;
  unsigned long __cil_tmp98 ;
  unsigned long __cil_tmp99 ;
  unsigned int __cil_tmp100 ;
  unsigned int __cil_tmp101 ;
  unsigned int __cil_tmp102 ;
  unsigned long __cil_tmp103 ;
  unsigned long __cil_tmp104 ;
  unsigned long __cil_tmp105 ;
  unsigned long __cil_tmp106 ;
  float4 volatile   *__cil_tmp107 ;
  void *__cil_tmp108 ;
  void volatile   *__cil_tmp109 ;
  unsigned int __cil_tmp110 ;
  unsigned long __cil_tmp111 ;
  unsigned long __cil_tmp112 ;
  unsigned int __cil_tmp113 ;
  unsigned long __cil_tmp114 ;
  unsigned long __cil_tmp115 ;
  unsigned int __cil_tmp116 ;
  unsigned long __cil_tmp117 ;
  unsigned long __cil_tmp118 ;
  unsigned long __cil_tmp119 ;
  unsigned long __cil_tmp120 ;
  float4 volatile   *__cil_tmp121 ;
  void *__cil_tmp122 ;
  void volatile   *__cil_tmp123 ;
  unsigned int __cil_tmp124 ;
  unsigned long __cil_tmp125 ;
  unsigned long __cil_tmp126 ;
  unsigned int __cil_tmp127 ;
  unsigned long __cil_tmp128 ;
  unsigned long __cil_tmp129 ;
  unsigned int __cil_tmp130 ;
  unsigned long __cil_tmp131 ;
  unsigned long __cil_tmp132 ;
  unsigned long __cil_tmp133 ;
  unsigned long __cil_tmp134 ;
  float4 volatile   *__cil_tmp135 ;
  void *__cil_tmp136 ;
  void volatile   *__cil_tmp137 ;
  unsigned int __cil_tmp138 ;
  unsigned long __cil_tmp139 ;
  unsigned long __cil_tmp140 ;
  unsigned int __cil_tmp141 ;
  unsigned long __cil_tmp142 ;
  unsigned long __cil_tmp143 ;
  unsigned int __cil_tmp144 ;
  unsigned long __cil_tmp145 ;
  unsigned long __cil_tmp146 ;
  unsigned int __cil_tmp147 ;
  int __cil_tmp148 ;
  unsigned int __cil_tmp149 ;
  unsigned long __cil_tmp150 ;
  unsigned long __cil_tmp151 ;
  unsigned long __cil_tmp152 ;
  unsigned long __cil_tmp153 ;
  float4 volatile   *__cil_tmp154 ;
  void *__cil_tmp155 ;
  void volatile   *__cil_tmp156 ;
  unsigned int __cil_tmp157 ;
  unsigned long __cil_tmp158 ;
  unsigned long __cil_tmp159 ;
  unsigned int __cil_tmp160 ;
  unsigned long __cil_tmp161 ;
  unsigned long __cil_tmp162 ;
  unsigned int __cil_tmp163 ;
  unsigned long __cil_tmp164 ;
  unsigned long __cil_tmp165 ;
  unsigned long __cil_tmp166 ;
  unsigned long __cil_tmp167 ;
  float4 volatile   *__cil_tmp168 ;
  void *__cil_tmp169 ;
  void volatile   *__cil_tmp170 ;
  unsigned int __cil_tmp171 ;
  unsigned long __cil_tmp172 ;
  unsigned long __cil_tmp173 ;
  unsigned int __cil_tmp174 ;
  unsigned long __cil_tmp175 ;
  unsigned long __cil_tmp176 ;
  unsigned int __cil_tmp177 ;
  unsigned long __cil_tmp178 ;
  unsigned long __cil_tmp179 ;
  unsigned int __cil_tmp180 ;
  int __cil_tmp181 ;
  unsigned int __cil_tmp182 ;
  unsigned long __cil_tmp183 ;
  unsigned long __cil_tmp184 ;
  unsigned long __cil_tmp185 ;
  unsigned long __cil_tmp186 ;
  float4 volatile   *__cil_tmp187 ;
  void *__cil_tmp188 ;
  void volatile   *__cil_tmp189 ;
  unsigned int __cil_tmp190 ;
  unsigned long __cil_tmp191 ;
  unsigned long __cil_tmp192 ;
  unsigned int __cil_tmp193 ;
  unsigned long __cil_tmp194 ;
  unsigned long __cil_tmp195 ;
  unsigned int __cil_tmp196 ;
  unsigned long __cil_tmp197 ;
  unsigned long __cil_tmp198 ;
  unsigned long __cil_tmp199 ;
  unsigned long __cil_tmp200 ;
  float4 volatile   *__cil_tmp201 ;
  void *__cil_tmp202 ;
  void volatile   *__cil_tmp203 ;
  unsigned int __cil_tmp204 ;
  unsigned long __cil_tmp205 ;
  unsigned long __cil_tmp206 ;
  unsigned int __cil_tmp207 ;
  unsigned long __cil_tmp208 ;
  unsigned long __cil_tmp209 ;
  unsigned int __cil_tmp210 ;
  unsigned long __cil_tmp211 ;
  unsigned long __cil_tmp212 ;
  unsigned int __cil_tmp213 ;
  int __cil_tmp214 ;
  unsigned int __cil_tmp215 ;

  {
  {
#line 204
  __cil_tmp25 = 0 * 4UL;
#line 204
  __cil_tmp26 = (unsigned long )(tags) + __cil_tmp25;
#line 204
  *((unsigned int *)__cil_tmp26) = 0U;
#line 205
  __cil_tmp27 = 1 * 4UL;
#line 205
  __cil_tmp28 = (unsigned long )(tags) + __cil_tmp27;
#line 205
  *((unsigned int *)__cil_tmp28) = 1U;
#line 209
  __cil_tmp29 = 0 * 4UL;
#line 209
  __cil_tmp30 = (unsigned long )(tags) + __cil_tmp29;
#line 209
  __cil_tmp31 = *((unsigned int *)__cil_tmp30);
#line 209
  __cil_tmp32 = 1 << __cil_tmp31;
#line 209
  __cil_tmp33 = (unsigned int )__cil_tmp32;
#line 209
  mfc_write_tag_mask(__cil_tmp33);
#line 210
  __cil_tmp34 = (void *)(& ctx);
#line 210
  __cil_tmp35 = (void volatile   *)__cil_tmp34;
#line 210
  __cil_tmp36 = (unsigned int )argv;
#line 210
  __cil_tmp37 = (unsigned int )40UL;
#line 210
  __cil_tmp38 = 0 * 4UL;
#line 210
  __cil_tmp39 = (unsigned long )(tags) + __cil_tmp38;
#line 210
  __cil_tmp40 = *((unsigned int *)__cil_tmp39);
#line 210
  mfc_get(__cil_tmp35, __cil_tmp36, __cil_tmp37, __cil_tmp40, 0U, 0U);
#line 211
  tmp = __VERIFIER_nondet_int();
#line 211
  __cil_tmp41 = & ctx;
#line 211
  *((int volatile   *)__cil_tmp41) = (int volatile   )tmp;
#line 211
  tmp___0 = __VERIFIER_nondet_int();
#line 211
  __cil_tmp42 = (unsigned long )(& ctx) + 8;
#line 211
  *((void * volatile  *)__cil_tmp42) = (void * volatile  )tmp___0;
#line 211
  tmp___1 = __VERIFIER_nondet_int();
#line 211
  __cil_tmp43 = (unsigned long )(& ctx) + 16;
#line 211
  *((void * volatile  *)__cil_tmp43) = (void * volatile  )tmp___1;
#line 211
  tmp___2 = __CROVER_ndet_int();
#line 211
  __cil_tmp44 = (unsigned long )(& ctx) + 24;
#line 211
  *((float * volatile  *)__cil_tmp44) = (float * volatile  )tmp___2;
#line 211
  tmp___3 = __VERIFIER_nondet_int();
#line 211
  __cil_tmp45 = (unsigned long )(& ctx) + 32;
#line 211
  *((float volatile   *)__cil_tmp45) = (float volatile   )tmp___3;
#line 212
  mfc_read_tag_status_all();
#line 214
  __cil_tmp46 = (unsigned long )(& ctx) + 32;
#line 214
  __cil_tmp47 = *((float volatile   *)__cil_tmp46);
#line 214
  dt = (float )__cil_tmp47;
#line 220
  time = (float )0;
#line 222
  state = 0;
  }
  {
#line 224
  while (1) {
    while_continue: /* CIL Label */ ;
    {
#line 224
    __cil_tmp48 = (float )10;
#line 224
    if (time < __cil_tmp48) {

    } else {
#line 224
      goto while_break;
    }
    }
    {
#line 226
    __cil_tmp49 = 0 * 4UL;
#line 226
    __cil_tmp50 = (unsigned long )(tags) + __cil_tmp49;
#line 226
    __cil_tmp51 = *((unsigned int *)__cil_tmp50);
#line 226
    __cil_tmp52 = __cil_tmp51 == 0U;
#line 226
    assert(__cil_tmp52);
#line 227
    __cil_tmp53 = 1 * 4UL;
#line 227
    __cil_tmp54 = (unsigned long )(tags) + __cil_tmp53;
#line 227
    __cil_tmp55 = *((unsigned int *)__cil_tmp54);
#line 227
    __cil_tmp56 = __cil_tmp55 == 1U;
#line 227
    assert(__cil_tmp56);
    }
#line 229
    if (state == 0) {
#line 232
      __cil_tmp57 = & ctx;
#line 232
      __cil_tmp58 = *((int volatile   *)__cil_tmp57);
#line 232
      left = (unsigned int )__cil_tmp58;
#line 234
      if (left < 1024U) {
#line 234
        cnt = (int )left;
      } else {
#line 234
        cnt = 1024;
      }
      {
#line 236
      __cil_tmp59 = (unsigned long )(& ctx) + 8;
#line 236
      __cil_tmp60 = *((void * volatile  *)__cil_tmp59);
#line 236
      ctx_pos_v = (float4 volatile   *)__cil_tmp60;
#line 237
      __cil_tmp61 = (unsigned long )(& ctx) + 16;
#line 237
      __cil_tmp62 = *((void * volatile  *)__cil_tmp61);
#line 237
      ctx_vel_v = (float4 volatile   *)__cil_tmp62;
#line 238
      __cil_tmp63 = (unsigned long )(& ctx) + 24;
#line 238
      __cil_tmp64 = *((float * volatile  *)__cil_tmp63);
#line 238
      ctx_inv_mass = (float volatile   *)__cil_tmp64;
#line 241
      buffer = 0;
#line 242
      __cil_tmp65 = 0 * 16384UL;
#line 242
      __cil_tmp66 = (unsigned long )(pos) + __cil_tmp65;
#line 242
      __cil_tmp67 = (float4 volatile   (*)[1024])__cil_tmp66;
#line 242
      __cil_tmp68 = (void *)__cil_tmp67;
#line 242
      __cil_tmp69 = (void volatile   *)__cil_tmp68;
#line 242
      __cil_tmp70 = (unsigned int )ctx_pos_v;
#line 242
      __cil_tmp71 = (unsigned long )cnt;
#line 242
      __cil_tmp72 = __cil_tmp71 * 16UL;
#line 242
      __cil_tmp73 = (unsigned int )__cil_tmp72;
#line 242
      __cil_tmp74 = 0 * 4UL;
#line 242
      __cil_tmp75 = (unsigned long )(tags) + __cil_tmp74;
#line 242
      __cil_tmp76 = *((unsigned int *)__cil_tmp75);
#line 242
      mfc_getb(__cil_tmp69, __cil_tmp70, __cil_tmp73, __cil_tmp76, 0U, 0U);
#line 243
      __cil_tmp77 = 0 * 16384UL;
#line 243
      __cil_tmp78 = (unsigned long )(vel) + __cil_tmp77;
#line 243
      __cil_tmp79 = (float4 volatile   (*)[1024])__cil_tmp78;
#line 243
      __cil_tmp80 = (void *)__cil_tmp79;
#line 243
      __cil_tmp81 = (void volatile   *)__cil_tmp80;
#line 243
      __cil_tmp82 = (unsigned int )ctx_vel_v;
#line 243
      __cil_tmp83 = (unsigned long )cnt;
#line 243
      __cil_tmp84 = __cil_tmp83 * 16UL;
#line 243
      __cil_tmp85 = (unsigned int )__cil_tmp84;
#line 243
      __cil_tmp86 = 0 * 4UL;
#line 243
      __cil_tmp87 = (unsigned long )(tags) + __cil_tmp86;
#line 243
      __cil_tmp88 = *((unsigned int *)__cil_tmp87);
#line 243
      mfc_get(__cil_tmp81, __cil_tmp82, __cil_tmp85, __cil_tmp88, 0U, 0U);
#line 244
      __cil_tmp89 = 0 * 4096UL;
#line 244
      __cil_tmp90 = (unsigned long )(inv_mass) + __cil_tmp89;
#line 244
      __cil_tmp91 = (float4 volatile   (*)[256])__cil_tmp90;
#line 244
      __cil_tmp92 = (void *)__cil_tmp91;
#line 244
      __cil_tmp93 = (void volatile   *)__cil_tmp92;
#line 244
      __cil_tmp94 = (unsigned int )ctx_inv_mass;
#line 244
      __cil_tmp95 = (unsigned long )cnt;
#line 244
      __cil_tmp96 = __cil_tmp95 * 4UL;
#line 244
      __cil_tmp97 = (unsigned int )__cil_tmp96;
#line 244
      __cil_tmp98 = 0 * 4UL;
#line 244
      __cil_tmp99 = (unsigned long )(tags) + __cil_tmp98;
#line 244
      __cil_tmp100 = *((unsigned int *)__cil_tmp99);
#line 244
      mfc_get(__cil_tmp93, __cil_tmp94, __cil_tmp97, __cil_tmp100, 0U, 0U);
#line 246
      state = 1;
      }
    } else {

    }
#line 250
    if (state == 1) {
#line 253
      if (buffer >= 0) {
#line 253
        if (buffer < 2) {
#line 253
          tmp___4 = 1;
        } else {
#line 253
          tmp___4 = 0;
        }
      } else {
#line 253
        tmp___4 = 0;
      }
      {
#line 253
      assert(tmp___4);
      }
      {
#line 255
      __cil_tmp101 = (unsigned int )cnt;
#line 255
      if (__cil_tmp101 < left) {
#line 256
        __cil_tmp102 = (unsigned int )cnt;
#line 256
        left = left - __cil_tmp102;
#line 258
        next_ctx_pos_v = ctx_pos_v + cnt;
#line 259
        next_ctx_vel_v = ctx_vel_v + cnt;
#line 260
        next_ctx_inv_mass = ctx_inv_mass + cnt;
#line 261
        if (left < 1024U) {
#line 261
          next_cnt = (int )left;
        } else {
#line 261
          next_cnt = 1024;
        }
        {
#line 266
        next_buffer = buffer ^ 1;
#line 272
        __cil_tmp103 = 0 * 16UL;
#line 272
        __cil_tmp104 = next_buffer * 16384UL;
#line 272
        __cil_tmp105 = __cil_tmp104 + __cil_tmp103;
#line 272
        __cil_tmp106 = (unsigned long )(pos) + __cil_tmp105;
#line 272
        __cil_tmp107 = (float4 volatile   *)__cil_tmp106;
#line 272
        __cil_tmp108 = (void *)__cil_tmp107;
#line 272
        __cil_tmp109 = (void volatile   *)__cil_tmp108;
#line 272
        __cil_tmp110 = (unsigned int )next_ctx_pos_v;
#line 272
        __cil_tmp111 = (unsigned long )next_cnt;
#line 272
        __cil_tmp112 = __cil_tmp111 * 16UL;
#line 272
        __cil_tmp113 = (unsigned int )__cil_tmp112;
#line 272
        __cil_tmp114 = next_buffer * 4UL;
#line 272
        __cil_tmp115 = (unsigned long )(tags) + __cil_tmp114;
#line 272
        __cil_tmp116 = *((unsigned int *)__cil_tmp115);
#line 272
        mfc_get(__cil_tmp109, __cil_tmp110, __cil_tmp113, __cil_tmp116, 0U, 0U);
#line 275
        __cil_tmp117 = 0 * 16UL;
#line 275
        __cil_tmp118 = next_buffer * 16384UL;
#line 275
        __cil_tmp119 = __cil_tmp118 + __cil_tmp117;
#line 275
        __cil_tmp120 = (unsigned long )(vel) + __cil_tmp119;
#line 275
        __cil_tmp121 = (float4 volatile   *)__cil_tmp120;
#line 275
        __cil_tmp122 = (void *)__cil_tmp121;
#line 275
        __cil_tmp123 = (void volatile   *)__cil_tmp122;
#line 275
        __cil_tmp124 = (unsigned int )next_ctx_vel_v;
#line 275
        __cil_tmp125 = (unsigned long )next_cnt;
#line 275
        __cil_tmp126 = __cil_tmp125 * 16UL;
#line 275
        __cil_tmp127 = (unsigned int )__cil_tmp126;
#line 275
        __cil_tmp128 = next_buffer * 4UL;
#line 275
        __cil_tmp129 = (unsigned long )(tags) + __cil_tmp128;
#line 275
        __cil_tmp130 = *((unsigned int *)__cil_tmp129);
#line 275
        mfc_get(__cil_tmp123, __cil_tmp124, __cil_tmp127, __cil_tmp130, 0U, 0U);
#line 276
        __cil_tmp131 = 0 * 16UL;
#line 276
        __cil_tmp132 = next_buffer * 4096UL;
#line 276
        __cil_tmp133 = __cil_tmp132 + __cil_tmp131;
#line 276
        __cil_tmp134 = (unsigned long )(inv_mass) + __cil_tmp133;
#line 276
        __cil_tmp135 = (float4 volatile   *)__cil_tmp134;
#line 276
        __cil_tmp136 = (void *)__cil_tmp135;
#line 276
        __cil_tmp137 = (void volatile   *)__cil_tmp136;
#line 276
        __cil_tmp138 = (unsigned int )next_ctx_inv_mass;
#line 276
        __cil_tmp139 = (unsigned long )next_cnt;
#line 276
        __cil_tmp140 = __cil_tmp139 * 4UL;
#line 276
        __cil_tmp141 = (unsigned int )__cil_tmp140;
#line 276
        __cil_tmp142 = next_buffer * 4UL;
#line 276
        __cil_tmp143 = (unsigned long )(tags) + __cil_tmp142;
#line 276
        __cil_tmp144 = *((unsigned int *)__cil_tmp143);
#line 276
        mfc_get(__cil_tmp137, __cil_tmp138, __cil_tmp141, __cil_tmp144, 0U, 0U);
#line 279
        __cil_tmp145 = buffer * 4UL;
#line 279
        __cil_tmp146 = (unsigned long )(tags) + __cil_tmp145;
#line 279
        __cil_tmp147 = *((unsigned int *)__cil_tmp146);
#line 279
        __cil_tmp148 = 1 << __cil_tmp147;
#line 279
        __cil_tmp149 = (unsigned int )__cil_tmp148;
#line 279
        mfc_write_tag_mask(__cil_tmp149);
#line 280
        mfc_read_tag_status_all();
#line 287
        __cil_tmp150 = 0 * 16UL;
#line 287
        __cil_tmp151 = buffer * 16384UL;
#line 287
        __cil_tmp152 = __cil_tmp151 + __cil_tmp150;
#line 287
        __cil_tmp153 = (unsigned long )(pos) + __cil_tmp152;
#line 287
        __cil_tmp154 = (float4 volatile   *)__cil_tmp153;
#line 287
        __cil_tmp155 = (void *)__cil_tmp154;
#line 287
        __cil_tmp156 = (void volatile   *)__cil_tmp155;
#line 287
        __cil_tmp157 = (unsigned int )ctx_pos_v;
#line 287
        __cil_tmp158 = (unsigned long )cnt;
#line 287
        __cil_tmp159 = __cil_tmp158 * 16UL;
#line 287
        __cil_tmp160 = (unsigned int )__cil_tmp159;
#line 287
        __cil_tmp161 = buffer * 4UL;
#line 287
        __cil_tmp162 = (unsigned long )(tags) + __cil_tmp161;
#line 287
        __cil_tmp163 = *((unsigned int *)__cil_tmp162);
#line 287
        mfc_put(__cil_tmp156, __cil_tmp157, __cil_tmp160, __cil_tmp163, 0U, 0U);
#line 288
        __cil_tmp164 = 0 * 16UL;
#line 288
        __cil_tmp165 = buffer * 16384UL;
#line 288
        __cil_tmp166 = __cil_tmp165 + __cil_tmp164;
#line 288
        __cil_tmp167 = (unsigned long )(vel) + __cil_tmp166;
#line 288
        __cil_tmp168 = (float4 volatile   *)__cil_tmp167;
#line 288
        __cil_tmp169 = (void *)__cil_tmp168;
#line 288
        __cil_tmp170 = (void volatile   *)__cil_tmp169;
#line 288
        __cil_tmp171 = (unsigned int )ctx_vel_v;
#line 288
        __cil_tmp172 = (unsigned long )cnt;
#line 288
        __cil_tmp173 = __cil_tmp172 * 16UL;
#line 288
        __cil_tmp174 = (unsigned int )__cil_tmp173;
#line 288
        __cil_tmp175 = buffer * 4UL;
#line 288
        __cil_tmp176 = (unsigned long )(tags) + __cil_tmp175;
#line 288
        __cil_tmp177 = *((unsigned int *)__cil_tmp176);
#line 288
        mfc_put(__cil_tmp170, __cil_tmp171, __cil_tmp174, __cil_tmp177, 0U, 0U);
#line 290
        ctx_pos_v = next_ctx_pos_v;
#line 291
        ctx_vel_v = next_ctx_vel_v;
#line 292
        ctx_inv_mass = next_ctx_inv_mass;
#line 294
        buffer = next_buffer;
#line 295
        cnt = next_cnt;
        }
      } else {
#line 298
        state = 2;
      }
      }
    } else {

    }
#line 303
    if (state == 2) {
      {
#line 305
      __cil_tmp178 = buffer * 4UL;
#line 305
      __cil_tmp179 = (unsigned long )(tags) + __cil_tmp178;
#line 305
      __cil_tmp180 = *((unsigned int *)__cil_tmp179);
#line 305
      __cil_tmp181 = 1 << __cil_tmp180;
#line 305
      __cil_tmp182 = (unsigned int )__cil_tmp181;
#line 305
      mfc_write_tag_mask(__cil_tmp182);
#line 306
      mfc_read_tag_status_all();
#line 313
      __cil_tmp183 = 0 * 16UL;
#line 313
      __cil_tmp184 = buffer * 16384UL;
#line 313
      __cil_tmp185 = __cil_tmp184 + __cil_tmp183;
#line 313
      __cil_tmp186 = (unsigned long )(pos) + __cil_tmp185;
#line 313
      __cil_tmp187 = (float4 volatile   *)__cil_tmp186;
#line 313
      __cil_tmp188 = (void *)__cil_tmp187;
#line 313
      __cil_tmp189 = (void volatile   *)__cil_tmp188;
#line 313
      __cil_tmp190 = (unsigned int )ctx_pos_v;
#line 313
      __cil_tmp191 = (unsigned long )cnt;
#line 313
      __cil_tmp192 = __cil_tmp191 * 16UL;
#line 313
      __cil_tmp193 = (unsigned int )__cil_tmp192;
#line 313
      __cil_tmp194 = buffer * 4UL;
#line 313
      __cil_tmp195 = (unsigned long )(tags) + __cil_tmp194;
#line 313
      __cil_tmp196 = *((unsigned int *)__cil_tmp195);
#line 313
      mfc_put(__cil_tmp189, __cil_tmp190, __cil_tmp193, __cil_tmp196, 0U, 0U);
#line 314
      __cil_tmp197 = 0 * 16UL;
#line 314
      __cil_tmp198 = buffer * 16384UL;
#line 314
      __cil_tmp199 = __cil_tmp198 + __cil_tmp197;
#line 314
      __cil_tmp200 = (unsigned long )(vel) + __cil_tmp199;
#line 314
      __cil_tmp201 = (float4 volatile   *)__cil_tmp200;
#line 314
      __cil_tmp202 = (void *)__cil_tmp201;
#line 314
      __cil_tmp203 = (void volatile   *)__cil_tmp202;
#line 314
      __cil_tmp204 = (unsigned int )ctx_vel_v;
#line 314
      __cil_tmp205 = (unsigned long )cnt;
#line 314
      __cil_tmp206 = __cil_tmp205 * 16UL;
#line 314
      __cil_tmp207 = (unsigned int )__cil_tmp206;
#line 314
      __cil_tmp208 = buffer * 4UL;
#line 314
      __cil_tmp209 = (unsigned long )(tags) + __cil_tmp208;
#line 314
      __cil_tmp210 = *((unsigned int *)__cil_tmp209);
#line 314
      mfc_put(__cil_tmp203, __cil_tmp204, __cil_tmp207, __cil_tmp210, 0U, 0U);
#line 317
      __cil_tmp211 = buffer * 4UL;
#line 317
      __cil_tmp212 = (unsigned long )(tags) + __cil_tmp211;
#line 317
      __cil_tmp213 = *((unsigned int *)__cil_tmp212);
#line 317
      __cil_tmp214 = 1 << __cil_tmp213;
#line 317
      __cil_tmp215 = (unsigned int )__cil_tmp214;
#line 317
      mfc_write_tag_mask(__cil_tmp215);
#line 318
      mfc_read_tag_status_all();
#line 320
      time = time + dt;
#line 322
      state = 0;
      }
    } else {

    }
  }
  while_break: /* CIL Label */ ;
  }
#line 327
  return (0);
}
}
