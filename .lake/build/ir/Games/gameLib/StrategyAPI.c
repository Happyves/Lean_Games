// Lean compiler output
// Module: Games.gameLib.StrategyAPI
// Imports: Init Games.gameLib.Termination Games.gameLib.HistoryAPI Games.gameLib.Playability Games.exLib.General
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_Game__World_cExStrat__staged__fst___elambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_cExStrat__staged__snd___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_hasDecEq___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_cExStrat__staged__fst___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_cExStrat__staged__fst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_sStrat__winner_x27___elambda__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_decidableSuffix___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_sStrat__winner_x27___elambda__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_fStrat__winner_x27___elambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_cExStrat__staged__snd___elambda__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_cExStrat__staged__snd___elambda__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_cExStrat__staged__snd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_fStrat__winner_x27___elambda__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_sStrat__winner_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_rget___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_cExStrat__staged__fst___elambda__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_fStrat__winner_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_cExStrat__staged__fst___elambda__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_rtake___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_cExStrat__staged__snd___elambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_fStrat__winner_x27___elambda__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_fStrat__winner_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_sStrat__winner_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_sStrat__winner_x27___elambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_cExStrat__staged__fst___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_List_lengthTRAux___rarg(x_5, x_8);
x_10 = l_List_rtake___rarg(x_4, x_9);
lean_inc(x_5);
x_11 = l_List_hasDecEq___rarg(x_1, x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = lean_apply_3(x_3, x_5, lean_box(0), lean_box(0));
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_List_lengthTRAux___rarg(x_4, x_8);
x_14 = lean_nat_dec_lt(x_9, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_9);
x_15 = lean_apply_3(x_3, x_5, lean_box(0), lean_box(0));
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_3);
x_16 = l_List_rget___rarg(x_4, x_9);
lean_dec(x_9);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Game__World_cExStrat__staged__fst___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Game__World_cExStrat__staged__fst___elambda__1___rarg___boxed), 7, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Game__World_cExStrat__staged__fst___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Game__World_cExStrat__staged__fst___elambda__1___rarg___boxed), 7, 4);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_3);
lean_closure_set(x_6, 3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Game__World_cExStrat__staged__fst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Game__World_cExStrat__staged__fst___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Game__World_cExStrat__staged__fst___elambda__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Game__World_cExStrat__staged__fst___elambda__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Game__World_cExStrat__staged__snd___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_List_lengthTRAux___rarg(x_5, x_8);
x_10 = l_List_rtake___rarg(x_4, x_9);
lean_inc(x_5);
x_11 = l_List_hasDecEq___rarg(x_1, x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = lean_apply_3(x_3, x_5, lean_box(0), lean_box(0));
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_List_lengthTRAux___rarg(x_4, x_8);
x_14 = lean_nat_dec_lt(x_9, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_9);
x_15 = lean_apply_3(x_3, x_5, lean_box(0), lean_box(0));
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_3);
x_16 = l_List_rget___rarg(x_4, x_9);
lean_dec(x_9);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Game__World_cExStrat__staged__snd___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Game__World_cExStrat__staged__snd___elambda__1___rarg___boxed), 7, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Game__World_cExStrat__staged__snd___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Game__World_cExStrat__staged__snd___elambda__1___rarg___boxed), 7, 4);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_3);
lean_closure_set(x_6, 3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Game__World_cExStrat__staged__snd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Game__World_cExStrat__staged__snd___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Game__World_cExStrat__staged__snd___elambda__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Game__World_cExStrat__staged__snd___elambda__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Game__World_fStrat__winner_x27___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_List_lengthTRAux___rarg(x_8, x_11);
x_13 = l_List_rtake___rarg(x_4, x_12);
lean_inc(x_8);
x_14 = l_List_decidableSuffix___rarg(x_1, x_13, x_8);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_7);
x_15 = lean_apply_3(x_3, x_8, lean_box(0), lean_box(0));
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_3);
x_16 = l_List_lengthTRAux___rarg(x_4, x_11);
x_17 = lean_nat_dec_lt(x_12, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
x_18 = l_List_rget___rarg(x_8, x_16);
lean_dec(x_16);
x_19 = lean_apply_5(x_7, x_18, lean_box(0), x_8, lean_box(0), lean_box(0));
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
x_20 = l_List_rget___rarg(x_4, x_12);
lean_dec(x_12);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Game__World_fStrat__winner_x27___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Game__World_fStrat__winner_x27___elambda__1___rarg___boxed), 10, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Game__World_fStrat__winner_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l_Game__World_fStrat__winner_x27___elambda__1___rarg___boxed), 10, 7);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_4);
lean_closure_set(x_8, 4, lean_box(0));
lean_closure_set(x_8, 5, lean_box(0));
lean_closure_set(x_8, 6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Game__World_fStrat__winner_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Game__World_fStrat__winner_x27___rarg), 7, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Game__World_fStrat__winner_x27___elambda__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Game__World_fStrat__winner_x27___elambda__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Game__World_sStrat__winner_x27___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_List_lengthTRAux___rarg(x_8, x_11);
x_13 = l_List_rtake___rarg(x_4, x_12);
lean_inc(x_8);
x_14 = l_List_decidableSuffix___rarg(x_1, x_13, x_8);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_7);
x_15 = lean_apply_3(x_3, x_8, lean_box(0), lean_box(0));
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_3);
x_16 = l_List_lengthTRAux___rarg(x_4, x_11);
x_17 = lean_nat_dec_lt(x_12, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
x_18 = l_List_rget___rarg(x_8, x_16);
lean_dec(x_16);
x_19 = lean_apply_5(x_7, x_18, lean_box(0), x_8, lean_box(0), lean_box(0));
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
x_20 = l_List_rget___rarg(x_4, x_12);
lean_dec(x_12);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Game__World_sStrat__winner_x27___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Game__World_sStrat__winner_x27___elambda__1___rarg___boxed), 10, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Game__World_sStrat__winner_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l_Game__World_sStrat__winner_x27___elambda__1___rarg___boxed), 10, 7);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_4);
lean_closure_set(x_8, 4, lean_box(0));
lean_closure_set(x_8, 5, lean_box(0));
lean_closure_set(x_8, 6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Game__World_sStrat__winner_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Game__World_sStrat__winner_x27___rarg), 7, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Game__World_sStrat__winner_x27___elambda__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Game__World_sStrat__winner_x27___elambda__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Games_gameLib_Termination(uint8_t builtin, lean_object*);
lean_object* initialize_Games_gameLib_HistoryAPI(uint8_t builtin, lean_object*);
lean_object* initialize_Games_gameLib_Playability(uint8_t builtin, lean_object*);
lean_object* initialize_Games_exLib_General(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Games_gameLib_StrategyAPI(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Games_gameLib_Termination(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Games_gameLib_HistoryAPI(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Games_gameLib_Playability(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Games_exLib_General(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
