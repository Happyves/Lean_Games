// Lean compiler output
// Module: Games.gameLib.HistoryMoves
// Imports: Init Games.gameLib.HistoryAPI Games.gameLib.Playability Games.gameLib.Termination
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
LEAN_EXPORT lean_object* l_Hist__from__moves(lean_object*);
LEAN_EXPORT lean_object* l_Hist__from__moves___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_csStrategy__from__moves(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_csStrategy__from__moves___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_hasDecEq___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_moves__from__strats(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidablePredNatTurn__fst(lean_object*);
LEAN_EXPORT lean_object* l_Game__World_moves__from__strats___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Game__World_hist__on__turn___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
LEAN_EXPORT lean_object* l_Game__World_cfStrategy__from__moves___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_moves__from__strats___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_cfStrategy__from__moves___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Game__World_csStrategy__from__moves___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_cfStrategy__from__moves(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Hist__from__moves___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_List_range(x_2);
x_4 = l_List_reverse___rarg(x_3);
x_5 = lean_box(0);
x_6 = l_List_mapTR_loop___rarg(x_1, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Hist__from__moves(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Hist__from__moves___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Game__World_moves__from__strats___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_5);
lean_inc(x_4);
x_7 = l_Game__World_hist__on__turn___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_6, x_8);
x_10 = l_instDecidablePredNatTurn__fst(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = lean_apply_3(x_5, x_7, lean_box(0), lean_box(0));
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_5);
x_12 = lean_apply_3(x_4, x_7, lean_box(0), lean_box(0));
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Game__World_moves__from__strats(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Game__World_moves__from__strats___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Game__World_moves__from__strats___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Game__World_moves__from__strats___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Game__World_cfStrategy__from__moves___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_List_lengthTRAux___rarg(x_8, x_11);
lean_inc(x_12);
lean_inc(x_6);
x_13 = l_Hist__from__moves___rarg(x_6, x_12);
lean_inc(x_8);
x_14 = l_List_hasDecEq___rarg(x_1, x_8, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_6);
x_15 = lean_apply_3(x_5, x_8, lean_box(0), lean_box(0));
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_5);
x_16 = lean_apply_1(x_6, x_12);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Game__World_cfStrategy__from__moves(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Game__World_cfStrategy__from__moves___rarg___boxed), 10, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Game__World_cfStrategy__from__moves___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Game__World_cfStrategy__from__moves___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Game__World_csStrategy__from__moves___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_List_lengthTRAux___rarg(x_8, x_11);
lean_inc(x_12);
lean_inc(x_6);
x_13 = l_Hist__from__moves___rarg(x_6, x_12);
lean_inc(x_8);
x_14 = l_List_hasDecEq___rarg(x_1, x_8, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_6);
x_15 = lean_apply_3(x_5, x_8, lean_box(0), lean_box(0));
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_5);
x_16 = lean_apply_1(x_6, x_12);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Game__World_csStrategy__from__moves(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Game__World_csStrategy__from__moves___rarg___boxed), 10, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Game__World_csStrategy__from__moves___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Game__World_csStrategy__from__moves___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Games_gameLib_HistoryAPI(uint8_t builtin, lean_object*);
lean_object* initialize_Games_gameLib_Playability(uint8_t builtin, lean_object*);
lean_object* initialize_Games_gameLib_Termination(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Games_gameLib_HistoryMoves(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Games_gameLib_HistoryAPI(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Games_gameLib_Playability(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Games_gameLib_Termination(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
