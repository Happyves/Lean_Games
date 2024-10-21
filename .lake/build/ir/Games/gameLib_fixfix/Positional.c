// Lean compiler output
// Module: Games.gameLib_fixfix.Positional
// Imports: Init Games.gameLib_fixfix.Termination
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
LEAN_EXPORT lean_object* l_Positional__Game__World___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_indexOf___at_Positional__Game__World___spec__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Positional__Game__World___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_PosGame__trans___at_Positional__Game__World___spec__1(lean_object*);
uint8_t l_instDecidablePredNatTurn__fst(lean_object*);
LEAN_EXPORT lean_object* l_Positional__Game__World___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_go___at_PosGame__trans___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Positional__Game__World___rarg___closed__1;
LEAN_EXPORT lean_object* l_List_findIdx_go___at_PosGame__trans___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_go___at_Positional__Game__World___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_go___at_Positional__Game__World___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PosGame__trans___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PosGame__trans___at_Positional__Game__World___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_indexOf___at_PosGame__trans___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_indexOf___at_Positional__Game__World___spec__2(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Positional__Game__World(lean_object*);
LEAN_EXPORT lean_object* l_List_indexOf___at_PosGame__trans___spec__1(lean_object*);
lean_object* l_instBEq___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Positional__Game__World___rarg___lambda__1___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PosGame__trans(lean_object*);
LEAN_EXPORT lean_object* l_Positional__Game__World___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_go___at_PosGame__trans___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_7 = lean_apply_2(x_1, x_5, x_2);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
x_3 = x_6;
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go___at_PosGame__trans___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_findIdx_go___at_PosGame__trans___spec__2___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_indexOf___at_PosGame__trans___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_List_findIdx_go___at_PosGame__trans___spec__2___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_indexOf___at_PosGame__trans___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_indexOf___at_PosGame__trans___spec__1___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PosGame__trans___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_instBEq___rarg), 3, 1);
lean_closure_set(x_4, 0, x_1);
lean_inc(x_2);
lean_inc(x_3);
x_5 = l_List_elem___rarg(x_4, x_3, x_2);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_unsigned_to_nat(0u);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = l_List_reverse___rarg(x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_List_findIdx_go___at_PosGame__trans___spec__2___rarg(x_1, x_3, x_7, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_9);
x_12 = l_instDecidablePredNatTurn__fst(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_unsigned_to_nat(2u);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_unsigned_to_nat(1u);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_PosGame__trans(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PosGame__trans___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go___at_Positional__Game__World___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_7 = lean_apply_2(x_1, x_5, x_2);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
x_3 = x_6;
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go___at_Positional__Game__World___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_findIdx_go___at_Positional__Game__World___spec__3___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_indexOf___at_Positional__Game__World___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_List_findIdx_go___at_Positional__Game__World___spec__3___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_indexOf___at_Positional__Game__World___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_indexOf___at_Positional__Game__World___spec__2___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PosGame__trans___at_Positional__Game__World___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_instBEq___rarg), 3, 1);
lean_closure_set(x_4, 0, x_1);
lean_inc(x_2);
lean_inc(x_3);
x_5 = l_List_elem___rarg(x_4, x_3, x_2);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_unsigned_to_nat(0u);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = l_List_reverse___rarg(x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_List_findIdx_go___at_Positional__Game__World___spec__3___rarg(x_1, x_3, x_7, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_9);
x_12 = l_instDecidablePredNatTurn__fst(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_unsigned_to_nat(2u);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_unsigned_to_nat(1u);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_PosGame__trans___at_Positional__Game__World___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PosGame__trans___at_Positional__Game__World___spec__1___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Positional__Game__World___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Positional__Game__World___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_3);
x_7 = l_PosGame__trans___at_Positional__Game__World___spec__1___rarg(x_1, x_6, x_5);
return x_7;
}
}
static lean_object* _init_l_Positional__Game__World___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Positional__Game__World___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Positional__Game__World___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Positional__Game__World___rarg___lambda__2), 5, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Positional__Game__World___rarg___closed__1;
lean_inc(x_4);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Positional__Game__World(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Positional__Game__World___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Positional__Game__World___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Positional__Game__World___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Positional__Game__World___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Positional__Game__World___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Games_gameLib__fixfix_Termination(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Games_gameLib__fixfix_Positional(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Games_gameLib__fixfix_Termination(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Positional__Game__World___rarg___closed__1 = _init_l_Positional__Game__World___rarg___closed__1();
lean_mark_persistent(l_Positional__Game__World___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
