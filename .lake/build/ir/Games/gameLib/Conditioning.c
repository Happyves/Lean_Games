// Lean compiler output
// Module: Games.gameLib.Conditioning
// Imports: Init Games.gameLib.Basic Games.gameLib.Termination
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
LEAN_EXPORT lean_object* l_Game__World_world__after__fst___elambda__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_world__after__preHist___elambda__2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_fst__strat__deconditioned(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Games_gameLib_Conditioning_0__History__on__turn_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l_zGame_state__on__turn___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_zGame_history__on__turn(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqListNil___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Games_gameLib_Conditioning_0__History__on__turn_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_world__after__preHist___elambda__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_world__after__preHist___rarg(lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
uint8_t l_instDecidablePredNatTurn__fst(lean_object*);
LEAN_EXPORT lean_object* l_zGame__World_snd__strat__deconditioned(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqListNil___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Game__World_world__after__fst___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_world__after__preHist___elambda__1(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT lean_object* l_zGame__World_world__after__fst___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_world__after__fst___elambda__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_zGame__World_snd__strat__deconditioned___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_fst__strat__deconditioned___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_snd__strat__deconditioned(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_world__after__fst___elambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_snd__strat__deconditioned___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_world__after__fst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_world__after__preHist___elambda__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_zGame__World_snd__strat__conditioned(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_zGame__World_snd__strat__deconditioned___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_zGame_history__on__turn___rarg___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_History__on__turn___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_world__after__preHist(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_zGame__World_snd__strat__conditioned___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_snd__strat__deconditioned___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_zGame_history__on__turn___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqListNil(lean_object*);
LEAN_EXPORT lean_object* l___private_Games_gameLib_Conditioning_0__History__on__turn_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_zGame__World_world__after__fst(lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_world__after__fst___elambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_zGame__World_snd__strat__conditioned___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_zGame_state__on__turn___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_fst__strat__deconditioned___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_zGame_state__on__turn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Game__World_world__after__fst___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_3(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Game__World_world__after__fst___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Game__World_world__after__fst___elambda__1___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Game__World_world__after__fst___elambda__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_3(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Game__World_world__after__fst___elambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Game__World_world__after__fst___elambda__2___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Game__World_world__after__fst___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Game__World_world__after__fst___elambda__2___rarg), 4, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_box(0);
lean_inc(x_1);
x_6 = l_Game__World_world__after__fst___elambda__2___rarg(x_1, x_4, x_5, x_2);
x_7 = lean_alloc_closure((void*)(l_Game__World_world__after__fst___elambda__1___rarg), 4, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Game__World_world__after__fst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Game__World_world__after__fst___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqListNil___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableEqListNil(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instDecidableEqListNil___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqListNil___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_instDecidableEqListNil___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_fst__strat__deconditioned___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_instDecidableEqListNil___rarg(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_Game__World_world__after__fst___rarg(x_3, x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_List_redLength___rarg(x_5);
x_10 = lean_mk_empty_array_with_capacity(x_9);
lean_dec(x_9);
x_11 = l_List_toArrayAux___rarg(x_5, x_10);
x_12 = lean_array_pop(x_11);
x_13 = lean_array_to_list(lean_box(0), x_12);
x_14 = lean_apply_2(x_1, x_8, x_13);
return x_14;
}
else
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_fst__strat__deconditioned(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_fst__strat__deconditioned___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_fst__strat__deconditioned___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_fst__strat__deconditioned___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_snd__strat__deconditioned___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l_Game__World_world__after__fst___rarg(x_3, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_List_redLength___rarg(x_5);
x_9 = lean_mk_empty_array_with_capacity(x_8);
lean_dec(x_8);
x_10 = l_List_toArrayAux___rarg(x_5, x_9);
x_11 = lean_array_pop(x_10);
x_12 = lean_array_to_list(lean_box(0), x_11);
x_13 = lean_apply_2(x_1, x_7, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_snd__strat__deconditioned(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_snd__strat__deconditioned___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_snd__strat__deconditioned___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_snd__strat__deconditioned___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Game__World_world__after__preHist___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_3(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Game__World_world__after__preHist___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Game__World_world__after__preHist___elambda__1___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Game__World_world__after__preHist___elambda__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_3(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Game__World_world__after__preHist___elambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Game__World_world__after__preHist___elambda__2___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Game__World_world__after__preHist___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Game__World_world__after__preHist___elambda__2___rarg), 4, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_inc(x_1);
x_7 = l_Game__World_world__after__preHist___elambda__2___rarg(x_1, x_6, x_4, x_3);
x_8 = lean_alloc_closure((void*)(l_Game__World_world__after__preHist___elambda__1___rarg), 4, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Game__World_world__after__preHist(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Game__World_world__after__preHist___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_zGame__World_world__after__fst___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_1);
x_4 = l_Game__World_world__after__fst___rarg(x_1, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 2);
lean_dec(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_dec(x_7);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Game__World_world__after__fst___elambda__2___rarg), 4, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_alloc_closure((void*)(l_Game__World_world__after__fst___elambda__1___rarg), 4, 1);
lean_closure_set(x_9, 0, x_1);
lean_ctor_set(x_4, 2, x_9);
lean_ctor_set(x_4, 1, x_8);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Game__World_world__after__fst___elambda__2___rarg), 4, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_alloc_closure((void*)(l_Game__World_world__after__fst___elambda__1___rarg), 4, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_zGame__World_world__after__fst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_zGame__World_world__after__fst___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Games_gameLib_Conditioning_0__History__on__turn_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Games_gameLib_Conditioning_0__History__on__turn_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Games_gameLib_Conditioning_0__History__on__turn_match__1_splitter___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Games_gameLib_Conditioning_0__History__on__turn_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Games_gameLib_Conditioning_0__History__on__turn_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_zGame_history__on__turn___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_History__on__turn___rarg(x_4, x_5, x_6, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_zGame_history__on__turn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_zGame_history__on__turn___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_zGame_history__on__turn___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_zGame_history__on__turn___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_zGame_state__on__turn___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
lean_inc(x_1);
x_7 = l_zGame_history__on__turn___rarg(x_1, x_6);
x_8 = lean_nat_add(x_6, x_5);
lean_dec(x_6);
x_9 = l_instDecidablePredNatTurn__fst(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_12);
x_14 = lean_apply_2(x_13, x_12, x_7);
x_15 = lean_apply_3(x_11, x_12, x_7, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_18);
x_20 = lean_apply_2(x_19, x_18, x_7);
x_21 = lean_apply_3(x_17, x_18, x_7, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_zGame_state__on__turn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_zGame_state__on__turn___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_zGame_state__on__turn___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_zGame_state__on__turn___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_zGame__World_snd__strat__conditioned___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_List_appendTR___rarg(x_5, x_8);
x_10 = lean_apply_2(x_1, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_zGame__World_snd__strat__conditioned(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_zGame__World_snd__strat__conditioned___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_zGame__World_snd__strat__conditioned___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_zGame__World_snd__strat__conditioned___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_zGame__World_snd__strat__deconditioned___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_instDecidableEqListNil___rarg(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_zGame__World_world__after__fst___rarg(x_3, x_2, lean_box(0));
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_List_redLength___rarg(x_6);
x_11 = lean_mk_empty_array_with_capacity(x_10);
lean_dec(x_10);
x_12 = l_List_toArrayAux___rarg(x_6, x_11);
x_13 = lean_array_pop(x_12);
x_14 = lean_array_to_list(lean_box(0), x_13);
x_15 = lean_apply_2(x_1, x_9, x_14);
return x_15;
}
else
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_zGame__World_snd__strat__deconditioned(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_zGame__World_snd__strat__deconditioned___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_zGame__World_snd__strat__deconditioned___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_zGame__World_snd__strat__deconditioned___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Games_gameLib_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Games_gameLib_Termination(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Games_gameLib_Conditioning(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Games_gameLib_Basic(builtin, lean_io_mk_world());
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
