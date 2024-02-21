// Lean compiler output
// Module: Games.gameLib.Positional
// Imports: Init Games.gameLib.Basic
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
LEAN_EXPORT lean_object* l_List_findIdx_go___at_Positional__Game__World___elambda__2___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Positional__Game__World___elambda__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_indexOf___at_PosGameW__trans___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_go___at_PosGameW__trans___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Positional__Game__World___elambda__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidablePredNatTurn__fst(lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_go___at_Positional__Game__World___elambda__1___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Positional__Game__World___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_indexOf___at_Positional__Game__World___elambda__2___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Positional__Game__World___elambda__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Positional__Game__World___elambda__2(lean_object*);
LEAN_EXPORT lean_object* l_PosGameW__trans___at_Positional__Game__World___elambda__2___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_go___at_Positional__Game__World___elambda__2___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_indexOf___at_Positional__Game__World___elambda__1___spec__2___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_indexOf___at_Positional__Game__World___elambda__1___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_go___at_PosGameW__trans___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Positional__Game__World___elambda__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PosGameW__trans___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_indexOf___at_PosGameW__trans___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_PosGameW__trans___at_Positional__Game__World___elambda__2___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Positional__Game__World(lean_object*);
lean_object* l_instBEq___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PosGameW__trans___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_indexOf___at_Positional__Game__World___elambda__2___spec__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PosGameW__trans___at_Positional__Game__World___elambda__1___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_PosGameW__trans___at_Positional__Game__World___elambda__1___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PosGameW__trans___at_Positional__Game__World___elambda__1___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Positional__Game__World___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PosGameW__trans___at_Positional__Game__World___elambda__2___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Positional__Game__World___elambda__1(lean_object*);
LEAN_EXPORT lean_object* l_PosGameW__trans(lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_go___at_Positional__Game__World___elambda__1___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_go___at_PosGameW__trans___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_List_findIdx_go___at_PosGameW__trans___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_findIdx_go___at_PosGameW__trans___spec__2___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_indexOf___at_PosGameW__trans___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_List_findIdx_go___at_PosGameW__trans___spec__2___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_indexOf___at_PosGameW__trans___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_indexOf___at_PosGameW__trans___spec__1___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PosGameW__trans___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
lean_inc(x_1);
lean_inc(x_5);
x_6 = lean_apply_2(x_1, x_5, x_4);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_instBEq___rarg), 3, 1);
lean_closure_set(x_8, 0, x_1);
lean_inc(x_3);
lean_inc(x_5);
x_9 = l_List_elem___rarg(x_8, x_5, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(0u);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_List_findIdx_go___at_PosGameW__trans___spec__2___rarg(x_1, x_5, x_3, x_11);
x_13 = l_instDecidablePredNatTurn__fst(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_unsigned_to_nat(2u);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_unsigned_to_nat(1u);
return x_15;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_PosGameW__trans(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PosGameW__trans___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PosGameW__trans___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PosGameW__trans___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go___at_Positional__Game__World___elambda__1___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_List_findIdx_go___at_Positional__Game__World___elambda__1___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_findIdx_go___at_Positional__Game__World___elambda__1___spec__3___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_indexOf___at_Positional__Game__World___elambda__1___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_List_findIdx_go___at_Positional__Game__World___elambda__1___spec__3___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_indexOf___at_Positional__Game__World___elambda__1___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_indexOf___at_Positional__Game__World___elambda__1___spec__2___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PosGameW__trans___at_Positional__Game__World___elambda__1___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
lean_inc(x_1);
lean_inc(x_5);
x_6 = lean_apply_2(x_1, x_5, x_4);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_instBEq___rarg), 3, 1);
lean_closure_set(x_8, 0, x_1);
lean_inc(x_3);
lean_inc(x_5);
x_9 = l_List_elem___rarg(x_8, x_5, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(0u);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_List_findIdx_go___at_Positional__Game__World___elambda__1___spec__3___rarg(x_1, x_5, x_3, x_11);
x_13 = l_instDecidablePredNatTurn__fst(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_unsigned_to_nat(2u);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_unsigned_to_nat(1u);
return x_15;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_PosGameW__trans___at_Positional__Game__World___elambda__1___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PosGameW__trans___at_Positional__Game__World___elambda__1___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Positional__Game__World___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_PosGameW__trans___at_Positional__Game__World___elambda__1___spec__1___rarg(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Positional__Game__World___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Positional__Game__World___elambda__1___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_findIdx_go___at_Positional__Game__World___elambda__2___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_List_findIdx_go___at_Positional__Game__World___elambda__2___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_findIdx_go___at_Positional__Game__World___elambda__2___spec__3___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_indexOf___at_Positional__Game__World___elambda__2___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_List_findIdx_go___at_Positional__Game__World___elambda__2___spec__3___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_indexOf___at_Positional__Game__World___elambda__2___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_indexOf___at_Positional__Game__World___elambda__2___spec__2___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_PosGameW__trans___at_Positional__Game__World___elambda__2___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
lean_inc(x_1);
lean_inc(x_5);
x_6 = lean_apply_2(x_1, x_5, x_4);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_instBEq___rarg), 3, 1);
lean_closure_set(x_8, 0, x_1);
lean_inc(x_3);
lean_inc(x_5);
x_9 = l_List_elem___rarg(x_8, x_5, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(0u);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_List_findIdx_go___at_Positional__Game__World___elambda__2___spec__3___rarg(x_1, x_5, x_3, x_11);
x_13 = l_instDecidablePredNatTurn__fst(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_unsigned_to_nat(2u);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_unsigned_to_nat(1u);
return x_15;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_PosGameW__trans___at_Positional__Game__World___elambda__2___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PosGameW__trans___at_Positional__Game__World___elambda__2___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Positional__Game__World___elambda__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_PosGameW__trans___at_Positional__Game__World___elambda__2___spec__1___rarg(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Positional__Game__World___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Positional__Game__World___elambda__2___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Positional__Game__World___elambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Positional__Game__World___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_Positional__Game__World___elambda__3___boxed), 2, 1);
lean_closure_set(x_4, 0, lean_box(0));
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Positional__Game__World___elambda__2___rarg), 4, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_alloc_closure((void*)(l_Positional__Game__World___elambda__1___rarg), 4, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
return x_7;
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
LEAN_EXPORT lean_object* l_PosGameW__trans___at_Positional__Game__World___elambda__1___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PosGameW__trans___at_Positional__Game__World___elambda__1___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_PosGameW__trans___at_Positional__Game__World___elambda__2___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PosGameW__trans___at_Positional__Game__World___elambda__2___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Positional__Game__World___elambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Positional__Game__World___elambda__3(x_1, x_2);
lean_dec(x_2);
return x_3;
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
lean_object* initialize_Games_gameLib_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Games_gameLib_Positional(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Games_gameLib_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
