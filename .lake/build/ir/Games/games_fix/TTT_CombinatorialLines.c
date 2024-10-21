// Lean compiler output
// Module: Games.games_fix.TTT_CombinatorialLines
// Imports: Init Mathlib
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
LEAN_EXPORT lean_object* l_Opp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Games_games__fix_TTT__CombinatorialLines_0__the__inj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_seq__reverse___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Games_games__fix_TTT__CombinatorialLines_0__the__inj___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Opp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Games_games__fix_TTT__CombinatorialLines_0__the__inj___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Games_games__fix_TTT__CombinatorialLines_0__the__inj___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Games_games__fix_TTT__CombinatorialLines_0__the__inj___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_seq__reverse___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Games_games__fix_TTT__CombinatorialLines_0__the__inj___rarg___lambda__3(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Games_games__fix_TTT__CombinatorialLines_0__the__inj___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Finset_decidableExistsAndFinset___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_seq__reverse(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Games_games__fix_TTT__CombinatorialLines_0__the__inj(lean_object*);
LEAN_EXPORT lean_object* l_seq__reverse___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Games_games__fix_TTT__CombinatorialLines_0__the__inj___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
uint8_t l_Fintype_decidableForallFintype___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Opp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_1, x_4);
x_6 = lean_nat_sub(x_5, x_3);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Opp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Opp(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_seq__reverse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Opp(x_1, lean_box(0), x_4);
x_7 = lean_apply_2(x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_seq__reverse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_seq__reverse___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_seq__reverse___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_seq__reverse___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_seq__reverse___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_seq__reverse(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Games_games__fix_TTT__CombinatorialLines_0__the__inj___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_apply_2(x_1, x_4, x_2);
x_6 = lean_nat_dec_eq(x_5, x_3);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Games_games__fix_TTT__CombinatorialLines_0__the__inj___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_alloc_closure((void*)(l___private_Games_games__fix_TTT__CombinatorialLines_0__the__inj___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
x_6 = l_List_finRange(x_3);
x_7 = l_Fintype_decidableForallFintype___rarg(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Games_games__fix_TTT__CombinatorialLines_0__the__inj___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_3);
x_4 = lean_apply_2(x_1, x_3, x_2);
x_5 = lean_nat_dec_eq(x_4, x_3);
lean_dec(x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Games_games__fix_TTT__CombinatorialLines_0__the__inj___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_alloc_closure((void*)(l___private_Games_games__fix_TTT__CombinatorialLines_0__the__inj___rarg___lambda__2___boxed), 4, 3);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
lean_closure_set(x_4, 2, x_1);
x_5 = l_List_finRange(x_1);
lean_inc(x_5);
x_6 = l_Finset_decidableExistsAndFinset___rarg(x_5, lean_box(0), x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_alloc_closure((void*)(l___private_Games_games__fix_TTT__CombinatorialLines_0__the__inj___rarg___lambda__3___boxed), 3, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_3);
x_8 = l_Fintype_decidableForallFintype___rarg(x_7, x_5);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(2u);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_unsigned_to_nat(1u);
return x_10;
}
}
else
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_unsigned_to_nat(0u);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Games_games__fix_TTT__CombinatorialLines_0__the__inj(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Games_games__fix_TTT__CombinatorialLines_0__the__inj___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Games_games__fix_TTT__CombinatorialLines_0__the__inj___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l___private_Games_games__fix_TTT__CombinatorialLines_0__the__inj___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Games_games__fix_TTT__CombinatorialLines_0__the__inj___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l___private_Games_games__fix_TTT__CombinatorialLines_0__the__inj___rarg___lambda__2(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Games_games__fix_TTT__CombinatorialLines_0__the__inj___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Games_games__fix_TTT__CombinatorialLines_0__the__inj___rarg___lambda__3(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Games_games__fix_TTT__CombinatorialLines_0__the__inj___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Games_games__fix_TTT__CombinatorialLines_0__the__inj(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Games_games__fix_TTT__CombinatorialLines(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
