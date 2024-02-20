// Lean compiler output
// Module: Games.games.PickUpBricks
// Imports: Init Games.exLib.Nat Games.gameLib.Basic Mathlib.Tactic
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
static lean_object* l_PickUpBricks__pubWin__vs__toy___closed__4;
LEAN_EXPORT lean_object* l_toy__strat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_bricks__end__turn__from__ini__hist__act(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Games_games_PickUpBricks_0__PickUpBricks_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Games_games_PickUpBricks_0__History__on__turn_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at_Composition_sizeUpTo___spec__2(lean_object*, lean_object*);
static lean_object* l_PickUpBricks__pubWin__vs__toy___closed__2;
LEAN_EXPORT lean_object* l_PickUpBricks___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_bricks__start__turn__from__ini__hist___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_toy__strat(lean_object*, lean_object*);
static lean_object* l_PickUpBricks__pubWin__vs__toy___closed__3;
static lean_object* l_PickUpBricks__pubWin__vs__toy___closed__5;
LEAN_EXPORT lean_object* l_pub__win__strat___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Games_games_PickUpBricks_0__History__on__turn_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_bricks__end__turn__from__ini__hist__act___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_bricks__start__turn__from__ini__hist(lean_object*, lean_object*);
static lean_object* l_PickUpBricks__pubWin__vs__toy___closed__1;
LEAN_EXPORT lean_object* l___private_Games_games_PickUpBricks_0__History__on__turn_match__1_splitter(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Games_games_PickUpBricks_0__PickUpBricks_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_pub__win__strat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PickUpBricks(lean_object*);
LEAN_EXPORT lean_object* l_PickUpBricks___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_PickUpBricks__pubWin__vs__toy;
LEAN_EXPORT lean_object* l_bricks__start__turn__from__ini__hist(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_foldl___at_Composition_sizeUpTo___spec__2(x_3, x_2);
x_5 = lean_nat_sub(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_bricks__start__turn__from__ini__hist___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_bricks__start__turn__from__ini__hist(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_bricks__end__turn__from__ini__hist__act(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_List_foldl___at_Composition_sizeUpTo___spec__2(x_4, x_2);
x_6 = lean_nat_sub(x_1, x_5);
lean_dec(x_5);
x_7 = lean_nat_sub(x_6, x_3);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_bricks__end__turn__from__ini__hist__act___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_bricks__end__turn__from__ini__hist__act(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_PickUpBricks___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_List_foldl___at_Composition_sizeUpTo___spec__2(x_4, x_2);
x_6 = lean_nat_sub(x_1, x_5);
lean_dec(x_5);
x_7 = lean_nat_sub(x_6, x_3);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_PickUpBricks(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_PickUpBricks___elambda__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_PickUpBricks___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PickUpBricks___elambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_pub__win__strat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_foldl___at_Composition_sizeUpTo___spec__2(x_3, x_2);
x_5 = lean_nat_sub(x_1, x_4);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(3u);
x_7 = lean_nat_mod(x_5, x_6);
x_8 = lean_nat_dec_eq(x_5, x_3);
lean_dec(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_dec_eq(x_7, x_9);
lean_dec(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_unsigned_to_nat(2u);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_unsigned_to_nat(1u);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_7);
x_13 = lean_unsigned_to_nat(0u);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_pub__win__strat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_pub__win__strat(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Games_games_PickUpBricks_0__PickUpBricks_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_2);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_dec_eq(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_apply_4(x_4, x_1, lean_box(0), lean_box(0), lean_box(0));
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_1);
x_10 = lean_apply_1(x_3, lean_box(0));
return x_10;
}
}
else
{
lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_apply_1(x_2, lean_box(0));
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Games_games_PickUpBricks_0__PickUpBricks_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Games_games_PickUpBricks_0__PickUpBricks_match__1_splitter___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_toy__strat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_foldl___at_Composition_sizeUpTo___spec__2(x_3, x_2);
x_5 = lean_nat_sub(x_1, x_4);
lean_dec(x_4);
x_6 = lean_nat_dec_eq(x_5, x_3);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(1u);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(0u);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_toy__strat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_toy__strat(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_PickUpBricks__pubWin__vs__toy___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_alloc_closure((void*)(l_PickUpBricks___elambda__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_PickUpBricks__pubWin__vs__toy___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = l_PickUpBricks__pubWin__vs__toy___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_PickUpBricks__pubWin__vs__toy___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_pub__win__strat___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_PickUpBricks__pubWin__vs__toy___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_toy__strat___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_PickUpBricks__pubWin__vs__toy___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_PickUpBricks__pubWin__vs__toy___closed__2;
x_2 = l_PickUpBricks__pubWin__vs__toy___closed__3;
x_3 = l_PickUpBricks__pubWin__vs__toy___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_PickUpBricks__pubWin__vs__toy() {
_start:
{
lean_object* x_1; 
x_1 = l_PickUpBricks__pubWin__vs__toy___closed__5;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Games_games_PickUpBricks_0__History__on__turn_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Games_games_PickUpBricks_0__History__on__turn_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Games_games_PickUpBricks_0__History__on__turn_match__1_splitter___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Games_games_PickUpBricks_0__History__on__turn_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Games_games_PickUpBricks_0__History__on__turn_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Games_exLib_Nat(uint8_t builtin, lean_object*);
lean_object* initialize_Games_gameLib_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Games_games_PickUpBricks(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Games_exLib_Nat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Games_gameLib_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_PickUpBricks__pubWin__vs__toy___closed__1 = _init_l_PickUpBricks__pubWin__vs__toy___closed__1();
lean_mark_persistent(l_PickUpBricks__pubWin__vs__toy___closed__1);
l_PickUpBricks__pubWin__vs__toy___closed__2 = _init_l_PickUpBricks__pubWin__vs__toy___closed__2();
lean_mark_persistent(l_PickUpBricks__pubWin__vs__toy___closed__2);
l_PickUpBricks__pubWin__vs__toy___closed__3 = _init_l_PickUpBricks__pubWin__vs__toy___closed__3();
lean_mark_persistent(l_PickUpBricks__pubWin__vs__toy___closed__3);
l_PickUpBricks__pubWin__vs__toy___closed__4 = _init_l_PickUpBricks__pubWin__vs__toy___closed__4();
lean_mark_persistent(l_PickUpBricks__pubWin__vs__toy___closed__4);
l_PickUpBricks__pubWin__vs__toy___closed__5 = _init_l_PickUpBricks__pubWin__vs__toy___closed__5();
lean_mark_persistent(l_PickUpBricks__pubWin__vs__toy___closed__5);
l_PickUpBricks__pubWin__vs__toy = _init_l_PickUpBricks__pubWin__vs__toy();
lean_mark_persistent(l_PickUpBricks__pubWin__vs__toy);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
