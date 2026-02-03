// Lean compiler output
// Module: SocialChoiceAtlas.Core.Ranking
// Imports: Init Mathlib.Data.Fin.Basic Mathlib.Data.Finset.Basic Mathlib.Data.Fintype.Card Mathlib.Data.List.Dedup Mathlib.Data.List.Nodup Mathlib.Data.List.Perm.Basic
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
LEAN_EXPORT lean_object* l_SocialChoiceAtlas_Ranking_position(lean_object*);
LEAN_EXPORT lean_object* l_List_indexOf___at_SocialChoiceAtlas_Ranking_position___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SocialChoiceAtlas_Ranking_position___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_indexOf___at_SocialChoiceAtlas_Ranking_position___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_SocialChoiceAtlas_Ranking_position___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_go___at_SocialChoiceAtlas_Ranking_position___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_go___at_SocialChoiceAtlas_Ranking_position___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_SocialChoiceAtlas_Ranking_decidablePrefers___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SocialChoiceAtlas_Ranking_decidablePrefers(lean_object*);
LEAN_EXPORT lean_object* l_SocialChoiceAtlas_Ranking_decidablePrefers___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findIdx_go___at_SocialChoiceAtlas_Ranking_position___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_List_findIdx_go___at_SocialChoiceAtlas_Ranking_position___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_findIdx_go___at_SocialChoiceAtlas_Ranking_position___spec__2___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_indexOf___at_SocialChoiceAtlas_Ranking_position___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_List_findIdx_go___at_SocialChoiceAtlas_Ranking_position___spec__2___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_indexOf___at_SocialChoiceAtlas_Ranking_position___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_indexOf___at_SocialChoiceAtlas_Ranking_position___spec__1___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_SocialChoiceAtlas_Ranking_position___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_List_findIdx_go___at_SocialChoiceAtlas_Ranking_position___spec__2___rarg(x_1, x_4, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_SocialChoiceAtlas_Ranking_position(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_SocialChoiceAtlas_Ranking_position___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_SocialChoiceAtlas_Ranking_position___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_SocialChoiceAtlas_Ranking_position___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_SocialChoiceAtlas_Ranking_decidablePrefers___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
lean_inc(x_1);
x_7 = l_List_findIdx_go___at_SocialChoiceAtlas_Ranking_position___spec__2___rarg(x_1, x_4, x_3, x_6);
x_8 = l_List_findIdx_go___at_SocialChoiceAtlas_Ranking_position___spec__2___rarg(x_1, x_5, x_3, x_6);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_SocialChoiceAtlas_Ranking_decidablePrefers(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_SocialChoiceAtlas_Ranking_decidablePrefers___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_SocialChoiceAtlas_Ranking_decidablePrefers___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_SocialChoiceAtlas_Ranking_decidablePrefers___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Fin_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Finset_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Fintype_Card(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_List_Dedup(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_List_Nodup(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_List_Perm_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SocialChoiceAtlas_Core_Ranking(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Fin_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Finset_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Fintype_Card(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_List_Dedup(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_List_Nodup(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_List_Perm_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
