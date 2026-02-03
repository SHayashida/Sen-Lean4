// Lean compiler output
// Module: SocialChoiceAtlas.Sen.BaseCase24.Spec
// Imports: Init Mathlib.Data.Fin.Basic Mathlib.Tactic.FinCases SocialChoiceAtlas.Core.Profile
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
static lean_object* l_SocialChoiceAtlas_Sen_BaseCase24_allVoters___closed__2;
LEAN_EXPORT lean_object* l_SocialChoiceAtlas_Sen_BaseCase24_alt3;
static lean_object* l_SocialChoiceAtlas_Sen_BaseCase24_allAlts___closed__2;
static lean_object* l_SocialChoiceAtlas_Sen_BaseCase24_allAlts___closed__3;
LEAN_EXPORT lean_object* l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeAlt;
static lean_object* l_SocialChoiceAtlas_Sen_BaseCase24_allAlts___closed__1;
static lean_object* l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeVoter___closed__1;
LEAN_EXPORT lean_object* l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeVoter;
LEAN_EXPORT uint8_t l_SocialChoiceAtlas_Sen_BaseCase24_instDecidableEqVoter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SocialChoiceAtlas_Sen_BaseCase24_voter0;
LEAN_EXPORT uint8_t l_SocialChoiceAtlas_Sen_BaseCase24_instDecidableEqAlt(lean_object*, lean_object*);
static lean_object* l_SocialChoiceAtlas_Sen_BaseCase24_allVoters___closed__1;
LEAN_EXPORT lean_object* l_SocialChoiceAtlas_Sen_BaseCase24_alt0;
static lean_object* l_SocialChoiceAtlas_Sen_BaseCase24_allAlts___closed__4;
LEAN_EXPORT lean_object* l_SocialChoiceAtlas_Sen_BaseCase24_alt2;
LEAN_EXPORT lean_object* l_SocialChoiceAtlas_Sen_BaseCase24_voter1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SocialChoiceAtlas_Sen_BaseCase24_instDecidableEqAlt___boxed(lean_object*, lean_object*);
lean_object* l_List_ofFn___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SocialChoiceAtlas_Sen_BaseCase24_allAlts;
LEAN_EXPORT lean_object* l_SocialChoiceAtlas_Sen_BaseCase24_allVoters;
LEAN_EXPORT lean_object* l_SocialChoiceAtlas_Sen_BaseCase24_instDecidableEqVoter___boxed(lean_object*, lean_object*);
lean_object* l_List_finRange___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_SocialChoiceAtlas_Sen_BaseCase24_alt1;
static lean_object* l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeVoter___closed__2;
static lean_object* l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeAlt___closed__1;
static lean_object* _init_l_SocialChoiceAtlas_Sen_BaseCase24_voter0() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_SocialChoiceAtlas_Sen_BaseCase24_voter1() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1u);
return x_1;
}
}
static lean_object* _init_l_SocialChoiceAtlas_Sen_BaseCase24_alt0() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_SocialChoiceAtlas_Sen_BaseCase24_alt1() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1u);
return x_1;
}
}
static lean_object* _init_l_SocialChoiceAtlas_Sen_BaseCase24_alt2() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(2u);
return x_1;
}
}
static lean_object* _init_l_SocialChoiceAtlas_Sen_BaseCase24_alt3() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(3u);
return x_1;
}
}
LEAN_EXPORT uint8_t l_SocialChoiceAtlas_Sen_BaseCase24_instDecidableEqVoter(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_SocialChoiceAtlas_Sen_BaseCase24_instDecidableEqVoter___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_SocialChoiceAtlas_Sen_BaseCase24_instDecidableEqVoter(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_SocialChoiceAtlas_Sen_BaseCase24_instDecidableEqAlt(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_SocialChoiceAtlas_Sen_BaseCase24_instDecidableEqAlt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_SocialChoiceAtlas_Sen_BaseCase24_instDecidableEqAlt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeVoter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_finRange___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeVoter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeVoter___closed__1;
x_3 = l_List_ofFn___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeVoter() {
_start:
{
lean_object* x_1; 
x_1 = l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeVoter___closed__2;
return x_1;
}
}
static lean_object* _init_l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeAlt___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeVoter___closed__1;
x_3 = l_List_ofFn___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeAlt() {
_start:
{
lean_object* x_1; 
x_1 = l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeAlt___closed__1;
return x_1;
}
}
static lean_object* _init_l_SocialChoiceAtlas_Sen_BaseCase24_allVoters___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_SocialChoiceAtlas_Sen_BaseCase24_allVoters___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_SocialChoiceAtlas_Sen_BaseCase24_allVoters___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_SocialChoiceAtlas_Sen_BaseCase24_allVoters() {
_start:
{
lean_object* x_1; 
x_1 = l_SocialChoiceAtlas_Sen_BaseCase24_allVoters___closed__2;
return x_1;
}
}
static lean_object* _init_l_SocialChoiceAtlas_Sen_BaseCase24_allAlts___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_SocialChoiceAtlas_Sen_BaseCase24_allAlts___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_SocialChoiceAtlas_Sen_BaseCase24_allAlts___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_SocialChoiceAtlas_Sen_BaseCase24_allAlts___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_SocialChoiceAtlas_Sen_BaseCase24_allAlts___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_SocialChoiceAtlas_Sen_BaseCase24_allAlts___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_SocialChoiceAtlas_Sen_BaseCase24_allAlts___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_SocialChoiceAtlas_Sen_BaseCase24_allAlts() {
_start:
{
lean_object* x_1; 
x_1 = l_SocialChoiceAtlas_Sen_BaseCase24_allAlts___closed__4;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Fin_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic_FinCases(uint8_t builtin, lean_object*);
lean_object* initialize_SocialChoiceAtlas_Core_Profile(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SocialChoiceAtlas_Sen_BaseCase24_Spec(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Fin_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_FinCases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SocialChoiceAtlas_Core_Profile(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_SocialChoiceAtlas_Sen_BaseCase24_voter0 = _init_l_SocialChoiceAtlas_Sen_BaseCase24_voter0();
lean_mark_persistent(l_SocialChoiceAtlas_Sen_BaseCase24_voter0);
l_SocialChoiceAtlas_Sen_BaseCase24_voter1 = _init_l_SocialChoiceAtlas_Sen_BaseCase24_voter1();
lean_mark_persistent(l_SocialChoiceAtlas_Sen_BaseCase24_voter1);
l_SocialChoiceAtlas_Sen_BaseCase24_alt0 = _init_l_SocialChoiceAtlas_Sen_BaseCase24_alt0();
lean_mark_persistent(l_SocialChoiceAtlas_Sen_BaseCase24_alt0);
l_SocialChoiceAtlas_Sen_BaseCase24_alt1 = _init_l_SocialChoiceAtlas_Sen_BaseCase24_alt1();
lean_mark_persistent(l_SocialChoiceAtlas_Sen_BaseCase24_alt1);
l_SocialChoiceAtlas_Sen_BaseCase24_alt2 = _init_l_SocialChoiceAtlas_Sen_BaseCase24_alt2();
lean_mark_persistent(l_SocialChoiceAtlas_Sen_BaseCase24_alt2);
l_SocialChoiceAtlas_Sen_BaseCase24_alt3 = _init_l_SocialChoiceAtlas_Sen_BaseCase24_alt3();
lean_mark_persistent(l_SocialChoiceAtlas_Sen_BaseCase24_alt3);
l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeVoter___closed__1 = _init_l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeVoter___closed__1();
lean_mark_persistent(l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeVoter___closed__1);
l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeVoter___closed__2 = _init_l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeVoter___closed__2();
lean_mark_persistent(l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeVoter___closed__2);
l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeVoter = _init_l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeVoter();
lean_mark_persistent(l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeVoter);
l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeAlt___closed__1 = _init_l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeAlt___closed__1();
lean_mark_persistent(l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeAlt___closed__1);
l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeAlt = _init_l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeAlt();
lean_mark_persistent(l_SocialChoiceAtlas_Sen_BaseCase24_instFintypeAlt);
l_SocialChoiceAtlas_Sen_BaseCase24_allVoters___closed__1 = _init_l_SocialChoiceAtlas_Sen_BaseCase24_allVoters___closed__1();
lean_mark_persistent(l_SocialChoiceAtlas_Sen_BaseCase24_allVoters___closed__1);
l_SocialChoiceAtlas_Sen_BaseCase24_allVoters___closed__2 = _init_l_SocialChoiceAtlas_Sen_BaseCase24_allVoters___closed__2();
lean_mark_persistent(l_SocialChoiceAtlas_Sen_BaseCase24_allVoters___closed__2);
l_SocialChoiceAtlas_Sen_BaseCase24_allVoters = _init_l_SocialChoiceAtlas_Sen_BaseCase24_allVoters();
lean_mark_persistent(l_SocialChoiceAtlas_Sen_BaseCase24_allVoters);
l_SocialChoiceAtlas_Sen_BaseCase24_allAlts___closed__1 = _init_l_SocialChoiceAtlas_Sen_BaseCase24_allAlts___closed__1();
lean_mark_persistent(l_SocialChoiceAtlas_Sen_BaseCase24_allAlts___closed__1);
l_SocialChoiceAtlas_Sen_BaseCase24_allAlts___closed__2 = _init_l_SocialChoiceAtlas_Sen_BaseCase24_allAlts___closed__2();
lean_mark_persistent(l_SocialChoiceAtlas_Sen_BaseCase24_allAlts___closed__2);
l_SocialChoiceAtlas_Sen_BaseCase24_allAlts___closed__3 = _init_l_SocialChoiceAtlas_Sen_BaseCase24_allAlts___closed__3();
lean_mark_persistent(l_SocialChoiceAtlas_Sen_BaseCase24_allAlts___closed__3);
l_SocialChoiceAtlas_Sen_BaseCase24_allAlts___closed__4 = _init_l_SocialChoiceAtlas_Sen_BaseCase24_allAlts___closed__4();
lean_mark_persistent(l_SocialChoiceAtlas_Sen_BaseCase24_allAlts___closed__4);
l_SocialChoiceAtlas_Sen_BaseCase24_allAlts = _init_l_SocialChoiceAtlas_Sen_BaseCase24_allAlts();
lean_mark_persistent(l_SocialChoiceAtlas_Sen_BaseCase24_allAlts);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
