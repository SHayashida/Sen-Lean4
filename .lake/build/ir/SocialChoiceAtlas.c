// Lean compiler output
// Module: SocialChoiceAtlas
// Imports: Init SocialChoiceAtlas.Core.Basics SocialChoiceAtlas.Core.Ranking SocialChoiceAtlas.Core.Profile SocialChoiceAtlas.Axioms.Pareto SocialChoiceAtlas.Axioms.Liberalism SocialChoiceAtlas.Axioms.Rationality SocialChoiceAtlas.Sen.BaseCase24.Spec SocialChoiceAtlas.Sen.BaseCase24.Theorem
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_SocialChoiceAtlas_Core_Basics(uint8_t builtin, lean_object*);
lean_object* initialize_SocialChoiceAtlas_Core_Ranking(uint8_t builtin, lean_object*);
lean_object* initialize_SocialChoiceAtlas_Core_Profile(uint8_t builtin, lean_object*);
lean_object* initialize_SocialChoiceAtlas_Axioms_Pareto(uint8_t builtin, lean_object*);
lean_object* initialize_SocialChoiceAtlas_Axioms_Liberalism(uint8_t builtin, lean_object*);
lean_object* initialize_SocialChoiceAtlas_Axioms_Rationality(uint8_t builtin, lean_object*);
lean_object* initialize_SocialChoiceAtlas_Sen_BaseCase24_Spec(uint8_t builtin, lean_object*);
lean_object* initialize_SocialChoiceAtlas_Sen_BaseCase24_Theorem(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SocialChoiceAtlas(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SocialChoiceAtlas_Core_Basics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SocialChoiceAtlas_Core_Ranking(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SocialChoiceAtlas_Core_Profile(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SocialChoiceAtlas_Axioms_Pareto(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SocialChoiceAtlas_Axioms_Liberalism(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SocialChoiceAtlas_Axioms_Rationality(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SocialChoiceAtlas_Sen_BaseCase24_Spec(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SocialChoiceAtlas_Sen_BaseCase24_Theorem(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
