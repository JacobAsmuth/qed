/*
  uv_stubs.c — defined-failure stubs for the four libuv temp-file/tmpdir
  functions that `libleanrt` references but the prebuilt `linux_wasm32`
  toolchain does not bundle (Lean v4.15 gained this libuv dependency; the
  toolchain ships only the header). A browser frontend never creates temp files,
  so these are never called — but defining them keeps the emscripten linker
  strict, so any other missing symbol still surfaces as an error.
*/
#include <stddef.h>

int  uv_fs_mkdtemp(void *loop, void *req, const char *tpl, void *cb) { (void)loop; (void)req; (void)tpl; (void)cb; return -1; }
int  uv_fs_mkstemp(void *loop, void *req, const char *tpl, void *cb) { (void)loop; (void)req; (void)tpl; (void)cb; return -1; }
int  uv_os_tmpdir (char *buffer, size_t *size) { (void)buffer; (void)size; return -1; }
const char *uv_strerror(int err) { (void)err; return "libuv unsupported in wasm build"; }
