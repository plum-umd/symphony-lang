#ifndef SYMPHONY_SPDZ_H__
#define SYMPHONY_SPDZ_H__

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

  /*
  ----------------------------
  --- SPDZ Binary Contexts ---
  ----------------------------
*/

  struct mp_semi_bin_ctx;
  typedef struct mp_semi_bin_ctx mp_semi_bin_ctx_t;

  mp_semi_bin_ctx_t *mp_semi_bin_ctx_create(uint16_t party, int *sockets, size_t size);
  void mp_semi_bin_ctx_destroy(mp_semi_bin_ctx_t *p);

/*
  ------------------------
  --- SPDZ Binary Bits ---
  ------------------------
*/

  struct mp_semi_bin_bit;
  typedef struct mp_semi_bin_bit mp_semi_bin_bit_t;

  void mp_semi_bin_bit_send(bool b, int *sockets, size_t size);
  mp_semi_bin_bit_t *mp_semi_bin_bit_recv(int socket);
  bool mp_semi_bin_bit_reify(mp_semi_bin_bit_t *v);
  void mp_semi_bin_bit_destroy(mp_semi_bin_bit_t *v);

#ifdef __cplusplus
}
#endif

#endif
