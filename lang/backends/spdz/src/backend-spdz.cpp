#include "backend-spdz.h"

/*
  ----------------------------
  --- SPDZ Binary Contexts ---
  ----------------------------
*/

struct mp_semi_bin_ctx {
};

mp_semi_bin_ctx_t *mp_semi_bin_ctx_create(uint16_t party, int *sockets, size_t size) {
  return NULL;
}

void mp_semi_bin_ctx_destroy(mp_semi_bin_ctx_t *p) {
  return;
}

/*
  ------------------------
  --- SPDZ Binary Bits ---
  ------------------------
*/

struct mp_semi_bin_bit {
};

void mp_semi_bin_bit_send(bool b, int *sockets, size_t size) {
  return;
}

mp_semi_bin_bit_t *mp_semi_bin_bit_recv(int socket) {
  return NULL;
}

bool mp_semi_bin_bit_reify(mp_semi_bin_bit_t *v) {
  return true;
}

void mp_semi_bin_bit_destroy(mp_semi_bin_bit_t *v) {
  return;
}
