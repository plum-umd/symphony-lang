#ifndef SYMPHONY_EMP_H__
#define SYMPHONY_EMP_H__
#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>
#include "symphony/util.h"

#ifdef __cplusplus
extern "C" {
#endif

/*
  --------------------
  --- EMP Contexts ---
  --------------------
*/

  struct emp_semi_ctx;
  typedef struct emp_semi_ctx emp_semi_ctx_t;

  emp_semi_ctx_t *emp_semi_ctx_create(int8_t party, channel_t *chan);
  void emp_semi_ctx_destroy(emp_semi_ctx_t *p);

/*
  ----------------
  --- EMP Bits ---
  ----------------
*/

  typedef struct emp_semi_bit {
    int obj[4];
  } emp_semi_bit_t;

  // Share from INPUT party
  void emp_semi_bit_send_share(bool b, channel_t **chans);
  emp_semi_bit_t *emp_semi_bit_recv_share(emp_semi_ctx_t *p, channel_t *chan);
  emp_semi_bit_t emp_semi_bit_recv_share_stack(emp_semi_ctx_t *p, channel_t *chan);

  // Share from COMPUTE party
  emp_semi_bit_t emp_semi_bit_share_stack(emp_semi_ctx_t *p, int8_t party, bool b);
  emp_semi_bit_t *emp_semi_bit_share(emp_semi_ctx_t *p, int8_t party, bool b);

  // Reveal to OUTPUT party
  void emp_semi_bit_send_reveal(emp_semi_ctx_t *p, emp_semi_bit_t *v, channel_t *chan);
  void emp_semi_bit_send_reveal_stack(emp_semi_ctx_t *p, emp_semi_bit_t v, channel_t *chan);
  bool emp_semi_bit_recv_reveal(channel_t **chans);

  // Reveal to COMPUTE party
  bool emp_semi_bit_reveal(emp_semi_ctx_t *p, int8_t party, emp_semi_bit_t *v);
  bool emp_semi_bit_reveal_stack(emp_semi_ctx_t *p, int8_t party, emp_semi_bit_t v);

  // Destroy a share
  void emp_semi_bit_destroy(emp_semi_bit_t *v);

/*
  --------------------------
  ---- Stack Allocation ----
  --------------------------
*/

  emp_semi_bit_t emp_semi_bit_xor_stack(emp_semi_ctx_t *p, emp_semi_bit_t *lhs, emp_semi_bit_t *rhs);
  emp_semi_bit_t emp_semi_bit_and_stack(emp_semi_ctx_t *p, emp_semi_bit_t *lhs, emp_semi_bit_t *rhs);

  emp_semi_bit_t emp_semi_bit_not_stack(emp_semi_ctx_t *p, emp_semi_bit_t *v);
  emp_semi_bit_t emp_semi_bit_or_stack(emp_semi_ctx_t *p, emp_semi_bit_t *lhs, emp_semi_bit_t *rhs);
  emp_semi_bit_t emp_semi_bit_cond_stack(emp_semi_ctx_t *p, emp_semi_bit_t *guard, emp_semi_bit_t *lhs, emp_semi_bit_t *rhs);

/*
  -------------------------
  ---- Heap Allocation ----
  -------------------------
*/

  emp_semi_bit_t *emp_semi_bit_xor(emp_semi_ctx_t *p, emp_semi_bit_t *lhs, emp_semi_bit_t *rhs);
  emp_semi_bit_t *emp_semi_bit_and(emp_semi_ctx_t *p, emp_semi_bit_t *lhs, emp_semi_bit_t *rhs);

  emp_semi_bit_t *emp_semi_bit_not(emp_semi_ctx_t *p, emp_semi_bit_t *v);
  emp_semi_bit_t *emp_semi_bit_or(emp_semi_ctx_t *p, emp_semi_bit_t *lhs, emp_semi_bit_t *rhs);
  emp_semi_bit_t *emp_semi_bit_cond(emp_semi_ctx_t *p, emp_semi_bit_t *guard, emp_semi_bit_t *lhs, emp_semi_bit_t *rhs);

/*
  --------------------
  --- EMP Integers ---
  --------------------
*/

  struct emp_semi_int64;
  typedef struct emp_semi_int64 emp_semi_int64_t;

  // Share from INPUT party
  void emp_semi_int64_send_share(int64_t v, channel_t **chans);
  emp_semi_int64_t *emp_semi_int64_recv_share(emp_semi_ctx_t *p, channel_t *chan);

  // Share from COMPUTE party
  emp_semi_int64_t *emp_semi_int64_share(emp_semi_ctx_t *p, int8_t party, int64_t v);

  // Reveal to OUTPUT party
  void emp_semi_int64_send_reveal(emp_semi_ctx_t *p, emp_semi_int64_t *v, channel_t *chan);
  int64_t emp_semi_int64_recv_reveal(channel_t **chans);

  // Reveal to COMPUTE party
  int64_t emp_semi_int64_reveal(emp_semi_ctx_t *p, int8_t party, emp_semi_int64_t *v);

  // Destroy a share
  void emp_semi_int64_destroy(emp_semi_int64_t *v);

  emp_semi_int64_t *emp_semi_int64_add(emp_semi_ctx_t *p, emp_semi_int64_t *lhs, emp_semi_int64_t *rhs);
  emp_semi_int64_t *emp_semi_int64_mult(emp_semi_ctx_t *p, emp_semi_int64_t *lhs, emp_semi_int64_t *rhs);

  emp_semi_int64_t *emp_semi_int64_sub(emp_semi_ctx_t *p, emp_semi_int64_t *lhs, emp_semi_int64_t *rhs);
  emp_semi_int64_t *emp_semi_int64_div(emp_semi_ctx_t *p, emp_semi_int64_t *lhs, emp_semi_int64_t *rhs);
  emp_semi_int64_t *emp_semi_int64_mod(emp_semi_ctx_t *p, emp_semi_int64_t *lhs, emp_semi_int64_t *rhs);
  emp_semi_bit_t *emp_semi_int64_eq(emp_semi_ctx_t *p, emp_semi_int64_t *lhs, emp_semi_int64_t *rhs);
  emp_semi_bit_t *emp_semi_int64_lt(emp_semi_ctx_t *p, emp_semi_int64_t *lhs, emp_semi_int64_t *rhs);
  emp_semi_bit_t *emp_semi_int64_lte(emp_semi_ctx_t *p, emp_semi_int64_t *lhs, emp_semi_int64_t *rhs);
  emp_semi_bit_t *emp_semi_int64_gt(emp_semi_ctx_t *p, emp_semi_int64_t *lhs, emp_semi_int64_t *rhs);
  emp_semi_int64_t *emp_semi_int64_cond(emp_semi_ctx_t *p, emp_semi_bit_t *guard, emp_semi_int64_t *lhs, emp_semi_int64_t *rhs);

#ifdef __cplusplus
}
#endif

#endif
