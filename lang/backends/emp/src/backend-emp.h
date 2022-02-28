#ifndef SYMPHONY_EMP_H__
#define SYMPHONY_EMP_H__
#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
  ----------------------
  --- NetIO Channels ---
  ----------------------
*/

  struct netio;
  typedef struct netio netio_t;
  netio_t *netio_create(const char *addr, int port, bool quiet);
  void netio_destroy(netio_t *io);

  void netio_send(netio_t *io, void *data, size_t bytes);
  void netio_recv(netio_t *io, void *data, size_t bytes);
  void netio_flush(netio_t *io);

/*
  --------------------
  --- EMP Contexts ---
  --------------------
*/

  struct emp_semi_ctx;
  typedef struct emp_semi_ctx emp_semi_ctx_t;

  emp_semi_ctx_t *emp_semi_ctx_create(int8_t party, netio_t *io);
  void emp_semi_ctx_destroy(emp_semi_ctx_t *p);

/*
  ----------------
  --- EMP Bits ---
  ----------------
*/

  typedef struct emp_semi_bit {
    int obj[4];
  } emp_semi_bit_t;

/*
  --------------------------
  ---- Stack Allocation ----
  --------------------------
*/

  emp_semi_bit_t emp_semi_bit_create_stack(emp_semi_ctx_t *p, int8_t party, bool b);

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

  emp_semi_bit_t *emp_semi_bit_create(emp_semi_ctx_t *p, int8_t party, bool b);
  bool emp_semi_bit_reveal(emp_semi_ctx_t *p, int8_t party, emp_semi_bit_t *v);
  void emp_semi_bit_destroy(emp_semi_bit_t *v);

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

  struct emp_semi_integer;
  typedef struct emp_semi_integer emp_semi_integer_t;

  emp_semi_integer_t *emp_semi_integer_create(emp_semi_ctx_t *p, int8_t party, uint16_t precision, int64_t v);
  int64_t emp_semi_integer_reveal(emp_semi_ctx_t *p, int8_t party, emp_semi_integer_t *v);
  void emp_semi_integer_destroy(emp_semi_integer_t *v);

  emp_semi_integer_t *emp_semi_integer_add(emp_semi_ctx_t *p, emp_semi_integer_t *lhs, emp_semi_integer_t *rhs);
  emp_semi_integer_t *emp_semi_integer_mult(emp_semi_ctx_t *p, emp_semi_integer_t *lhs, emp_semi_integer_t *rhs);

  emp_semi_integer_t *emp_semi_integer_sub(emp_semi_ctx_t *p, emp_semi_integer_t *lhs, emp_semi_integer_t *rhs);
  emp_semi_integer_t *emp_semi_integer_div(emp_semi_ctx_t *p, emp_semi_integer_t *lhs, emp_semi_integer_t *rhs);
  emp_semi_integer_t *emp_semi_integer_mod(emp_semi_ctx_t *p, emp_semi_integer_t *lhs, emp_semi_integer_t *rhs);
  emp_semi_bit_t *emp_semi_integer_eq(emp_semi_ctx_t *p, emp_semi_integer_t *lhs, emp_semi_integer_t *rhs);
  emp_semi_bit_t *emp_semi_integer_lt(emp_semi_ctx_t *p, emp_semi_integer_t *lhs, emp_semi_integer_t *rhs);
  emp_semi_bit_t *emp_semi_integer_lte(emp_semi_ctx_t *p, emp_semi_integer_t *lhs, emp_semi_integer_t *rhs);
  emp_semi_bit_t *emp_semi_integer_gt(emp_semi_ctx_t *p, emp_semi_integer_t *lhs, emp_semi_integer_t *rhs);
  emp_semi_integer_t *emp_semi_integer_cond(emp_semi_ctx_t *p, emp_semi_bit_t *guard, emp_semi_integer_t *lhs, emp_semi_integer_t *rhs);

#ifdef __cplusplus
}
#endif

#endif
