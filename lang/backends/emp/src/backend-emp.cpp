#include "backend-emp.h"
#include "emp-sh2pc/emp-sh2pc.h"
#include <immintrin.h>

using namespace emp;

struct netio {
  void *obj;
};

netio_t *netio_create(const char *address, int port, bool quiet) {
  netio_t *io;

  io      = (netio_t *) malloc(sizeof(netio_t));
  io->obj = new NetIO(address, port, quiet);

  return io;
}

void netio_destroy(netio_t *io) {
  if (io == NULL) {
    return;
  }

  delete static_cast<NetIO *>(io->obj);
  free(io);
}

void netio_send(netio_t *io, void *data, size_t bytes) {
  NetIO *net = static_cast<NetIO *>(io->obj);
  net->send_data_internal(data, bytes);
}

void netio_recv(netio_t *io, void *data, size_t bytes) {
  NetIO *net = static_cast<NetIO *>(io->obj);
  net->recv_data_internal(data, bytes);
}

void netio_flush(netio_t *io) {
  NetIO *net = static_cast<NetIO *>(io->obj);
  net->flush();
}

/*
  --------------------
  --- EMP Contexts ---
  --------------------
*/

struct emp_semi_ctx {
  void *circ;
  void *prot;
};

emp_semi_ctx_t *emp_semi_ctx_create(int8_t party, netio_t *io) {
  NetIO *net = static_cast<NetIO *>(io->obj);

  emp_semi_ctx_t *p;

  p = (emp_semi_ctx_t *) malloc(sizeof(emp_semi_ctx_t));
  setup_semi_honest(net, party);
  p->circ = CircuitExecution::circ_exec;
  p->prot = ProtocolExecution::prot_exec;

  return p;
}

void emp_install(emp_semi_ctx_t *p) {
  CircuitExecution::circ_exec = static_cast<CircuitExecution *>(p->circ);
  ProtocolExecution::prot_exec = static_cast<ProtocolExecution *>(p->prot);

  return;
}

void emp_semi_ctx_destroy(emp_semi_ctx_t *p) {
  emp_install(p);
  finalize_semi_honest();
  free(p);

  return;
}

/*
  ----------------
  --- EMP Bits ---
  ----------------
*/

/*
  --------------------------
  ---- Stack Allocation ----
  --------------------------
*/

emp_semi_bit_t emp_semi_bit_create_stack(emp_semi_ctx_t *p, int8_t party, bool b) {
  emp_install(p);

  Bit tmp(b, party);

  emp_semi_bit_t v;
  _mm_storeu_si128((__m128i *) v.obj, tmp.bit);

  return v;
}

emp_semi_bit_t emp_semi_bit_xor_stack(emp_semi_ctx_t *p, emp_semi_bit_t *lhs, emp_semi_bit_t *rhs) {
  emp_install(p);

  Bit lhs0(_mm_loadu_si128((__m128i *) lhs->obj));
  Bit rhs0(_mm_loadu_si128((__m128i *) rhs->obj));

  emp_semi_bit_t v;
  _mm_storeu_si128((__m128i *) v.obj, (lhs0 ^ rhs0).bit);

  return v;
}

emp_semi_bit_t emp_semi_bit_and_stack(emp_semi_ctx_t *p, emp_semi_bit_t *lhs, emp_semi_bit_t *rhs) {
  emp_install(p);

  Bit lhs0(_mm_loadu_si128((__m128i *) lhs->obj));
  Bit rhs0(_mm_loadu_si128((__m128i *) rhs->obj));

  emp_semi_bit_t v;
  _mm_storeu_si128((__m128i *) v.obj, (lhs0 & rhs0).bit);

  return v;
}

emp_semi_bit_t emp_semi_bit_not_stack(emp_semi_ctx_t *p, emp_semi_bit_t *v) {
  emp_install(p);

  Bit b(_mm_loadu_si128((__m128i *) v->obj));

  emp_semi_bit_t v0;
  _mm_storeu_si128((__m128i *) v0.obj, (!b).bit);

  return v0;
}

emp_semi_bit_t emp_semi_bit_or_stack(emp_semi_ctx_t *p, emp_semi_bit_t *lhs, emp_semi_bit_t *rhs) {
  emp_install(p);

  Bit lhs0(_mm_loadu_si128((__m128i *) lhs->obj));
  Bit rhs0(_mm_loadu_si128((__m128i *) rhs->obj));

  emp_semi_bit_t v;
  _mm_storeu_si128((__m128i *) v.obj, (lhs0 | rhs0).bit);

  return v;
}

emp_semi_bit_t emp_semi_bit_cond_stack(emp_semi_ctx_t *p, emp_semi_bit_t *guard, emp_semi_bit_t *lhs, emp_semi_bit_t *rhs) {
  emp_install(p);

  Bit guard0(_mm_loadu_si128((__m128i *) guard->obj));
  Bit lhs0(_mm_loadu_si128((__m128i *) lhs->obj));
  Bit rhs0(_mm_loadu_si128((__m128i *) rhs->obj));

  emp_semi_bit_t v;
  _mm_storeu_si128((__m128i *) v.obj, If(guard0, lhs0, rhs0).bit);

  return v;
}

/*
  -------------------------
  ---- Heap Allocation ----
  -------------------------
*/

emp_semi_bit_t *emp_semi_bit_create(emp_semi_ctx_t *p, int8_t party, bool b) {
  emp_semi_bit_t *v = (emp_semi_bit_t *) malloc(sizeof(emp_semi_bit_t));
  *v = emp_semi_bit_create_stack(p, b, party);

  return v;
}

bool emp_semi_bit_reveal(emp_semi_ctx_t *p, int8_t party, emp_semi_bit_t *v) {
  emp_install(p);

  Bit v0(_mm_loadu_si128((__m128i *) v->obj));
  bool ret = v0.reveal<bool>(party);

  return ret;
}

void emp_semi_bit_destroy(emp_semi_bit_t *v) {
  if (v == NULL) {
    return;
  }

  free(v);

  return;
}

emp_semi_bit_t *emp_semi_bit_xor(emp_semi_ctx_t *p, emp_semi_bit_t *lhs, emp_semi_bit_t *rhs) {
  emp_semi_bit_t *v = (emp_semi_bit_t *) malloc(sizeof(emp_semi_bit_t));
  *v = emp_semi_bit_xor_stack(p, lhs, rhs);

  return v;
}

emp_semi_bit_t *emp_semi_bit_and(emp_semi_ctx_t *p, emp_semi_bit_t *lhs, emp_semi_bit_t *rhs) {
  emp_semi_bit_t *v = (emp_semi_bit_t *) malloc(sizeof(emp_semi_bit_t));
  *v = emp_semi_bit_and_stack(p, lhs, rhs);

  return v;
}

emp_semi_bit_t *emp_semi_bit_not(emp_semi_ctx_t *p, emp_semi_bit_t *v) {
  emp_semi_bit_t *v0 = (emp_semi_bit_t *) malloc(sizeof(emp_semi_bit_t));
  *v0 = emp_semi_bit_not_stack(p, v0);

  return v0;
}

emp_semi_bit_t *emp_semi_bit_or(emp_semi_ctx_t *p, emp_semi_bit_t *lhs, emp_semi_bit_t *rhs) {
  emp_semi_bit_t *v = (emp_semi_bit_t *) malloc(sizeof(emp_semi_bit_t));
  *v = emp_semi_bit_or_stack(p, lhs, rhs);

  return v;
}

emp_semi_bit_t *emp_semi_bit_cond(emp_semi_ctx_t *p, emp_semi_bit_t *guard, emp_semi_bit_t *lhs, emp_semi_bit_t *rhs) {
  emp_semi_bit_t *v = (emp_semi_bit_t *) malloc(sizeof(emp_semi_bit_t));
  *v = emp_semi_bit_cond_stack(p, guard, lhs, rhs);

  return v;
}

/*
  --------------------
  --- EMP Integers ---
  --------------------
*/

struct emp_semi_integer {
  void *obj;
};


emp_semi_integer_t *emp_semi_integer_create(emp_semi_ctx_t *p, int8_t party, uint16_t precision, int64_t v) {
  emp_install(p);

  emp_semi_integer_t *v0;

  v0      = (emp_semi_integer_t *) malloc(sizeof(emp_semi_integer_t));
  v0->obj = new Integer(precision, v, party);

  return v0;
}

int64_t emp_semi_integer_reveal(emp_semi_ctx_t *p, int8_t party, emp_semi_integer_t *v) {
  emp_install(p);

  Integer *v0 = static_cast<Integer *>(v->obj);
  int64_t ret = (*v0).reveal<int64_t>(party);

  return ret;
}

void emp_semi_integer_destroy(emp_semi_integer_t *v) {
  if (v == NULL) {
    return;
  }

  delete static_cast<Integer *>(v->obj);
  free(v);

  return;
}

emp_semi_integer_t *emp_semi_integer_add(emp_semi_ctx_t *p, emp_semi_integer_t *lhs, emp_semi_integer_t *rhs) {
  emp_install(p);

  Integer *lhs0 = static_cast<Integer *>(lhs->obj);
  Integer *rhs0 = static_cast<Integer *>(rhs->obj);

  emp_semi_integer_t *v;
  v      = (emp_semi_integer_t *) malloc(sizeof(emp_semi_integer_t));
  v->obj = new Integer(*lhs0 + *rhs0);

  return v;
}

emp_semi_integer_t *emp_semi_integer_mult(emp_semi_ctx_t *p, emp_semi_integer_t *lhs, emp_semi_integer_t *rhs) {
  emp_install(p);

  Integer *lhs0 = static_cast<Integer *>(lhs->obj);
  Integer *rhs0 = static_cast<Integer *>(rhs->obj);

  emp_semi_integer_t *v;
  v      = (emp_semi_integer_t *) malloc(sizeof(emp_semi_integer_t));
  v->obj = new Integer(*lhs0 * *rhs0);

  return v;
}

emp_semi_integer_t *emp_semi_integer_sub(emp_semi_ctx_t *p, emp_semi_integer_t *lhs, emp_semi_integer_t *rhs) {
  emp_install(p);

  Integer *lhs0 = static_cast<Integer *>(lhs->obj);
  Integer *rhs0 = static_cast<Integer *>(rhs->obj);

  emp_semi_integer_t *v;
  v      = (emp_semi_integer_t *) malloc(sizeof(emp_semi_integer_t));
  v->obj = new Integer(*lhs0 - *rhs0);

  return v;
}

emp_semi_integer_t *emp_semi_integer_div(emp_semi_ctx_t *p, emp_semi_integer_t *lhs, emp_semi_integer_t *rhs) {
  emp_install(p);

  Integer *lhs0 = static_cast<Integer *>(lhs->obj);
  Integer *rhs0 = static_cast<Integer *>(rhs->obj);

  emp_semi_integer_t *v;
  v      = (emp_semi_integer_t *) malloc(sizeof(emp_semi_integer_t));
  v->obj = new Integer(*lhs0 / *rhs0);

  return v;
}

emp_semi_integer_t *emp_semi_integer_mod(emp_semi_ctx_t *p, emp_semi_integer_t *lhs, emp_semi_integer_t *rhs) {
  emp_install(p);

  Integer *lhs0 = static_cast<Integer *>(lhs->obj);
  Integer *rhs0 = static_cast<Integer *>(rhs->obj);

  emp_semi_integer_t *v;
  v      = (emp_semi_integer_t *) malloc(sizeof(emp_semi_integer_t));
  v->obj = new Integer(*lhs0 % *rhs0);

  return v;
}

emp_semi_bit_t *emp_semi_integer_eq(emp_semi_ctx_t *p, emp_semi_integer_t *lhs, emp_semi_integer_t *rhs) {
  emp_install(p);

  Integer *lhs0 = static_cast<Integer *>(lhs->obj);
  Integer *rhs0 = static_cast<Integer *>(rhs->obj);


  emp_semi_bit_t *v;
  v      = (emp_semi_bit_t *) malloc(sizeof(emp_semi_bit_t));
  _mm_storeu_si128((__m128i *) v->obj, (*lhs0 == *rhs0).bit);

  return v;
}

emp_semi_bit_t *emp_semi_integer_lt(emp_semi_ctx_t *p, emp_semi_integer_t *lhs, emp_semi_integer_t *rhs) {
  emp_install(p);

  Integer *lhs0 = static_cast<Integer *>(lhs->obj);
  Integer *rhs0 = static_cast<Integer *>(rhs->obj);

  emp_semi_bit_t *v;
  v      = (emp_semi_bit_t *) malloc(sizeof(emp_semi_bit_t));
  _mm_storeu_si128((__m128i *) v->obj, (*lhs0 < *rhs0).bit);

  return v;
}

emp_semi_bit_t *emp_semi_integer_lte(emp_semi_ctx_t *p, emp_semi_integer_t *lhs, emp_semi_integer_t *rhs) {
  emp_install(p);

  Integer *lhs0 = static_cast<Integer *>(lhs->obj);
  Integer *rhs0 = static_cast<Integer *>(rhs->obj);

  emp_semi_bit_t *v;
  v      = (emp_semi_bit_t *) malloc(sizeof(emp_semi_bit_t));
  _mm_storeu_si128((__m128i *) v->obj, (*lhs0 <= *rhs0).bit);

  return v;
}

emp_semi_bit_t *emp_semi_integer_gt(emp_semi_ctx_t *p, emp_semi_integer_t *lhs, emp_semi_integer_t *rhs) {
  emp_install(p);

  Integer *lhs0 = static_cast<Integer *>(lhs->obj);
  Integer *rhs0 = static_cast<Integer *>(rhs->obj);

  emp_semi_bit_t *v;
  v      = (emp_semi_bit_t *) malloc(sizeof(emp_semi_bit_t));
  _mm_storeu_si128((__m128i *) v->obj, (*lhs0 > *rhs0).bit);

  return v;
}

emp_semi_integer_t *emp_semi_integer_cond(emp_semi_ctx_t *p, emp_semi_bit_t *guard, emp_semi_integer_t *lhs, emp_semi_integer_t *rhs) {
  emp_install(p);

  Bit guard0(_mm_loadu_si128((__m128i *) guard->obj));
  Integer *lhs0 = static_cast<Integer *>(lhs->obj);
  Integer *rhs0 = static_cast<Integer *>(rhs->obj);

  emp_semi_integer_t *v;
  v      = (emp_semi_integer_t *) malloc(sizeof(emp_semi_integer_t));
  v->obj= new Integer(If(guard0, *lhs0, *rhs0));

  return v;
}
