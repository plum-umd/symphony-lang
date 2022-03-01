#include "backend-emp.h"
#include "emp-sh2pc/emp-sh2pc.h"
#include <immintrin.h>

using namespace emp;

ssize_t send_all(int socket, const void *buf, size_t len, int flags) {
  ssize_t left = len;
  const uint8_t *buf_bytes = (uint8_t *) buf;

  ssize_t sent = 0;
  while (0 < left) {
    sent = send(socket, buf_bytes + (len - left), left, flags);

    if (sent < 0) { return sent; }

    left -= sent;
  }

  return len;
}

void send_bool(int socket, bool b, int flags) {
  ssize_t sent = send_all(socket, &b, sizeof(bool), flags);

  if (sent < 0) { perror("send_bool: impossible"); }
}

void send_int64(int socket, int64_t v, int flags) {
  ssize_t sent = send_all(socket, &v, sizeof(int64_t), flags);

  if (sent < 0) { perror("send_int64: impossible"); }
}

bool recv_bool(int socket, int flags) {
  bool b;
  ssize_t received = recv(socket, &b, sizeof(bool), flags);

  if (received != sizeof(bool)) { perror("recv_bool: impossible"); }

  return b;
}

int64_t recv_int64(int socket, int flags) {
  int64_t v;
  ssize_t received = recv(socket, &v, sizeof(int64_t), flags);

  if (received != sizeof(int64_t)) { perror("recv_int64: impossible"); }

  return v;
}

/*
  ----------------------
  --- NetIO Channels ---
  ----------------------
*/

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

// TODO: Replace with XOR sharing written by ... someone else.
//       I am committing a cardinal sin by implementing my own crypto.

// INPUT -> {COMPUTE}
void emp_semi_bit_send_share(bool b, int *sockets, size_t size) {
  bool *shares = (bool *) malloc(size * sizeof(bool));
  bool sum = 0;

  size_t i;
  PRG prg;
  for (i = 0; i < size - 1; i++) {
    bool tmp;
    prg.random_bool(&tmp, 1);
    shares[i] = tmp;
    sum ^= tmp;
  }

  shares[i] = b ^ sum;

  for (i = 0; i < size; i++) {
    send_bool(sockets[i], shares[i], 0);
  }

  free(shares);
}

// {COMPUTE} <- INPUT
emp_semi_bit_t *emp_semi_bit_recv_share(emp_semi_ctx_t *p, int socket) {
  emp_install(p);

  emp_semi_bit_t *v = (emp_semi_bit_t *) malloc(sizeof(emp_semi_bit_t));
  *v = emp_semi_bit_recv_share_stack(p, socket);

  return v;
}

// {COMPUTE} <- INPUT
emp_semi_bit_t emp_semi_bit_recv_share_stack(emp_semi_ctx_t *p, int socket) {
  emp_install(p);

  bool my_sh = recv_bool(socket, 0);
  emp_semi_bit_t sh1 = emp_semi_bit_share_stack(p, 0, my_sh);
  emp_semi_bit_t sh2 = emp_semi_bit_share_stack(p, 1, my_sh);

  Bit sh1_bit(_mm_loadu_si128((__m128i *) sh1.obj));
  Bit sh2_bit(_mm_loadu_si128((__m128i *) sh2.obj));

  emp_semi_bit_t v;
  _mm_storeu_si128((__m128i *) v.obj, (sh1_bit ^ sh2_bit).bit);

  return v;
}

// {COMPUTE} <-> {COMPUTE}
emp_semi_bit_t emp_semi_bit_share_stack(emp_semi_ctx_t *p, int8_t party, bool b) {
  emp_install(p);

  Bit tmp(b, party);

  emp_semi_bit_t v;
  _mm_storeu_si128((__m128i *) v.obj, tmp.bit);

  return v;
}

// {COMPUTE} <-> {COMPUTE}
emp_semi_bit_t *emp_semi_bit_share(emp_semi_ctx_t *p, int8_t party, bool b) {
  emp_install(p);

  emp_semi_bit_t *v = (emp_semi_bit_t *) malloc(sizeof(emp_semi_bit_t));
  *v = emp_semi_bit_share_stack(p, party, b);

  return v;
}

// {COMPUTE} -> OUTPUT
void emp_semi_bit_send_reveal(emp_semi_ctx_t *p, emp_semi_bit_t *v, int socket) {
  emp_install(p);

  emp_semi_bit_send_reveal_stack(p, *v, socket);
}

// {COMPUTE} -> OUTPUT
void emp_semi_bit_send_reveal_stack(emp_semi_ctx_t *p, emp_semi_bit_t v, int socket) {
  emp_install(p);

  Bit v0(_mm_loadu_si128((__m128i *) v.obj));
  bool my_sh = v0.reveal<bool>(XOR); // See: https://github.com/emp-toolkit/emp-sh2pc/blob/master/emp-sh2pc/sh_gen.h#L61

  send_bool(socket, my_sh, 0);
}

// OUTPUT <- {COMPUTE}
bool emp_semi_bit_recv_reveal(int *sockets, size_t size) {
  bool result = 0;

  for (size_t i = 0; i < size; i++) {
    result ^= recv_bool(sockets[i], 0);
  }

  return result;
}

// {COMPUTE} <-> {COMPUTE}
bool emp_semi_bit_reveal(emp_semi_ctx_t *p, int8_t party, emp_semi_bit_t *v) {
  emp_install(p);

  return emp_semi_bit_reveal_stack(p, party, *v);
}

// {COMPUTE} <-> {COMPUTE}
bool emp_semi_bit_reveal_stack(emp_semi_ctx_t *p, int8_t party, emp_semi_bit_t v) {
  emp_install(p);

  Bit v0(_mm_loadu_si128((__m128i *) v.obj));
  bool ret = v0.reveal<bool>(party);

  return ret;
}

void emp_semi_bit_destroy(emp_semi_bit_t *v) {
  if (v == NULL) { return; }

  free(v);

  return;
}


/*
  --------------------------
  ---- Stack Allocation ----
  --------------------------
*/

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

struct emp_semi_int64 {
  void *obj;
};


// TODO: Replace with XOR sharing written by ... someone else.
//       I am committing a cardinal sin by implementing my own crypto.

// INPUT -> {COMPUTE}
void emp_semi_int64_send_share(int64_t v, int *sockets, size_t size) {
  int64_t *shares = (int64_t *) malloc(size * sizeof(int64_t));
  int64_t sum = 0;

  size_t i;
  PRG prg;
  for (i = 0; i < size - 1; i++) {
    int64_t tmp;
    prg.random_data_unaligned(&tmp, sizeof(int64_t));
    shares[i] = tmp;
    sum ^= tmp;
  }

  shares[i] = v ^ sum;

  for (i = 0; i < size; i++) {
    send_int64(sockets[i], shares[i], 0);
  }

  free(shares);
}

// {COMPUTE} <- INPUT
emp_semi_int64_t *emp_semi_int64_recv_share(emp_semi_ctx_t *p, int socket) {
  emp_install(p);

  int64_t my_sh = recv_int64(socket, 0);
  emp_semi_int64_t *sh1 = emp_semi_int64_share(p, 0, my_sh);
  emp_semi_int64_t *sh2 = emp_semi_int64_share(p, 1, my_sh);

  Integer *sh1_int64 = static_cast<Integer *>(sh1->obj);
  Integer *sh2_int64 = static_cast<Integer *>(sh2->obj);

  emp_semi_int64_t *v = (emp_semi_int64_t *) malloc(sizeof(emp_semi_int64_t));
  v->obj = new Integer(*sh1_int64 ^ *sh2_int64);

  return v;
}

// {COMPUTE} <-> {COMPUTE}
emp_semi_int64_t *emp_semi_int64_share(emp_semi_ctx_t *p, int8_t party, int64_t v) {
  emp_install(p);

  emp_semi_int64_t *v0 = (emp_semi_int64_t *) malloc(sizeof(emp_semi_int64_t));
  v0->obj = new Integer(64, v, party);

  return v0;
}

// {COMPUTE} -> OUTPUT
void emp_semi_int64_send_reveal(emp_semi_ctx_t *p, emp_semi_int64_t *v, int socket) {
  emp_install(p);

  Integer *v0 = static_cast<Integer *>(v->obj);
  int64_t my_sh = v0->reveal<int64_t>(XOR); // See: https://github.com/emp-toolkit/emp-sh2pc/blob/master/emp-sh2pc/sh_gen.h#L61

  send_int64(socket, my_sh, 0);
}

// OUTPUT <- {COMPUTE}
int64_t emp_semi_int64_recv_reveal(int *sockets, size_t size) {
  int64_t result = 0;

  for (size_t i = 0; i < size; i++) {
    result ^= recv_int64(sockets[i], 0);
  }

  return result;
}

// {COMPUTE} <-> {COMPUTE}
int64_t emp_semi_int64_reveal(emp_semi_ctx_t *p, int8_t party, emp_semi_int64_t *v) {
  emp_install(p);

  Integer *v0 = static_cast<Integer *>(v->obj);
  int64_t ret = v0->reveal<int64_t>(party);

  return ret;
}

void emp_semi_int64_destroy(emp_semi_int64_t *v) {
  if (v == NULL) { return; }

  delete static_cast<Integer *>(v->obj);
  free(v);

  return;
}

emp_semi_int64_t *emp_semi_int64_add(emp_semi_ctx_t *p, emp_semi_int64_t *lhs, emp_semi_int64_t *rhs) {
  emp_install(p);

  Integer *lhs0 = static_cast<Integer *>(lhs->obj);
  Integer *rhs0 = static_cast<Integer *>(rhs->obj);

  emp_semi_int64_t *v;
  v      = (emp_semi_int64_t *) malloc(sizeof(emp_semi_int64_t));
  v->obj = new Integer(*lhs0 + *rhs0);

  return v;
}

emp_semi_int64_t *emp_semi_int64_mult(emp_semi_ctx_t *p, emp_semi_int64_t *lhs, emp_semi_int64_t *rhs) {
  emp_install(p);

  Integer *lhs0 = static_cast<Integer *>(lhs->obj);
  Integer *rhs0 = static_cast<Integer *>(rhs->obj);

  emp_semi_int64_t *v;
  v      = (emp_semi_int64_t *) malloc(sizeof(emp_semi_int64_t));
  v->obj = new Integer(*lhs0 * *rhs0);

  return v;
}

emp_semi_int64_t *emp_semi_int64_sub(emp_semi_ctx_t *p, emp_semi_int64_t *lhs, emp_semi_int64_t *rhs) {
  emp_install(p);

  Integer *lhs0 = static_cast<Integer *>(lhs->obj);
  Integer *rhs0 = static_cast<Integer *>(rhs->obj);

  emp_semi_int64_t *v;
  v      = (emp_semi_int64_t *) malloc(sizeof(emp_semi_int64_t));
  v->obj = new Integer(*lhs0 - *rhs0);

  return v;
}

emp_semi_int64_t *emp_semi_int64_div(emp_semi_ctx_t *p, emp_semi_int64_t *lhs, emp_semi_int64_t *rhs) {
  emp_install(p);

  Integer *lhs0 = static_cast<Integer *>(lhs->obj);
  Integer *rhs0 = static_cast<Integer *>(rhs->obj);

  emp_semi_int64_t *v;
  v      = (emp_semi_int64_t *) malloc(sizeof(emp_semi_int64_t));
  v->obj = new Integer(*lhs0 / *rhs0);

  return v;
}

emp_semi_int64_t *emp_semi_int64_mod(emp_semi_ctx_t *p, emp_semi_int64_t *lhs, emp_semi_int64_t *rhs) {
  emp_install(p);

  Integer *lhs0 = static_cast<Integer *>(lhs->obj);
  Integer *rhs0 = static_cast<Integer *>(rhs->obj);

  emp_semi_int64_t *v;
  v      = (emp_semi_int64_t *) malloc(sizeof(emp_semi_int64_t));
  v->obj = new Integer(*lhs0 % *rhs0);

  return v;
}

emp_semi_bit_t *emp_semi_int64_eq(emp_semi_ctx_t *p, emp_semi_int64_t *lhs, emp_semi_int64_t *rhs) {
  emp_install(p);

  Integer *lhs0 = static_cast<Integer *>(lhs->obj);
  Integer *rhs0 = static_cast<Integer *>(rhs->obj);


  emp_semi_bit_t *v;
  v      = (emp_semi_bit_t *) malloc(sizeof(emp_semi_bit_t));
  _mm_storeu_si128((__m128i *) v->obj, (*lhs0 == *rhs0).bit);

  return v;
}

emp_semi_bit_t *emp_semi_int64_lt(emp_semi_ctx_t *p, emp_semi_int64_t *lhs, emp_semi_int64_t *rhs) {
  emp_install(p);

  Integer *lhs0 = static_cast<Integer *>(lhs->obj);
  Integer *rhs0 = static_cast<Integer *>(rhs->obj);

  emp_semi_bit_t *v;
  v      = (emp_semi_bit_t *) malloc(sizeof(emp_semi_bit_t));
  _mm_storeu_si128((__m128i *) v->obj, (*lhs0 < *rhs0).bit);

  return v;
}

emp_semi_bit_t *emp_semi_int64_lte(emp_semi_ctx_t *p, emp_semi_int64_t *lhs, emp_semi_int64_t *rhs) {
  emp_install(p);

  Integer *lhs0 = static_cast<Integer *>(lhs->obj);
  Integer *rhs0 = static_cast<Integer *>(rhs->obj);

  emp_semi_bit_t *v;
  v      = (emp_semi_bit_t *) malloc(sizeof(emp_semi_bit_t));
  _mm_storeu_si128((__m128i *) v->obj, (*lhs0 <= *rhs0).bit);

  return v;
}

emp_semi_bit_t *emp_semi_int64_gt(emp_semi_ctx_t *p, emp_semi_int64_t *lhs, emp_semi_int64_t *rhs) {
  emp_install(p);

  Integer *lhs0 = static_cast<Integer *>(lhs->obj);
  Integer *rhs0 = static_cast<Integer *>(rhs->obj);

  emp_semi_bit_t *v;
  v      = (emp_semi_bit_t *) malloc(sizeof(emp_semi_bit_t));
  _mm_storeu_si128((__m128i *) v->obj, (*lhs0 > *rhs0).bit);

  return v;
}

emp_semi_int64_t *emp_semi_int64_cond(emp_semi_ctx_t *p, emp_semi_bit_t *guard, emp_semi_int64_t *lhs, emp_semi_int64_t *rhs) {
  emp_install(p);

  Bit guard0(_mm_loadu_si128((__m128i *) guard->obj));
  Integer *lhs0 = static_cast<Integer *>(lhs->obj);
  Integer *rhs0 = static_cast<Integer *>(rhs->obj);

  emp_semi_int64_t *v;
  v      = (emp_semi_int64_t *) malloc(sizeof(emp_semi_int64_t));
  v->obj= new Integer(If(guard0, *lhs0, *rhs0));

  return v;
}
