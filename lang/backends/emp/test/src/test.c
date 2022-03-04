#include <stdlib.h>
#include <stdio.h>
#include "symphony/emp.h"

#define A 0
#define B 1
#define C 2
#define D 3
#define E 4

static int base_port = 12345;
static uint16_t me;
static channel_t *channels[5];

bool i_am(uint16_t party) {
  return me == party;
}

int port_of(uint16_t p1, uint16_t p2) {
  int gauss  = (p1 + 1) * (p1 + 2) / 2;
  int offset = 5 * p1 + p2 - gauss;
  return base_port + offset;
}

void setup() {
  for (int i = 0; i < 5; i++) {
    if (i_am(i)) { continue; }

    if (me < i) {
      channels[i] = tcp_channel_create_server(port_of(me, i));
    } else {
      channels[i] = tcp_channel_create_client("127.0.0.1", port_of(i, me));
    }
  }
}

void teardown() {
  for (int i = 0; i < 5; i++) {
    if (i_am(i)) { continue; }
    channel_destroy(channels[i]);
  }
}

int main(int argc, char **argv) {
  me = atoi(argv[1]);
  setup();

  if (i_am(A) || i_am(B)) {
    bool input = atoi(argv[2]);
    channel_t *to[2] = { channels[C], channels[D] };
    emp_semi_bit_send_share(input, to);
  }

  if (i_am(C) || i_am(D)) {
    emp_semi_ctx_t *p;
    emp_semi_bit_t *v1, *v2, *v3;

    if (i_am(C)) {
      p  = emp_semi_ctx_create(1, channels[D]);
    }

    if (i_am(D)) {
      p = emp_semi_ctx_create(2, channels[C]);
    }

    v1 = emp_semi_bit_recv_share(p, channels[A]);
    v2 = emp_semi_bit_recv_share(p, channels[B]);
    v3 = emp_semi_bit_xor(p, v1, v2);
    emp_semi_bit_send_reveal(p, v3, channels[E]);

    emp_semi_bit_destroy(v3);
    emp_semi_bit_destroy(v2);
    emp_semi_bit_destroy(v1);
    emp_semi_ctx_destroy(p);
  }

  if (i_am(E)) {
    channel_t *from[2] = { channels[C], channels[D] };
    bool output = emp_semi_bit_recv_reveal(from);
    printf("%d\n", output);
  }

  teardown();

  return 0;
}
