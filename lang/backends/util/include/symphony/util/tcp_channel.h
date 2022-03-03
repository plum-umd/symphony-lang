#ifndef SYMPHONY_C_TCP_CHANNEL_H__
#define SYMPHONY_C_TCP_CHANNEL_H__

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

#include "channel.h"

#ifdef __cplusplus
extern "C" {
#endif

  channel_t *tcp_channel_create_client(const char *address, uint16_t port);
  channel_t *tcp_channel_create_server(uint16_t port);

#ifdef __cplusplus
}
#endif

#endif
