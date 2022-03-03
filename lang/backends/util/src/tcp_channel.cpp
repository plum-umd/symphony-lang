// USES
#include "symphony/util/channel.h"
#include "symphony/util/TCPChannel.hpp"

// PROVIDES
#include "symphony/util/tcp_channel.h"

channel_t *tcp_channel_create_client(const char *address, uint16_t port) {
  channel_t *ret = (channel_t *) malloc(sizeof(channel_t));
  ret->obj = new TCPChannel(address, port);

  return ret;
}

channel_t *tcp_channel_create_server(uint16_t port) {
  channel_t *ret = (channel_t *) malloc(sizeof(channel_t));
  ret->obj = new TCPChannel(port);

  return ret;
}
