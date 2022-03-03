#include <cstdlib>

// USES
#include "symphony/util/Channel.hpp"

// PROVIDES
#include "symphony/util/channel.h"

void channel_destroy(channel_t *chan) {
  delete static_cast<Channel *>(chan->obj);
  free(chan);
}

void send_all(channel_t *chan, const void *data, size_t size) {
  Channel *o = static_cast<Channel *>(chan->obj);
  o->send_all(data, size);
}

void recv_all(channel_t *chan, void *buf, size_t size) {
  Channel *o = static_cast<Channel *>(chan->obj);
  o->recv_all(buf, size);
}

void flush(channel_t *chan) {
  Channel *o = static_cast<Channel *>(chan->obj);
  o->flush();
}

void send_bool(channel_t *chan, bool b) {
  Channel *o = static_cast<Channel *>(chan->obj);
  o->send_bool(b);
}

bool recv_bool(channel_t *chan) {
  Channel *o = static_cast<Channel *>(chan->obj);
  return o->recv_bool();
}

void send_int64(channel_t *chan, int64_t z) {
  Channel *o = static_cast<Channel *>(chan->obj);
  o->send_int64(z);
}

int64_t recv_int64(channel_t *chan) {
  Channel *o = static_cast<Channel *>(chan->obj);
  return o->recv_int64();
}
