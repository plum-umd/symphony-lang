#ifndef SYMPHONY_C_CHANNEL_H__
#define SYMPHONY_C_CHANNEL_H__

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

  struct channel {
    void *obj;
  };
  typedef struct channel channel_t;

  void channel_destroy(channel_t *chan);

  void send_all(channel_t *chan, const void *data, size_t size);
  void recv_all(channel_t *chan, void *buf, size_t size);
  void flush(channel_t *chan);

  void send_bool(channel_t *chan, bool b);
  bool recv_bool(channel_t *chan);
  void send_int64(channel_t *chan, int64_t z);
  int64_t recv_int64(channel_t *chan);

#ifdef __cplusplus
}
#endif

#endif
