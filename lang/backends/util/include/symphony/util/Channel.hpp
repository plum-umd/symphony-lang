#ifndef SYMPHONY_CHANNEL_H__
#define SYMPHONY_CHANNEL_H__

#include <cstddef>
#include <cstdint>

class Channel {
public:
  virtual ~Channel() {}

  virtual void send_all(const void *data, size_t size) = 0;
  virtual void recv_all(void *buf, size_t size) = 0;
  virtual void flush() = 0;

  void send_bool(bool b) {
    this->send_all(&b, sizeof(bool));
  }

  bool recv_bool() {
    bool b;
    this->recv_all(&b, sizeof(bool));
    return b;
  }

  void send_int64(int64_t z) {
    this->send_all(&z, sizeof(int64_t));
  }

  int64_t recv_int64() {
    int64_t z;
    this->recv_all(&z, sizeof(int64_t));
    return z;
  }
};

#endif
