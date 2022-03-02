#ifndef SYMPHONY_TCPCHANNEL_H__
#define SYMPHONY_TCPCHANNEL_H__

#include <iostream>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <string>

#include "Channel.hpp"

#include <unistd.h>
#include <arpa/inet.h>
#include <sys/types.h>
#include <netinet/tcp.h>
#include <netinet/in.h>
#include <sys/socket.h>

const static size_t DEFAULT_BUFFER_SIZE = 1024 * 1024;

static void fail(const char *msg) {
  perror(msg);
  exit(EXIT_FAILURE);
}

static void set_nodelay(int sock) {
  const int one = 1;
  setsockopt(sock, IPPROTO_TCP, TCP_NODELAY, &one, sizeof(int));
}

static FILE *mk_stream(int sock) {
  FILE *ret = fdopen(sock, "wb+");
  if (ret == NULL) { fail("mk_stream (fdopen): impossible"); }
  return ret;
}

static uint8_t *mk_buffer(size_t buffer_size) {
  uint8_t *ret = new uint8_t[buffer_size];
  if (ret == NULL) { fail("mk_buffer (new): impossible"); }
  memset(ret, 0, buffer_size);
  return ret;
}

static void buffer_with(FILE *conn, uint8_t *buf, size_t size) {
  int err = setvbuf(conn, (char *) buf, _IOFBF, size);
  if (err != 0) { fail("buffer_with (setvbuf): impossible"); }
}

class TCPChannel : public Channel {
private:
  bool dirty;
  uint8_t *buffer;
  FILE *conn;

  // Initialize a TCP channel from an existing socket
  void init_socket(int sock, size_t buffer_size) {
    this->conn   = mk_stream(sock);
    this->buffer = mk_buffer(buffer_size);
    buffer_with(this->conn, this->buffer, buffer_size);
  }

  // Initialize a TCP channel as the client
  void init_client(const char *address, int port, size_t buffer_size) {
    if (port < 0 || port > 65535) {
      fail("init_client (port): impossible");
    }

    struct sockaddr_in server;
    memset(&server, 0, sizeof(server));
    server.sin_family      = AF_INET;
    server.sin_addr.s_addr = inet_addr(address);
    server.sin_port        = htons(port);

    int sock;
    while (true) {
      sock = socket(AF_INET, SOCK_STREAM, 0);
      int err = connect(sock, (struct sockaddr *) &server, sizeof(struct sockaddr));

      if (err == 0) { break; }

      close(sock);
      usleep(250);
    }

    set_nodelay(sock);
    this->init_socket(sock, buffer_size);
  }

  // Initialize a TCP channel as the server
  void init_server(int port, size_t buffer_size) {
    if (port < 0 || port > 65535) {
      fail("init_server (port): impossible");
    }

    struct sockaddr_in server;
    memset(&server, 0, sizeof(server));
    server.sin_family      = AF_INET;
    server.sin_addr.s_addr = htonl(INADDR_ANY);
    server.sin_port        = htons(port);

    int server_sock = socket(AF_INET, SOCK_STREAM, 0);
    int reuse = 1;
    setsockopt(server_sock, SOL_SOCKET, SO_REUSEADDR, (const uint8_t *) &reuse, sizeof(reuse));

    int err;
    err = bind(server_sock, (struct sockaddr *) &server, sizeof(struct sockaddr));
    if (err != 0) { fail("init_server (bind): impossible"); }

    err = listen(server_sock, 1);
    if (err != 0) { fail("init_server (listen): impossible"); }

    struct sockaddr_in client;
    socklen_t client_size = sizeof(client);
    int client_sock = accept(server_sock, (struct sockaddr *) &client, &client_size);
    if (err < 0) { fail("init_server (accept): impossible"); }
    close(server_sock);

    init_socket(client_sock, buffer_size);
  }

public:
  TCPChannel(const char *address, int port, size_t buffer_size = DEFAULT_BUFFER_SIZE) {
    this->dirty = false;
    this->init_client(address, port, buffer_size);
  }

  TCPChannel(int port, size_t buffer_size = DEFAULT_BUFFER_SIZE) {
    this->dirty = false;
    this->init_server(port, buffer_size);
  }

  ~TCPChannel(){
    this->flush();
    fclose(this->conn);
    delete[] this->buffer;
  }

  void send_all(const void *data, size_t size) {
    uint8_t *tmp = (uint8_t *) data;
    size_t total_sent = 0;

    while (total_sent < size) {
      int sent = fwrite(tmp + total_sent, 1, size - total_sent, this->conn);
      if (0 < sent) {
        total_sent += sent;
      } else {
        perror("send_all: impossible");
        exit(EXIT_FAILURE);
      }
    }

    this->dirty = true;
  }

  void recv_all(void *buf, size_t size) {
    if (this->dirty) {
      this->flush();
      this->dirty = false;
    }

    uint8_t *tmp = (uint8_t *) buf;
    size_t total_read = 0;

    while (total_read < size) {
      size_t read = fread(tmp + total_read, 1, size - total_read, this->conn);
      if (0 < read) {
        total_read += read;
      } else {
        perror("recv_all: impossible");
        exit(EXIT_FAILURE);
      }
    }
  }

  void flush() {
    fflush(this->conn);
  }
};

#endif
