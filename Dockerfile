FROM ubuntu

ENV LC_ALL=C.UTF-8

WORKDIR /psl

RUN : \
  && export DEBIAN_FRONTEND=noninteractive \
  && apt-get -qy update \
  && apt-get -qy install curl make \
  && curl -sSL -o install_stack https://get.haskellstack.org/ \
  && sh install_stack \
;

COPY Makefile Makefile
COPY examples examples
COPY examples-data examples-data
COPY main main
COPY package.yaml package.yaml
COPY resources resources
COPY src src
COPY stack.yaml stack.yaml
COPY tests tests

RUN make build psli
