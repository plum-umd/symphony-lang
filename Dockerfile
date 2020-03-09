FROM ubuntu

WORKDIR /psl

RUN : \
  && export DEBIAN_FRONTEND=noninteractive \
  && apt-get -qy update \
  && apt-get -qy install curl \
  && curl -sSL -o install_stack https://get.haskellstack.org/ \
  && sh install_stack \
  && stack install ghcid \
;

COPY Makefile Makefile
COPY main main
COPY package.yaml package.yaml
COPY src src
COPY stack.yaml stack.yaml
COPY tests tests

RUN make build
