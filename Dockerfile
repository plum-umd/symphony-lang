FROM ubuntu:20.04
ENV TZ=America/New_York
RUN ln -snf /usr/share/zoneinfo/$TZ /etc/localtime && echo $TZ > /etc/timezone
RUN apt-get update && \
    apt-get install -yy \
    sudo \
    wget \
    python \
    xxd \
    git

WORKDIR /deps

# EMP
RUN wget https://raw.githubusercontent.com/emp-toolkit/emp-readme/master/scripts/install.py && \
    python install.py --deps --tool --ot --sh2pc

# EMP C Wrapper
RUN git clone https://github.com/Isweet/emp-c.git
WORKDIR emp-c/build
RUN cmake .. && make && \
    cp ../src/empc.h /usr/local/include && \
    cp libempc.so /usr/local/lib

# Haskell / STACK
RUN wget -qO- https://get.haskellstack.org/ | sh

# Allyn Deps
RUN git clone https://github.com/Isweet/allyn-lang.git
WORKDIR allyn-lang
RUN stack build --only-dependencies --extra-include-dirs=/usr/local/include --extra-lib-dirs=/usr/local/lib

RUN rm -rf /deps

WORKDIR /allyn-lang
