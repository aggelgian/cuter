FROM erlang:21.2-alpine
MAINTAINER pierrefenoll@gmail.com
WORKDIR /app
RUN set -x \
 && apk update && apk upgrade \
 && apk add py2-pip make git g++ \
 && pip install protobuf==3.2.0 parsimonious==0.7.0 \
 && git clone -b z3-4.8.3 --depth 1 https://github.com/Z3Prover/z3.git \
 && cd z3 && python scripts/mk_make.py --python && cd build && make -j7 && make install && z3 --version && cd /app \
 && git clone --depth 1 https://github.com/aggelgian/cuter.git && cd cuter \
 && git submodule init && git submodule update \
 && git submodule foreach make -j7 \
 && apk add protobuf autoconf && autoconf && ./configure --with-protoc=/usr/bin/protoc \
 && apk add bash && make depend && make \
 && rm -r /var/cache/apk/*
ENTRYPOINT ["/app/cuter/cuter"]
CMD ["lists", "sum", "'[[1]]'"]
