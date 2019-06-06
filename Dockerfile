FROM ubuntu:bionic

# Space-separated version string without leading 'v' (e.g. "0.4.21 0.4.22") 
ARG SOLC

RUN apt-get update \
  && apt-get install -y \
     libsqlite3-0 \
     libsqlite3-dev \
  && apt-get install -y \
     build-essential \
     locales \
     python-pip-whl=9.0.1-2 \
     python3-pip=9.0.1-2 \
     python3-setuptools \
     software-properties-common \
  && add-apt-repository -y ppa:ethereum/ethereum \
  && apt-get update \
  && apt-get install -y \
     solc \
     libssl-dev \
     python3-dev \
     pandoc \
     git \
     wget \
  && ln -s /usr/bin/python3 /usr/local/bin/python

COPY ./requirements.txt /opt/mythril/requirements.txt

RUN cd /opt/mythril \
  && pip3 install -r requirements.txt

RUN locale-gen en_US.UTF-8
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US.en
ENV LC_ALL en_US.UTF-8

COPY . /opt/mythril
RUN cd /opt/mythril \
  && python setup.py install

WORKDIR /home/mythril

RUN ( [ ! -z "${SOLC}" ] && set -e && for ver in $SOLC; do python -m solc.install v${ver}; done ) || true

COPY ./mythril/support/assets/signatures.db /home/mythril/.mythril/signatures.db

ENTRYPOINT ["/usr/local/bin/myth"]
