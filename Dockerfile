FROM ubuntu:bionic

RUN apt-get update \
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

ENTRYPOINT ["/usr/local/bin/myth"]
