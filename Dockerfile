FROM ubuntu:rolling

COPY . .

RUN apt-get update \
  && apt-get install -y software-properties-common python-software-properties \
  && add-apt-repository -y ppa:ethereum/ethereum \
  && apt-get update \
  && apt-get install -y solc \
  && apt-get install -y libssl-dev \
  && apt-get install -y python3-pip python3-dev \
  && ln -s /usr/bin/python3 /usr/local/bin/python \
  && pip3 install --upgrade pip \
  && apt-get install -y pandoc \
  && apt-get install -y git \
  && pip3 install -r requirements.txt \
  && python setup.py install

CMD []
