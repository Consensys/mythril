
FROM ubuntu:16.04

RUN apt-get update 
RUN apt-get install -y wget pandoc python3 git gcc python3-dev build-essential libssl-dev python3-pip python3-setuptools


RUN git clone https://github.com/b-mueller/mythril/
RUN pip3 install laser-ethereum
RUN (cd mythril &&  python3 setup.py install)
RUN (mkdir ~/.mythril && cd ~/.mythril && wget https://raw.githubusercontent.com/b-mueller/mythril/master/signatures.json)

WORKDIR /mythril

ENTRYPOINT [“myth”]
