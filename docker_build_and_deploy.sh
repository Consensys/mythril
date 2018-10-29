#!/bin/sh

set -eo pipefail

NAME=$1

VERSION_TAG=${NAME}:${CIRCLE_TAG#?}
LATEST_TAG=${NAME}:latest

docker build -t ${VERSION_TAG} .
docker tag ${VERSION_TAG} ${LATEST_TAG}

docker login -u $DOCKERHUB_USERNAME -p $DOCKERHUB_PASSWORD

docker push ${VERSION_TAG}
docker push ${LATEST_TAG}
