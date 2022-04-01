#!/bin/sh

set -eo pipefail

NAME=$1

if [ ! -z $CIRCLE_TAG ];
then
  VERSION=${CIRCLE_TAG#?}
else
  VERSION=${CIRCLE_SHA1}
fi

VERSION_TAG=${NAME}:${VERSION}
LATEST_TAG=${NAME}:latest

docker build -t ${VERSION_TAG} .
docker tag ${VERSION_TAG} ${LATEST_TAG}

echo "$DOCKERHUB_PASSWORD" | docker login -u $DOCKERHUB_USERNAME --password-stdin

docker push ${VERSION_TAG}
docker push ${LATEST_TAG}
