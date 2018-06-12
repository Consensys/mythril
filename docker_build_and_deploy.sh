#!/bin/sh

VERSION=${CIRCLE_TAG#?}
docker build -t mythril/mythril:${VERSION} .
docker login -u $DOCKERHUB_USERNAME -p $DOCKERHUB_PASSWORD
docker push mythril/mythril:${VERSION}
