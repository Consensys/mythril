#!/bin/bash

set -eo pipefail

NAME=$1

if [[ ! $NAME =~ ^mythril/myth(-dev)?$ ]];
then
  echo "Error: unknown image name: $NAME" >&2
  exit 1
fi

if [ ! -z $CIRCLE_TAG ];
then
  GIT_VERSION=${CIRCLE_TAG#?}
else
  GIT_VERSION=${CIRCLE_SHA1}
fi

export DOCKER_BUILDKIT=1
docker buildx create --use

# Build and test all versions of the image. (The result will stay in the cache,
# so the next build should be almost instant.)
docker buildx bake myth-smoke-test

echo "$DOCKERHUB_PASSWORD" | docker login -u $DOCKERHUB_USERNAME --password-stdin

# strip mythril/ from NAME, e.g. myth or myth-dev
BAKE_TARGET="${NAME#mythril/}"

VERSION="${GIT_VERSION:?},latest" docker buildx bake --push "${BAKE_TARGET:?}"
