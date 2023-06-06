variable "REGISTRY" {
  default = "docker.io"
}

variable "VERSION" {
  default = "dev"
}

variable "PYTHON_VERSION" {
  default = "3.10"
}

variable "INSTALLED_SOLC_VERSIONS" {
  default = "0.8.19"
}

function "myth-tags" {
  params = [NAME]
  result = formatlist("${REGISTRY}/${NAME}:%s", split(",", VERSION))
}

group "default" {
  targets = ["myth", "myth-smoke-test"]
}

target "_myth-base" {
  target = "myth"
  args = {
    PYTHON_VERSION = PYTHON_VERSION
    INSTALLED_SOLC_VERSIONS = INSTALLED_SOLC_VERSIONS
  }
  platforms = [
    "linux/amd64",
    "linux/arm64"
  ]
}

target "myth" {
  inherits = ["_myth-base"]
  tags = myth-tags("mythril/myth")
}

target "myth-dev" {
  inherits = ["_myth-base"]
  tags = myth-tags("mythril/myth-dev")
}

target "myth-smoke-test" {
  inherits = ["_myth-base"]
  target = "myth-smoke-test"
  output = ["build/docker/smoke-test"]
}
