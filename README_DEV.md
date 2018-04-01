For Developers
===============

## Running tests

### python version

First, make sure your python version is `3.6.x`. Some tests will fail with `3.5.x` since some generated easm code is different from `3.6.x`.

### truffle

In the tests, we tested the command `--truffle`, which required the `truffle` command is installed.

```
npm install -g truffle
```

### geth

In order to run tests and coverage reports, you need to run `geth` locally, since some tests depend on it.

Install `geth` from here: <https://github.com/ethereum/go-ethereum/wiki/Building-Ethereum>

Then you can run `geth version` and if you see `Version: 1.8.2-stable` or above, it's OK for testing.

Don't forget to run `geth account new` to generate an account for you if this is the first time you use it.

Then start it like this:

```
geth --syncmode full --rpc --shh --debug
```

We use `--syncmode full` here because the `eth.blockNumber` will get increased soon in this mode, which is useful in tests.

If there is no error thrown, you can wait 1 or 2 minutes before running tests.

And you need to check `eth.coinbase` has no error thrown and `eth.blockNumber` should greater than `0`:

```
$ geth attach
> eth.coinbase
> eth.blockNumber
```

### Run the tests

```bash
pip3 install -r requirements.txt
./all_tests.sh
```

It may cost you about 3 minutes to run all the tests.

The tests may save their outputs content to `./tests/testdata/outputs_current/`, you can compare the files between it and `./tests/testdata/outputs_expected/` to see the difference if there is any changes.

If you think the changes are expected, you can just copy them to `outputs_expected` and commit them as new expected outputs.

The `./tests/testdata/outputs_current/` directory is deleted and recreated in `all_tests.sh` and `coverage_report.sh` each time.

### Generating test coverage report 

```bash
./coverage_report.sh
```

It will generate a coverage testing report `coverage_html_report/index.html`, which will be automatically opened in browser. You can find coverage rate and tested/missing code from the report.

Notice there are some tests are running by shell commands(`tests/cmd_line_test.py`), not calling by python, so they are not included in the coverage analysis.

It may cost you about 5 minutes to generate the report.
