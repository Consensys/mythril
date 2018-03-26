Truffle Hello World Demo
========================

```
npm install -g truffle ethereumjs-testrpc
```

This repo is created by following commands:

```
truffle init
truffle compile
```

In order to run `truffle migrate`, we need to setup `truffle.js` first:

```
networks: {
  development: {
    host: "localhost",
    port: 8545,
    network_id: "*" // Match any network id
  }
}
```

Resources
---------

- <https://medium.com/etherereum-salon/eth-testing-472c2f73b4c3>
