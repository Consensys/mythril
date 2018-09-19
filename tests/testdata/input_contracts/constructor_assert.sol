pragma solidity ^0.4.24;

contract AssertFail {

	constructor(uint8 var1){
		assert(var1>0);
	}
}
