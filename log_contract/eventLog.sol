pragma solidity ^0.4.23;

contract Test {
    event replace(string indexed log, string hash);
    string log = "Replaced transaction";
	function test(string txhash) public returns (string) {
	    emit replace(log,txhash);
	    return txhash;
	}
}
