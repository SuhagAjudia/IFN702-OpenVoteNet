pragma solidity ^0.4.24;
library ECCMath {
    function invmod(uint a, uint p) internal pure returns (uint) {
        if (a == 0 || a == p || p == 0)
            revert();
        if (a > p)
            a = a % p;
        int t1;
        int t2 = 1;
        uint r1 = p;
        uint r2 = a;
        uint q;
        while (r2 != 0) {
            q = r1 / r2;
            (t1, t2, r1, r2) = (t2, t1 - int(q) * t2, r2, r1 - q * r2);
        }
        if (t1 < 0)
            return (p - uint(-t1));
        return uint(t1);
    }


    function expmod(uint b, uint e, uint m) internal pure returns (uint r) {
        if (b == 0)
            return 0;
        if (e == 0)
            return 1;
        if (m == 0)
            revert();
        r = 1;
        uint bit = 2 ** 255;
        bit = bit;
        do{
            assembly {
            r := mulmod(mulmod(r, r, m), exp(b, iszero(iszero(and(e, bit)))), m)
            r := mulmod(mulmod(r, r, m), exp(b, iszero(iszero(and(e, div(bit, 2))))), m)
            r := mulmod(mulmod(r, r, m), exp(b, iszero(iszero(and(e, div(bit, 4))))), m)
            r := mulmod(mulmod(r, r, m), exp(b, iszero(iszero(and(e, div(bit, 8))))), m)
            bit := div(bit, 16)
            }
        }while(bit==0);
    }


    function toZ1(uint[3] memory P, uint zInv, uint z2Inv, uint prime) internal pure {
        P[0] = mulmod(P[0], z2Inv, prime);
        P[1] = mulmod(P[1], mulmod(zInv, z2Inv, prime), prime);
        P[2] = 1;
    }

    function toZ1(uint[3] memory PJ, uint prime) internal pure {
        uint zInv = invmod(PJ[2], prime);
        uint zInv2 = mulmod(zInv, zInv, prime);
        PJ[0] = mulmod(PJ[0], zInv2, prime);
        PJ[1] = mulmod(PJ[1], mulmod(zInv, zInv2, prime), prime);
        PJ[2] = 1;
    }

}

library Secp256k1 {

    uint constant pp = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F;
    uint constant Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798;
    uint constant Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8;
    uint constant nn = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141;
    uint constant lowSmax = 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0;
    function onCurve(uint[2] memory P) internal pure returns (bool) {
        uint p = pp;
        if (0 == P[0] || P[0] == p || 0 == P[1] || P[1] == p)
            return false;
        uint LHS = mulmod(P[1], P[1], p);
        uint RHS = addmod(mulmod(mulmod(P[0], P[0], p), P[0], p), 7, p);
        return LHS == RHS;
    }

    function isPubKey(uint[2] memory P) internal pure returns (bool isPK) {
        isPK = onCurve(P);
    }
    function isPubKey(uint[3] memory P) internal pure returns (bool isPK) {
        uint[2] memory a_P;
        a_P[0] = P[0];
        a_P[1] = P[1];
        isPK = onCurve(a_P);
    }

    function validateSignature(bytes32 message, uint[2] memory rs, uint[2] memory Q) internal pure returns (bool) {
        uint n = nn;
        uint p = pp;
        if(rs[0] == 0 || rs[0] >= n || rs[1] == 0 || rs[1] > lowSmax)
            return false;
        if (!isPubKey(Q))
            return false;

        uint sInv = ECCMath.invmod(rs[1], n);
        uint[3] memory u1G = _mul(mulmod(uint(message), sInv, n), [Gx, Gy]);
        uint[3] memory u2Q = _mul(mulmod(rs[0], sInv, n), Q);
        uint[3] memory P = _add(u1G, u2Q);

        if (P[2] == 0)
            return false;

        uint Px = ECCMath.invmod(P[2], p); // need Px/Pz^2
        Px = mulmod(P[0], mulmod(Px, Px, p), p);
        return Px % n == rs[0];
    }

    function compress(uint[2] memory P) internal pure returns (uint8 yBit, uint x) {
        x = P[0];
        yBit = P[1] & 1 == 1 ? 1 : 0;
    }

    function decompress(uint8 yBit, uint x) internal pure returns (uint[2] memory P) {
        uint p = pp;
        uint y2 = addmod(mulmod(x, mulmod(x, x, p), p), 7, p);
        uint y_ = ECCMath.expmod(y2, (p + 1) / 4, p);
        uint cmp = yBit ^ y_ & 1;
        P[0] = x;
        P[1] = (cmp == 0) ? y_ : p - y_;
    }

    function _add(uint[3] memory P, uint[3] memory Q) internal pure returns (uint[3] memory R) {
        if(P[2] == 0)
            return Q;
        if(Q[2] == 0)
            return P;
        uint p = pp;
        uint[4] memory zs; // Pz^2, Pz^3, Qz^2, Qz^3
        zs[0] = mulmod(P[2], P[2], p);
        zs[1] = mulmod(P[2], zs[0], p);
        zs[2] = mulmod(Q[2], Q[2], p);
        zs[3] = mulmod(Q[2], zs[2], p);
        uint[4] memory us = [
            mulmod(P[0], zs[2], p),
            mulmod(P[1], zs[3], p),
            mulmod(Q[0], zs[0], p),
            mulmod(Q[1], zs[1], p)
        ]; // Pu, Ps, Qu, Qs
        if (us[0] == us[2]) {
            if (us[1] != us[3])
                return R;
            else {
                return _double(P);
            }
        }
        uint h = addmod(us[2], p - us[0], p);
        uint r = addmod(us[3], p - us[1], p);
        uint h2 = mulmod(h, h, p);
        uint h3 = mulmod(h2, h, p);
        uint Rx = addmod(mulmod(r, r, p), p - h3, p);
        Rx = addmod(Rx, p - mulmod(2, mulmod(us[0], h2, p), p), p);
        R[0] = Rx;
        R[1] = mulmod(r, addmod(mulmod(us[0], h2, p), p - Rx, p), p);
        R[1] = addmod(R[1], p - mulmod(us[1], h3, p), p);
        R[2] = mulmod(h, mulmod(P[2], Q[2], p), p);
    }

    function _addMixed(uint[3] memory P, uint[2] memory Q) internal pure returns (uint[3] memory R) {
        if(P[2] == 0)
            return [Q[0], Q[1], 1];
        if(Q[1] == 0)
            return P;
        uint p = pp;
        uint[2] memory zs; // Pz^2, Pz^3, Qz^2, Qz^3
        zs[0] = mulmod(P[2], P[2], p);
        zs[1] = mulmod(P[2], zs[0], p);
        uint[4] memory us = [
            P[0],
            P[1],
            mulmod(Q[0], zs[0], p),
            mulmod(Q[1], zs[1], p)
        ]; // Pu, Ps, Qu, Qs
        if (us[0] == us[2]) {
            if (us[1] != us[3]) {
                P[0] = 0;
                P[1] = 0;
                P[2] = 0;
                return R;
            }
            else {
                _double(P);
                return _double(P);
            }
        }
        uint h = addmod(us[2], p - us[0], p);
        uint r = addmod(us[3], p - us[1], p);
        uint h2 = mulmod(h, h, p);
        uint h3 = mulmod(h2, h, p);
        uint Rx = addmod(mulmod(r, r, p), p - h3, p);
        Rx = addmod(Rx, p - mulmod(2, mulmod(us[0], h2, p), p), p);
        R[0] = Rx;
        R[1] = mulmod(r, addmod(mulmod(us[0], h2, p), p - Rx, p), p);
        R[1] = addmod(R[1], p - mulmod(us[1], h3, p), p);
        R[2] = mulmod(h, P[2], p);
    }

    function _addMixedM(uint[3] memory P, uint[2] memory Q) internal pure {
        if(P[1] == 0) {
            P[0] = Q[0];
            P[1] = Q[1];
            P[2] = 1;
            return;
        }
        if(Q[1] == 0)
            return;
        uint p = pp;
        uint[2] memory zs; // Pz^2, Pz^3, Qz^2, Qz^3
        zs[0] = mulmod(P[2], P[2], p);
        zs[1] = mulmod(P[2], zs[0], p);
        uint[4] memory us = [
            P[0],
            P[1],
            mulmod(Q[0], zs[0], p),
            mulmod(Q[1], zs[1], p)
        ]; // Pu, Ps, Qu, Qs
        if (us[0] == us[2]) {
            if (us[1] != us[3]) {
                P[0] = 0;
                P[1] = 0;
                P[2] = 0;
                return;
            }
            else {
                _doubleM(P);
                return;
            }
        }
        uint h = addmod(us[2], p - us[0], p);
        uint r = addmod(us[3], p - us[1], p);
        uint h2 = mulmod(h, h, p);
        uint h3 = mulmod(h2, h, p);
        uint Rx = addmod(mulmod(r, r, p), p - h3, p);
        Rx = addmod(Rx, p - mulmod(2, mulmod(us[0], h2, p), p), p);
        P[0] = Rx;
        P[1] = mulmod(r, addmod(mulmod(us[0], h2, p), p - Rx, p), p);
        P[1] = addmod(P[1], p - mulmod(us[1], h3, p), p);
        P[2] = mulmod(h, P[2], p);
    }

    function _double(uint[3] memory P) internal pure returns (uint[3] memory Q) {
        uint p = pp;
        if (P[2] == 0)
            return Q;
        uint Px = P[0];
        uint Py = P[1];
        uint Py2 = mulmod(Py, Py, p);
        uint s = mulmod(4, mulmod(Px, Py2, p), p);
        uint m = mulmod(3, mulmod(Px, Px, p), p);
        uint Qx = addmod(mulmod(m, m, p), p - addmod(s, s, p), p);
        Q[0] = Qx;
        Q[1] = addmod(mulmod(m, addmod(s, p - Qx, p), p), p - mulmod(8, mulmod(Py2, Py2, p), p), p);
        Q[2] = mulmod(2, mulmod(Py, P[2], p), p);
    }

    function _doubleM(uint[3] memory P) internal pure {
        uint p = pp;
        if (P[2] == 0)
            return;
        uint Px = P[0];
        uint Py = P[1];
        uint Py2 = mulmod(Py, Py, p);
        uint s = mulmod(4, mulmod(Px, Py2, p), p);
        uint m = mulmod(3, mulmod(Px, Px, p), p);
        uint PxTemp = addmod(mulmod(m, m, p), p - addmod(s, s, p), p);
        P[0] = PxTemp;
        P[1] = addmod(mulmod(m, addmod(s, p - PxTemp, p), p), p - mulmod(8, mulmod(Py2, Py2, p), p), p);
        P[2] = mulmod(2, mulmod(Py, P[2], p), p);
    }

    function _mul(uint d, uint[2] memory P) internal pure returns (uint[3] memory Q) {
        uint p = pp;
        if (d == 0) // TODO
            return Q;
        uint dwPtr; // points to array of NAF coefficients.
        uint i;

        // wNAF
        assembly
        {
                let dm := 0
                dwPtr := mload(0x40)
                mstore(0x40, add(dwPtr, 512)) // Should lower this.
            //loop:
              //  jumpi(loop_end, iszero(d))
                //jumpi(even, iszero(and(d, 1)))
                dm := mod(d, 32)
                mstore8(add(dwPtr, i), dm) // Don"t store as signed - convert when reading.
                d := add(sub(d, dm), mul(gt(dm, 16), 32))
            //even:
                d := div(d, 2)
                i := add(i, 1)
               // jump(loop)
            //loop_end:
        }
        
        dwPtr = dwPtr;

        // Pre calculation
        uint[3][8] memory PREC; // P, 3P, 5P, 7P, 9P, 11P, 13P, 15P
        PREC[0] = [P[0], P[1], 1];
        uint256[3] memory X =  _double(PREC[0]);
        PREC[1] = _addMixed(X, P);
        PREC[2] = _add(X, PREC[1]);
        PREC[3] = _add(X, PREC[2]);
        PREC[4] = _add(X, PREC[3]);
        PREC[5] = _add(X, PREC[4]);
        PREC[6] = _add(X, PREC[5]);
        PREC[7] = _add(X, PREC[6]);

        uint[16] memory INV;
        INV[0] = PREC[1][2];                            // a1
        INV[1] = mulmod(PREC[2][2], INV[0], p);         // a2
        INV[2] = mulmod(PREC[3][2], INV[1], p);         // a3
        INV[3] = mulmod(PREC[4][2], INV[2], p);         // a4
        INV[4] = mulmod(PREC[5][2], INV[3], p);         // a5
        INV[5] = mulmod(PREC[6][2], INV[4], p);         // a6
        INV[6] = mulmod(PREC[7][2], INV[5], p);         // a7

        INV[7] = ECCMath.invmod(INV[6], p);             // a7inv
        INV[8] = INV[7];                                // aNinv (a7inv)

        INV[15] = mulmod(INV[5], INV[8], p);            // z7inv
        for(uint k = 6; k >= 2; k--) {                  // z6inv to z2inv
            INV[8] = mulmod(PREC[k + 1][2], INV[8], p);
            INV[8 + k] = mulmod(INV[k - 2], INV[8], p);
        }
        INV[9] = mulmod(PREC[2][2], INV[8], p);         // z1Inv
        for(k = 0; k < 7; k++) {
            ECCMath.toZ1(PREC[k + 1], INV[k + 9], mulmod(INV[k + 9], INV[k + 9], p), p);
        }

        // Mult loop
        while(i > 0) {
            uint dj;
            uint pIdx;
            i--;
            assembly {
                dj := byte(0, mload(add(dwPtr, i)))
            }
            _doubleM(Q);
            if (dj > 16) {
                pIdx = (31 - dj) / 2; // These are the "negative ones", so invert y.
                _addMixedM(Q, [PREC[pIdx][0], p - PREC[pIdx][1]]);
            }
            else if (dj > 0) {
                pIdx = (dj - 1) / 2;
                _addMixedM(Q, [PREC[pIdx][0], PREC[pIdx][1]]);
            }
        }
    }

}


contract owned {
    address public owner;

    constructor() public {
        owner = msg.sender;
    }

    modifier onlyOwner {
        if(owner != msg.sender) revert();
        _;
    }

    function transferOwnership(address newOwner) public onlyOwner() {
        owner = newOwner;
    }
}

contract AnonymousVoting is owned {

  uint constant pp = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F;
  uint constant Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798;
  uint constant Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8;
  uint constant nn = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141;
  uint[2] G;
  address[] public addresses;
  mapping (address => uint) public addressid; 
  mapping (uint => Voter) public voters;
  mapping (address => bool) public eligible; 
  mapping (address => bool) public registered; 
  mapping (address => bool) public votecast; 
  mapping (address => bool) public commitment; 
  mapping (address => uint) public refunds; 

  struct Voter {
      address addr;
      uint[2] registeredkey;
      uint[2] reconstructedkey;
      bytes32 commitment;
      uint[2] vote;
  }


  function getVoter() public view returns (uint[2] memory _registeredkey, uint[2] memory _reconstructedkey, bytes32 _commitment){
      uint index = addressid[msg.sender];
      _registeredkey = voters[index].registeredkey;
      _reconstructedkey = voters[index].reconstructedkey;
      _commitment = voters[index].commitment;
  }

  uint public finishSignupPhase; 
  uint public endSignupPhase;
  uint public endCommitmentPhase;
  uint public endVotingPhase; 
  uint public endRefundPhase; 

  uint public totalregistered;
  uint public totaleligible;
  uint public totalcommitted;
  uint public totalvoted;
  uint public totalrefunded;
  uint public totaltorefund;

  string public question;
  uint[2] public finaltally;
  bool public commitmentphase;
  uint public depositrequired;
  uint public gap; 
  address public charity;
  uint public lostdeposit; 
  enum State { SETUP, SIGNUP, COMMITMENT, VOTE, FINISHED }
  State public state;

  modifier inState(State s) {
    if(state != s) {
        revert();
    }
    _;
  }

  constructor(uint _gap, address _charity) public {
    G[0] = Gx;
    G[1] = Gy;
    state = State.SETUP;
    question = "No question set";
    gap = _gap; 
    charity = _charity;
  }


  function setEligible(address[] memory addr) public onlyOwner {


    if(totaleligible > 50) {
      revert();
    }


    for(uint i=0; i<addr.length; i++) {

      if(!eligible[addr[i]]) {
        eligible[addr[i]] = true;
        addresses.push(addr[i]);
        totaleligible += 1;
      }
    }
  }

  function beginSignUp(string memory _question, bool enableCommitmentPhase, uint _finishSignupPhase, uint _endSignupPhase, uint _endCommitmentPhase, uint _endVotingPhase, uint _endRefundPhase, uint _depositrequired) inState(State.SETUP) public onlyOwner payable returns (bool){
    if(_finishSignupPhase > 0 + gap && addresses.length >= 3 && _depositrequired >= 0) {

        if(_endSignupPhase-gap < _finishSignupPhase) {
          return false;
        }

        if(enableCommitmentPhase) {
          if(_endCommitmentPhase-gap < _endSignupPhase) {
            return false;
          }
          if(_endVotingPhase-gap < _endCommitmentPhase) {
            return false;
          }

        } else {
          if(_endVotingPhase-gap < _endSignupPhase) {
            return false;
          }
        }
        if(_endRefundPhase-gap < _endVotingPhase) {
          return false;
        }
      if(msg.value  != _depositrequired) {
        return false;
      }
      refunds[msg.sender] = msg.value;

      state = State.SIGNUP;
      finishSignupPhase = _finishSignupPhase;
      endSignupPhase = _endSignupPhase;
      endCommitmentPhase = _endCommitmentPhase;
      endVotingPhase = _endVotingPhase;
      endRefundPhase = _endRefundPhase;
      question = _question;
      commitmentphase = enableCommitmentPhase;
      depositrequired = _depositrequired; 
      return true;
    }

    return false;
  }

  function deadlinePassed() public returns (bool){

      uint refund = 0;
      if(state == State.SIGNUP && block.timestamp > endSignupPhase) {

         state = State.FINISHED;
         totaltorefund = totalregistered;
         if(addresses.length >= 3) {
           refund = refunds[owner];
           refunds[owner] = 0;
           lostdeposit = lostdeposit + refund;

         }
         return true;
      }
      if(state == State.COMMITMENT && block.timestamp > endCommitmentPhase) {

         for(uint i=0; i<totalregistered; i++) {
            if(!commitment[voters[i].addr]) {
               refund = refunds[voters[i].addr];
               refunds[voters[i].addr] = 0;
               lostdeposit = lostdeposit + refund;
            } else {
              totaltorefund = totaltorefund + 1;
            }
         }

         state = State.FINISHED;
         return true;
      }
      if(state == State.VOTE && block.timestamp > endVotingPhase) {
         for(i=0; i<totalregistered; i++) {
            if(!votecast[voters[i].addr]) {
              refund = refunds[voters[i].addr];
              refunds[voters[i].addr] = 0;
              lostdeposit = lostdeposit + refund;
            } else {
              if(refunds[voters[i].addr] > 0) {
                totaltorefund = totaltorefund + 1;
              }
            }
         }

         state = State.FINISHED;
         return true;
      }
      if(state == State.FINISHED && msg.sender == owner && refunds[owner] == 0 && (block.timestamp > endRefundPhase || totaltorefund == totalrefunded)) {
         for(i=0; i<totalregistered; i++) {
           refund = refunds[voters[i].addr];
           refunds[voters[i].addr] = 0;
           lostdeposit = lostdeposit + refund;
         }

         uint[2] memory empty;

         for(i=0; i<addresses.length; i++) {
            address addr = addresses[i];
            eligible[addr] = false; 
            registered[addr] = false; 
            voters[i] = Voter({addr: (address(0)), registeredkey: empty, reconstructedkey: empty, vote: empty, commitment: 0});
            addressid[addr] = 0; 
            votecast[addr] = false; 
            commitment[addr] = false;
         }

       
         finishSignupPhase = 0;
         endSignupPhase = 0;
         endCommitmentPhase = 0;
         endVotingPhase = 0;
         endRefundPhase = 0;

         delete addresses;

         totalregistered = 0;
         totaleligible = 0;
         totalcommitted = 0;
         totalvoted = 0;

 
         question = "No question set";
         finaltally[0] = 0;
         finaltally[1] = 0;
         commitmentphase = false;
         depositrequired = 0;
         totalrefunded = 0;
         totaltorefund = 0;

         state = State.SETUP;
         return true;
      }
      return false;
  }
  function register(uint[2] memory xG, uint[3] memory vG, uint r) inState(State.SIGNUP) public payable returns (bool) {
     if(block.timestamp > finishSignupPhase) {
       revert(); 
     }
     if(msg.value != depositrequired) {
      return false;
    }
  if(eligible[msg.sender]) {
        if(verifyZKP(xG,r,vG) && !registered[msg.sender]) {
            refunds[msg.sender] = msg.value;
            uint[2] memory empty;
            addressid[msg.sender] = totalregistered;
            voters[totalregistered] = Voter({addr: msg.sender, registeredkey: xG, reconstructedkey: empty, vote: empty, commitment: 0});
            registered[msg.sender] = true;
            totalregistered += 1;

            return true;
        }
    }

    return false;
  }

  function finishRegistrationPhase() inState(State.SIGNUP) public onlyOwner returns(bool) {
      if(totalregistered < 3) {
        return false;
      }
      if(block.timestamp < finishSignupPhase) {
        return false;
      }
      if(block.timestamp > endSignupPhase) {
        return false;
      }

      uint[2] memory temp;
      uint[3] memory yG;
      uint[3] memory beforei;
      uint[3] memory afteri;

      afteri[0] = voters[1].registeredkey[0];
      afteri[1] = voters[1].registeredkey[1];
      afteri[2] = 1;

      for(uint i=2; i<totalregistered; i++) {
         Secp256k1._addMixedM(afteri, voters[i].registeredkey);
      }

      ECCMath.toZ1(afteri,pp);
      voters[0].reconstructedkey[0] = afteri[0];
      voters[0].reconstructedkey[1] = pp - afteri[1];

     for(i=1; i<totalregistered; i++) {

       if(i==1) {
         beforei[0] = voters[0].registeredkey[0];
         beforei[1] = voters[0].registeredkey[1];
         beforei[2] = 1;
       } else {
         Secp256k1._addMixedM(beforei, voters[i-1].registeredkey);
       }


       if(i==(totalregistered-1)) {
         ECCMath.toZ1(beforei,pp);
         voters[i].reconstructedkey[0] = beforei[0];
         voters[i].reconstructedkey[1] = beforei[1];

       } else {

          temp[0] = voters[i].registeredkey[0];
          temp[1] = pp - voters[i].registeredkey[1];

          Secp256k1._addMixedM(afteri,temp);
          ECCMath.toZ1(afteri,pp);

          temp[0] = afteri[0];
          temp[1] = pp - afteri[1];

          yG = Secp256k1._addMixed(beforei, temp);

          ECCMath.toZ1(yG,pp);

          voters[i].reconstructedkey[0] = yG[0];
          voters[i].reconstructedkey[1] = yG[1];
       }
     }

      if(commitmentphase) {
        state = State.COMMITMENT;
      } else {
        state = State.VOTE;
      }
  }
  function submitCommitment(bytes32 h) public inState(State.COMMITMENT) {

     if(block.timestamp > endCommitmentPhase) {
       return;
     }

    if(!commitment[msg.sender]) {
        commitment[msg.sender] = true;
        uint index = addressid[msg.sender];
        voters[index].commitment = h;
        totalcommitted = totalcommitted + 1;

        if(totalcommitted == totalregistered) {
          state = State.VOTE;
        }
    }
  }
  function submitVote(uint[4] memory params, uint[2] memory y, uint[2] memory a1, uint[2] memory b1, uint[2] memory a2, uint[2] memory b2) public inState(State.VOTE) returns (bool) {
     if(block.timestamp > endVotingPhase) {
       return false;
     }

     uint c = addressid[msg.sender];
     if(registered[msg.sender] && !votecast[msg.sender]) {
       if(commitmentphase) {

         bytes32 h = keccak256(abi.encodePacked(msg.sender, params, voters[c].registeredkey, voters[c].reconstructedkey, y, a1, b1, a2, b2));


         if(voters[c].commitment != h) {
           return false;
         }
       }

       if(verify1outof2ZKP(params, y, a1, b1, a2, b2)) {
         voters[c].vote[0] = y[0];
         voters[c].vote[1] = y[1];

         votecast[msg.sender] = true;

         totalvoted += 1;

         uint refund = refunds[msg.sender];
         refunds[msg.sender] = 0;

         if (!msg.sender.send(refund)) {
            refunds[msg.sender] = refund;
         }

         return true;
       }
     }

     return false;
  }


  function computeTally() inState(State.VOTE) public onlyOwner {

     uint[3] memory temp;
     uint[2] memory vote;
     uint refund;


     for(uint i=0; i<totalregistered; i++) {


         if(!votecast[voters[i].addr]) {
            revert();
         }

         vote = voters[i].vote;

         if(i==0) {
           temp[0] = vote[0];
           temp[1] = vote[1];
           temp[2] = 1;
         } else {
             Secp256k1._addMixedM(temp, vote);
         }
     }


     state = State.FINISHED;


     for(i = 0; i<totalregistered; i++) {


       if(refunds[voters[i].addr] > 0) {
         totaltorefund = totaltorefund + 1;
       }
     }


     if(temp[0] == 0) {
       finaltally[0] = 0;
       finaltally[1] = totalregistered;

y
       refund = refunds[msg.sender];
       refunds[msg.sender] = 0;

       if (!msg.sender.send(refund)) {
          refunds[msg.sender] = refund;
       }
       return;
     } else {


       ECCMath.toZ1(temp,pp);
       uint[3] memory tempG;
       tempG[0] = G[0];
       tempG[1] = G[1];
       tempG[2] = 1;

       for(i=1; i<=totalregistered; i++) {

         if(temp[0] == tempG[0]) {
             finaltally[0] = i;
             finaltally[1] = totalregistered;


             refund = refunds[msg.sender];
             refunds[msg.sender] = 0;

             if (!msg.sender.send(refund)) {
                refunds[msg.sender] = refund;
             }
             return;
         }

         Secp256k1._addMixedM(tempG, G);
           ECCMath.toZ1(tempG,pp);
         }


         finaltally[0] = 0;
         finaltally[1] = 0;

         refund = refunds[msg.sender];
         refunds[msg.sender] = 0;

         if (!msg.sender.send(refund)) {
            refunds[msg.sender] = refund;
         }
         return;
      }
  }

  function withdrawRefund() public inState(State.FINISHED){

    uint refund = refunds[msg.sender];
    refunds[msg.sender] = 0;

    if (!msg.sender.send(refund)) {
       refunds[msg.sender] = refund;
    } else {

      if(msg.sender != owner) {
         totalrefunded = totalrefunded + 1;
      }
    }
  }


  function sendToCharity() public {

    uint profit = lostdeposit;
    lostdeposit = 0;

    if(!charity.send(profit)) {

      lostdeposit = profit;
    }
  }

  function verifyZKP(uint[2] memory xG, uint r, uint[3] memory vG) public returns (bool){
        G[0] = Gx;
      G[1] = Gy;

      if(!Secp256k1.isPubKey(xG) || !Secp256k1.isPubKey(vG)) {
        return false;
      }

      bytes32 b_c = keccak256(abi.encodePacked(msg.sender, Gx, Gy, xG, vG));
      uint c = uint(b_c);

  
      uint[3] memory rG = Secp256k1._mul(r, G);
      uint[3] memory xcG = Secp256k1._mul(c, xG);


      uint[3] memory rGxcG = Secp256k1._add(rG,xcG);

       ECCMath.toZ1(rGxcG, pp);

      if(rGxcG[0] == vG[0] && rGxcG[1] == vG[1]) {
         return true;
      } else {
         return false;
      }
  }

  function verify1outof2ZKP(uint[4] memory params, uint[2] memory y, uint[2] memory a1, uint[2] memory b1, uint[2] memory a2, uint[2] memory b2) public view returns (bool) {
      uint[2] memory var1;
      uint[3] memory var2;
      uint[3] memory var3;

      uint i = addressid[msg.sender];

.
      uint[2] memory yG = voters[i].reconstructedkey;
      uint[2] memory xG = voters[i].registeredkey;

      if(!Secp256k1.isPubKey(xG) || !Secp256k1.isPubKey(yG) || !Secp256k1.isPubKey(y) || !Secp256k1.isPubKey(a1) ||
         !Secp256k1.isPubKey(b1) || !Secp256k1.isPubKey(a2) || !Secp256k1.isPubKey(b2)) {
         return false;
      }

      if(uint(keccak256(abi.encodePacked(msg.sender, xG, y, a1, b1, a2, b2))) != addmod(params[0],params[1],nn)) {
        return false;
      }

      var2 = Secp256k1._mul(params[2], G);
      var3 = Secp256k1._add(var2, Secp256k1._mul(params[0], xG));
      ECCMath.toZ1(var3, pp);

      if(a1[0] != var3[0] || a1[1] != var3[1]) {
        return false;
      }

      var2 = Secp256k1._mul(params[2],yG);
      var3 = Secp256k1._add(var2, Secp256k1._mul(params[0], y));
      ECCMath.toZ1(var3, pp);

      if(b1[0] != var3[0] || b1[1] != var3[1]) {
        return false;
      }

      var2 = Secp256k1._mul(params[3],G);
      var3 = Secp256k1._add(var2, Secp256k1._mul(params[1], xG));
      ECCMath.toZ1(var3, pp);

      if(a2[0] != var3[0] || a2[1] != var3[1]) {
        return false;
      }

      var1[0] = G[0];
      var1[1] = pp - G[1];

      var3[0] = y[0];
      var3[1] = y[1];
      var3[2] = 1;

      var2 = Secp256k1._addMixed(var3,var1);

      ECCMath.toZ1(var2, pp);
      var1[0] = var2[0];
      var1[1] = var2[1];

      var2 = Secp256k1._mul(params[1],var1);

      var3 = Secp256k1._add(Secp256k1._mul(params[3],yG),var2);
      ECCMath.toZ1(var3, pp);

      if(b2[0] != var3[0] || b2[1] != var3[1]) {
        return false;
      }

      return true;
    }
}
