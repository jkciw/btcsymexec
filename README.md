# Symbolic execution and analysis of bitcoin script 
A framework to represent bitcoin scripts symbolically, define constraints for the script and validate the script against those constraints. 

## Tools
- script parser - to parse the given script into blocks of code (vertices)
- edge constructor - to construct edges between vertices based on conditions
- control flow graph builder - to build control flow graph using the vertices and the edges
- symbolic executor - symbilically execute the blocks of opcodes and follow all possible execution paths
- constraint checker - define constraints and verify if the constraints are satisfied by any of the execution paths

## Example script used
A Licho Mecenas contract is used as an example. It is used to make recurring donations from patron to beneficiary with time-based controls

MECENAS CONTRACT PSEUDOCODE
### Key Components:
    - Patron (sender of funds)
    - Beneficiary (receiver of funds)
    - Payment amount
    - Time interval (using CheckSequenceVerify)

CONTRACT Mecenas 

    // Contract Parameters
    INPUT :
        PATRON_PUBKEYHASH
        BENEFICIARY_PUBKEYHASH
        DONATION_AMOUNT
        TIME_INTERVAL
    

    // Contract Logic
    FUNCTION Receive donations () 
        // Ensure that the UTXO used is older than a certain time period
        REQUIRE input_tx.age > TIME_INTREVAL

        //Ensure that the first output of the transaction goes to the beneficiary 
        REQUIRE output_tx[0].ScriptPubkey = Benificiary's ScriptPubkey
        
        // Calculate value remaining in the input
        CHANGE = input_tx.value - DONATION_AMOUNT - MINER FEES

        // Two spending paths depending on how much amount is left in the input after this spend
        IF CHANGE <= DONATION_AMOUNT + MINER FEES > THEN 
            // Send all the input's amount to the beneficiary 

            output_tx[0].value = input_tx.value - MINER FEES
        ELSE 
            // Send the donation amount to the beneificiary 
            output_tx[0].value = DONATION_AMOUNT
            
            // Send the change to a new address that recursively enforces the covenant
            output_tx[1].value = CHANGE
            output_tx[1].ScriptPubKey = input[0].ScriptPubkey
    
    FUNCTION Reclaim funds ()       
        REQUIRE Hash160(public_key) = Patron's Public Key hash
        REQUIRE CHECKSIG(s, public_key)

### Execution Flow: 
1. Contract starts with funds from patron
2. Every TIME_INTERVAL:
   - Beneficiary can claim PAYMENT_AMOUNT
   - Remaining funds stay in contract
3. Patron can reclaim remaining funds at any time

### OP_CODES
Transaction introspection opcodes from the elements project are used to construct the contract. 
Ref: https://github.com/ElementsProject/elements/blob/master/doc/tapscript_opcodes.md


