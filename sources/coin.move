module 0x42::basic_coin {
    use std::signer;
    /// Error codes
    const ENOT_MODULE_OWNER: u64 = 0;
    const EINSUFFICIENT_BALANCE: u64 = 1;
    const EALREADY_HAS_BALANCE: u64 = 2;
    const EBALANCE_NOT_EXIST: u64 = 3;
    const EEQUAL_ADDR: u64 = 4;
    /// Constants
    const MIN_BALANCE: u64 = 100;

    // 1. Each Balance should have at least MIN_BALANCE.
    struct Balance has key {
        value: u64
    }
    spec Balance {
        invariant value >= MIN_BALANCE;
    }

    // 2. Balance should persist on chain. In other words, it should not be removed from the global state.
    spec module {
        invariant update forall addr: address: old(exists<Balance>(addr))
            ==> exists<Balance>(addr);
    }

    public fun balance_of(owner: address): u64 acquires Balance {
        borrow_global<Balance>(owner).value
    }
    public fun publish_balance(account: &signer) {
        assert!(!exists<Balance>(signer::address_of(account)), EALREADY_HAS_BALANCE);
        move_to(account, Balance { value: MIN_BALANCE });
    }


    // Task 1: Design high-level requirement for the withdraw function.
    // Task 2: Enforce these requirements.
    fun withdraw(account: &signer, amount: u64): u64 acquires Balance {
        let addr = signer::address_of(account);
        let balance = balance_of(addr);
        assert!(balance >= amount + MIN_BALANCE, EINSUFFICIENT_BALANCE);
        let balance_ref = &mut borrow_global_mut<Balance>(addr).value;
        *balance_ref = balance - amount;
        amount
    }


























    // High-level requirements
    //    Pre-conditions:
    //        Balance under the account signer should exist.
    //        The balance should be enough to support the withdrawal
    //
    //     Post-coditions:
    //        The balance after the withdrawl should be appropriate.
    //        The returned value should equal the amount withdrawn.










    spec withdraw {
        let addr = signer::address_of(account);
        aborts_if !exists<Balance>(addr);
        aborts_if global<Balance>(addr).value < amount + MIN_BALANCE;
        ensures global<Balance>(addr).value <= old(global<Balance>(addr).value);
        ensures global<Balance>(addr).value == old(global<Balance>(addr).value) - amount;
        ensures result == amount;
    }
    fun deposit(addr: address, amount: u64) acquires Balance{
        let balance = balance_of(addr);
        let balance_ref = &mut borrow_global_mut<Balance>(addr).value;
        *balance_ref = balance + amount;
    }
    public fun transfer(from: &signer, to: address, amount: u64) acquires Balance {
        let from_addr = signer::address_of(from);
        assert!(from_addr != to, EEQUAL_ADDR);
        let check = withdraw(from, amount);
        deposit(to, check);
    }
    // spec deposit {
    //     let balance = global<Balance<CoinType>>(addr).coin.value;
    //     let check_value = check.value;
    //     aborts_if !exists<Balance<CoinType>>(addr);
    //     aborts_if balance + check_value > MAX_U64;
    //     let post balance_post = global<Balance<CoinType>>(addr).coin.value;
    //     ensures balance_post == balance + check_value;
    // }
    // spec transfer {
    //     let addr_from = signer::address_of(from);
    //     let balance_from = global<Balance<CoinType>>(addr_from).coin.value;
    //     let balance_to = global<Balance<CoinType>>(to).coin.value;
    //     let post balance_from_post = global<Balance<CoinType>>(addr_from).coin.value;
    //     let post balance_to_post = global<Balance<CoinType>>(to).coin.value;
    //     aborts_if !exists<Balance<CoinType>>(addr_from);
    //     aborts_if !exists<Balance<CoinType>>(to);
    //     aborts_if balance_from < amount;
    //     aborts_if balance_to + amount > MAX_U64;
    //     aborts_if addr_from == to;
    //     ensures balance_from_post == balance_from - amount;
    //     ensures balance_to_post == balance_to + amount;
    // }
    // spec withdraw {
    //     let balance = global<Balance<CoinType>>(addr).coin.value;
    //     aborts_if !exists<Balance<CoinType>>(addr);
    //     aborts_if balance < amount;
    //     let post balance_post = global<Balance<CoinType>>(addr).coin.value;
    //     ensures result == Coin<CoinType> { value: amount };
    //     ensures balance_post == balance - amount;
    // }
}