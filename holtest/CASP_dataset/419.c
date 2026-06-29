struct account {
  int lower_limit;
  int balance;
  int upper_limit;
};

/*@
predicate valid_account{L}(struct account* account) =
\valid(account) &&
account->lower_limit <= account->balance <= account->upper_limit;
*/

/*@
requires valid_account(account) && 
0<= amount <= account->upper_limit - account -> balance;
assigns account->balance;
ensures valid_account(account) 
&& account->balance == \at(account->balance,Pre) + amount;
*/
void deposit(struct account* account, int amount) {
  account->balance += amount;
}

/*@
requires valid_account(account) && 
0<= amount <= account -> balance -account->lower_limit;
assigns account->balance;
ensures valid_account(account)
&& account->balance == \at(account->balance,Pre) - amount;
*/
void withdraw(struct account* account, int amount) {
  account->balance -= amount;
}

/*@ requires valid_account(account);
  assigns \nothing;
  ensures \result == account -> balance;
*/
int get_balance(struct account* account) { return account ->balance; }

/*@ requires \valid(account) && lower_limit <= 0 <= upper_limit;
  assigns account->balance, account->lower_limit, account->upper_limit;
  ensures valid_account(account) 
  && account->balance == 0 && account->lower_limit == lower_limit 
  && account->upper_limit == upper_limit;
*/
void init_account(struct account* account, int lower_limit, int upper_limit) {
  account->lower_limit = lower_limit;
  account -> upper_limit = upper_limit;
  account->balance = 0;
}

int main () {
  struct account _Account;
  struct account* myAccount = &_Account;
  init_account(myAccount,-100,200);
  deposit(myAccount,10);
  withdraw(myAccount,20);
  int current_balance = get_balance(myAccount);
  //@ assert current_balance == -10;
  return 0;
}
