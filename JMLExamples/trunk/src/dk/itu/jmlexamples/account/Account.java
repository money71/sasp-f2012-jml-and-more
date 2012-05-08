package dk.itu.jmlexamples.account;

/*
 * Based upon the jml4 example
 * should check|compile but not rac (JML 2) since the withdraw method is not correctly implemented
 * JML 2 (command line) / JML 2 Eclipse plugin raises: 
 *  Exception in thread "main" org.jmlspecs.jmlrac.runtime.JMLInternalPreconditionError: by method Account.withdraw
 *	at dk.itu.jmlexamples.account.Account.main(Account.java:1488)
 *
 * JML 4 provides more useful feedback on the command line - http://pastebin.com/BNU4uZWB 
 * (todo: change into wiki links - when documented there - and by the way whats atually the correct 
 * implementation of withdraw() - tried naively http://pastebin.com/hzS9EEs3)  
 * 
 * similar should check|(compile)|rac but not 'run' (OpenJML) - todo: verify that
 */
public class Account {
  private /*@ spec_public @*/ int bal;
  //@ public invariant bal >= 0;

  /*@ requires amt >= 0;
    @ assignable bal;
    @ ensures bal == amt; @*/
  public Account(int amt) {
    bal = amt;
  }
 
  /*@ assignable bal;
    @ ensures bal == acc.bal; @*/
  public Account(Account acc) {
    bal = acc.balance();
  }

  /*@ requires amt > 0 && amt <= acc.balance();
    @ assignable bal, acc.bal;
    @ ensures bal == \old(bal) + amt
    @   && acc.bal == \old(acc.bal - amt); @*/
  public void transfer(int amt, Account acc) {
    acc.withdraw(amt);
    deposit(amt);
  }

  /*@ requires amt > 0 && amt <= bal;
    @ assignable bal;
    @ ensures bal == \old(bal) - amt; @*/
  public void withdraw(int amt) {
    bal -= amt;
  }

  /*@ requires amt > 0;
    @ assignable bal;
    @ ensures bal == \old(bal) + amt; @*/
  public void deposit(int amt) {
    bal += amt;
  }

  //@ ensures \result == bal;
  public /*@ pure @*/ int balance() {
    return bal;
  }
    
	public static void main(String[] args) {
	    Account acc = new Account(100);
	    acc.withdraw(200);
	    System.out.println("Balance after withdrawal: " + acc.balance());
	}
}
