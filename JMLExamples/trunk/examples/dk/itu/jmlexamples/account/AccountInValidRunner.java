package dk.itu.jmlexamples.account;

public class AccountInValidRunner {

	
	public static void main(String[] args) {
	    Account acc = new Account(100);
	    acc.withdraw(200); // withdraw more than at the account.
	    System.out.println("Balance after withdrawal: " + acc.balance());
	}	
	
}
