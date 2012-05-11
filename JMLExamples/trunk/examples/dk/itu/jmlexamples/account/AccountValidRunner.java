package dk.itu.jmlexamples.account;

public class AccountValidRunner {

	
	public static void main(String[] args) {
	    Account acc = new Account(200);
	    acc.withdraw(200);
	    System.out.println("Balance after withdrawal: " + acc.balance());
	}	
	
}
