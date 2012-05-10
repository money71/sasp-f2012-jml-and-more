/**
 * 
 * Based upon a simple account example - though adjusted the specs
 * (TODO: add ref. and evt. refactor to AccountSimple etc.)
 * 
 */
public class JMLTest {

    private final /*@ spec_public @*/ int MAX_BALANCE = 100;
    
    /*@ invariant balance < MAX_BALANCE;
      @*/
    private /*@ spec_public @*/ int balance = 1;
    
    /*@ public normal_behavior
      @ requires a > 0;
      @ assignable balance;
      @ ensures balance == \old(balance) + a;
      @*/
    public void add(int a) {
        this.balance += a;
    }
    
    public void printBalance() {
        System.out.println("Balance: " + this.balance);
    }
    
    public static void main(String[] arg) {
    
        JMLTest t = new JMLTest();
// disabled because of #5 - http://code.google.com/p/sasp-f2012-jml-and-more/issues/detail?id=5         
//        if (arg.length == 1)
//            t.add(new Integer(arg[0]));

        t.add(101);
        
        t.printBalance();
        
        System.out.println("Done");
    
    }

}
