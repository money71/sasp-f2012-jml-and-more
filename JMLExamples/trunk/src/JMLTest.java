public class JMLTest {

    private final int MAX_BALANCE = 100;
    
    /*@ invariant balance < MAX_BALANCE;
      @*/
    private int balance = 1;
    
    /*@ public normal_behavior
      @ requires a > 0;
      @*/
    public void add(int a) {
        this.balance += a;
    }
    
    public void printBalance() {
        System.out.println("Balance: " + this.balance);
    }
    
    public static void main(String[] arg) {
    
        JMLTest t = new JMLTest();
        
        if (arg.length == 1)
            t.add(new Integer(arg[0]));
    
        t.printBalance();
        
        System.out.println("Done");
    
    }

}
